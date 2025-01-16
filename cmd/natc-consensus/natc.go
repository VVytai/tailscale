// Copyright (c) Tailscale Inc & AUTHORS
// SPDX-License-Identifier: BSD-3-Clause

// The natc command is a work-in-progress implementation of a NAT based
// connector for Tailscale. It is intended to be used to route traffic to a
// specific domain through a specific node.
package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"log"
	"net"
	"net/http"
	"net/netip"
	"os"
	"strings"
	"time"

	"github.com/gaissmai/bart"
	"github.com/inetaf/tcpproxy"
	"github.com/peterbourgon/ff/v3"
	"golang.org/x/net/dns/dnsmessage"
	"tailscale.com/client/tailscale"
	"tailscale.com/envknob"
	"tailscale.com/hostinfo"
	"tailscale.com/ipn"
	"tailscale.com/net/netutil"
	"tailscale.com/tailcfg"
	"tailscale.com/tsnet"
	"tailscale.com/tsweb"
)

func main() {
	hostinfo.SetApp("natc")
	if !envknob.UseWIPCode() {
		log.Fatal("cmd/natc-consensus is a work in progress and has not been security reviewed;\nits use requires TAILSCALE_USE_WIP_CODE=1 be set in the environment for now.")
	}

	// Parse flags
	fs := flag.NewFlagSet("natc", flag.ExitOnError)
	var (
		debugPort       = fs.Int("debug-port", 8893, "Listening port for debug/metrics endpoint")
		hostname        = fs.String("hostname", "", "Hostname to register the service under")
		siteID          = fs.Uint("site-id", 1, "an integer site ID to use for the ULA prefix which allows for multiple proxies to act in a HA configuration")
		v4PfxStr        = fs.String("v4-pfx", "100.64.1.0/24", "comma-separated list of IPv4 prefixes to advertise")
		verboseTSNet    = fs.Bool("verbose-tsnet", false, "enable verbose logging in tsnet")
		printULA        = fs.Bool("print-ula", false, "print the ULA prefix and exit")
		ignoreDstPfxStr = fs.String("ignore-destinations", "", "comma-separated list of prefixes to ignore")
		wgPort          = fs.Uint("wg-port", 0, "udp port for wireguard and peer to peer traffic")
		clusterTag      = fs.String("cluster-tag", "", "TODO")
	)
	ff.Parse(fs, os.Args[1:], ff.WithEnvVarPrefix("TS_NATC"))

	if *printULA {
		fmt.Println(ula(uint16(*siteID)))
		return
	}

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	if *siteID == 0 {
		log.Fatalf("site-id must be set")
	} else if *siteID > 0xffff {
		log.Fatalf("site-id must be in the range [0, 65535]")
	}

	var ignoreDstTable *bart.Table[bool]
	for _, s := range strings.Split(*ignoreDstPfxStr, ",") {
		s := strings.TrimSpace(s)
		if s == "" {
			continue
		}
		if ignoreDstTable == nil {
			ignoreDstTable = &bart.Table[bool]{}
		}
		pfx, err := netip.ParsePrefix(s)
		if err != nil {
			log.Fatalf("unable to parse prefix: %v", err)
		}
		if pfx.Masked() != pfx {
			log.Fatalf("prefix %v is not normalized (bits are set outside the mask)", pfx)
		}
		ignoreDstTable.Insert(pfx, true)
	}
	var v4Prefixes []netip.Prefix
	for _, s := range strings.Split(*v4PfxStr, ",") {
		p := netip.MustParsePrefix(strings.TrimSpace(s))
		if p.Masked() != p {
			log.Fatalf("v4 prefix %v is not a masked prefix", p)
		}
		v4Prefixes = append(v4Prefixes, p)
	}
	if len(v4Prefixes) == 0 {
		log.Fatalf("no v4 prefixes specified")
	}
	dnsAddr := v4Prefixes[0].Addr()
	ts := &tsnet.Server{
		Hostname: *hostname,
	}
	ts.ControlURL = "http://host.docker.internal:31544" // TODO
	if *wgPort != 0 {
		if *wgPort >= 1<<16 {
			log.Fatalf("wg-port must be in the range [0, 65535]")
		}
		ts.Port = uint16(*wgPort)
	}
	defer ts.Close()

	if *verboseTSNet {
		ts.Logf = log.Printf
	}

	// Start special-purpose listeners: dns, http promotion, debug server
	if *debugPort != 0 {
		mux := http.NewServeMux()
		tsweb.Debugger(mux)
		dln, err := ts.Listen("tcp", fmt.Sprintf(":%d", *debugPort))
		if err != nil {
			log.Fatalf("failed listening on debug port: %v", err)
		}
		defer dln.Close()
		go func() {
			log.Fatalf("debug serve: %v", http.Serve(dln, mux))
		}()
	}
	lc, err := ts.LocalClient()
	if err != nil {
		log.Fatalf("LocalClient() failed: %v", err)
	}
	if _, err := ts.Up(ctx); err != nil {
		log.Fatalf("ts.Up: %v", err)
	}

	ipp := ipPool{
		v4Ranges: v4Prefixes,
		dnsAddr:  dnsAddr,
	}

	err = ipp.StartConsensus(ctx, ts, *clusterTag)
	if err != nil {
		log.Fatalf("StartConsensus: %v", err)
	}
	defer ipp.consensus.Stop(ctx)

	c := &connector{
		ts:         ts,
		lc:         lc,
		dnsAddr:    dnsAddr,
		v4Ranges:   v4Prefixes,
		v6ULA:      ula(uint16(*siteID)),
		ignoreDsts: ignoreDstTable,
		ipAddrs:    &ipp,
	}
	c.run(ctx)
}

type connector struct {
	// ts is the tsnet.Server used to host the connector.
	ts *tsnet.Server
	// lc is the LocalClient used to interact with the tsnet.Server hosting this
	// connector.
	lc *tailscale.LocalClient

	// dnsAddr is the IPv4 address to listen on for DNS requests. It is used to
	// prevent the app connector from assigning it to a domain.
	dnsAddr netip.Addr

	// v4Ranges is the list of IPv4 ranges to advertise and assign addresses from.
	// These are masked prefixes.
	v4Ranges []netip.Prefix
	// v6ULA is the ULA prefix used by the app connector to assign IPv6 addresses.
	v6ULA netip.Prefix

	ipAddrs *ipPool

	// ignoreDsts is initialized at start up with the contents of --ignore-destinations (if none it is nil)
	// It is never mutated, only used for lookups.
	// Users who want to natc a DNS wildcard but not every address record in that domain can supply the
	// exceptions in --ignore-destinations. When we receive a dns request we will look up the fqdn
	// and if any of the ip addresses in response to the lookup match any 'ignore destinations' prefix we will
	// return a dns response that contains the ip addresses we discovered with the lookup (ie not the
	// natc behavior, which would return a dummy ip address pointing at natc).
	ignoreDsts *bart.Table[bool]
}

// v6ULA is the ULA prefix used by the app connector to assign IPv6 addresses.
// The 8th and 9th bytes are used to encode the site ID which allows for
// multiple proxies to act in a HA configuration.
// mnemonic: a99c = appc
var v6ULA = netip.MustParsePrefix("fd7a:115c:a1e0:a99c::/64")

func ula(siteID uint16) netip.Prefix {
	as16 := v6ULA.Addr().As16()
	as16[8] = byte(siteID >> 8)
	as16[9] = byte(siteID)
	return netip.PrefixFrom(netip.AddrFrom16(as16), 64+16)
}

// run runs the connector.
//
// The passed in context is only used for the initial setup. The connector runs
// forever.
func (c *connector) run(ctx context.Context) {
	if _, err := c.lc.EditPrefs(ctx, &ipn.MaskedPrefs{
		AdvertiseRoutesSet: true,
		Prefs: ipn.Prefs{
			AdvertiseRoutes: append(c.v4Ranges, c.v6ULA),
		},
	}); err != nil {
		log.Fatalf("failed to advertise routes: %v", err)
	}
	c.ts.RegisterFallbackTCPHandler(c.handleTCPFlow)
	c.serveDNS()
}

func (c *connector) serveDNS() {
	pc, err := c.ts.ListenPacket("udp", net.JoinHostPort(c.dnsAddr.String(), "53"))
	if err != nil {
		log.Fatalf("failed listening on port 53: %v", err)
	}
	defer pc.Close()
	log.Printf("Listening for DNS on %s", pc.LocalAddr().String())
	for {
		buf := make([]byte, 1500)
		n, addr, err := pc.ReadFrom(buf)
		if err != nil {
			if errors.Is(err, net.ErrClosed) {
				return
			}
			log.Printf("serveDNS.ReadFrom failed: %v", err)
			continue
		}
		go c.handleDNS(pc, buf[:n], addr.(*net.UDPAddr))
	}
}

func lookupDestinationIP(domain string) ([]netip.Addr, error) {
	netIPs, err := net.LookupIP(domain)
	if err != nil {
		var dnsError *net.DNSError
		if errors.As(err, &dnsError) && dnsError.IsNotFound {
			return nil, nil
		} else {
			return nil, err
		}
	}
	var addrs []netip.Addr
	for _, ip := range netIPs {
		a, ok := netip.AddrFromSlice(ip)
		if ok {
			addrs = append(addrs, a)
		}
	}
	return addrs, nil
}

// handleDNS handles a DNS request to the app connector.
// It generates a response based on the request and the node that sent it.
//
// Each node is assigned a unique pair of IP addresses for each domain it
// queries. This assignment is done lazily and is not persisted across restarts.
// A per-peer assignment allows the connector to reuse a limited number of IP
// addresses across multiple nodes and domains. It also allows for clear
// failover behavior when an app connector is restarted.
//
// This assignment later allows the connector to determine where to forward
// traffic based on the destination IP address.
func (c *connector) handleDNS(pc net.PacketConn, buf []byte, remoteAddr *net.UDPAddr) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	who, err := c.lc.WhoIs(ctx, remoteAddr.String())
	if err != nil {
		log.Printf("HandleDNS: WhoIs failed: %v\n", err)
		return
	}

	var msg dnsmessage.Message
	err = msg.Unpack(buf)
	if err != nil {
		log.Printf("HandleDNS: dnsmessage unpack failed: %v\n ", err)
		return
	}

	// If there are destination ips that we don't want to route, we
	// have to do a dns lookup here to find the destination ip.
	if c.ignoreDsts != nil {
		if len(msg.Questions) > 0 {
			q := msg.Questions[0]
			switch q.Type {
			case dnsmessage.TypeAAAA, dnsmessage.TypeA:
				dstAddrs, err := lookupDestinationIP(q.Name.String())
				if err != nil {
					log.Printf("HandleDNS: lookup destination failed: %v\n ", err)
					return
				}
				if c.ignoreDestination(dstAddrs) {
					bs, err := dnsResponse(&msg, dstAddrs)
					// TODO (fran): treat as SERVFAIL
					if err != nil {
						log.Printf("HandleDNS: generate ignore response failed: %v\n", err)
						return
					}
					_, err = pc.WriteTo(bs, remoteAddr)
					if err != nil {
						log.Printf("HandleDNS: write failed: %v\n", err)
					}
					return
				}
			}
		}
	}
	// None of the destination IP addresses match an ignore destination prefix, do
	// the natc thing.

	resp, err := c.generateDNSResponse(&msg, who.Node.ID)
	// TODO (fran): treat as SERVFAIL
	if err != nil {
		log.Printf("HandleDNS: connector handling failed: %v\n", err)
		return
	}
	// TODO (fran): treat as NXDOMAIN
	if len(resp) == 0 {
		return
	}
	// This connector handled the DNS request
	_, err = pc.WriteTo(resp, remoteAddr)
	if err != nil {
		log.Printf("HandleDNS: write failed: %v\n", err)
	}
}

// tsMBox is the mailbox used in SOA records.
// The convention is to replace the @ symbol with a dot.
// So in this case, the mailbox is support.tailscale.com. with the trailing dot
// to indicate that it is a fully qualified domain name.
var tsMBox = dnsmessage.MustNewName("support.tailscale.com.")

// generateDNSResponse generates a DNS response for the given request. The from
// argument is the NodeID of the node that sent the request.
func (c *connector) generateDNSResponse(req *dnsmessage.Message, from tailcfg.NodeID) ([]byte, error) {
	var addrs []netip.Addr
	if len(req.Questions) > 0 {
		switch req.Questions[0].Type {
		case dnsmessage.TypeAAAA, dnsmessage.TypeA:
			v4, err := c.ipAddrs.IpForDomain(from, req.Questions[0].Name.String())
			if err != nil {
				return nil, err
			}
			addrs = []netip.Addr{v4, c.v6ForV4(v4)}
		}
	}
	return dnsResponse(req, addrs)
}

// dnsResponse makes a DNS response for the natc. If the dnsmessage is requesting TypeAAAA
// or TypeA the provided addrs of the requested type will be used.
func dnsResponse(req *dnsmessage.Message, addrs []netip.Addr) ([]byte, error) {
	b := dnsmessage.NewBuilder(nil,
		dnsmessage.Header{
			ID:            req.Header.ID,
			Response:      true,
			Authoritative: true,
		})
	b.EnableCompression()

	if len(req.Questions) == 0 {
		return b.Finish()
	}
	q := req.Questions[0]
	if err := b.StartQuestions(); err != nil {
		return nil, err
	}
	if err := b.Question(q); err != nil {
		return nil, err
	}
	if err := b.StartAnswers(); err != nil {
		return nil, err
	}
	switch q.Type {
	case dnsmessage.TypeAAAA, dnsmessage.TypeA:
		want6 := q.Type == dnsmessage.TypeAAAA
		for _, ip := range addrs {
			if want6 != ip.Is6() {
				continue
			}
			if want6 {
				if err := b.AAAAResource(
					dnsmessage.ResourceHeader{Name: q.Name, Class: q.Class, TTL: 5},
					dnsmessage.AAAAResource{AAAA: ip.As16()},
				); err != nil {
					return nil, err
				}
			} else {
				if err := b.AResource(
					dnsmessage.ResourceHeader{Name: q.Name, Class: q.Class, TTL: 5},
					dnsmessage.AResource{A: ip.As4()},
				); err != nil {
					return nil, err
				}
			}
		}
	case dnsmessage.TypeSOA:
		if err := b.SOAResource(
			dnsmessage.ResourceHeader{Name: q.Name, Class: q.Class, TTL: 120},
			dnsmessage.SOAResource{NS: q.Name, MBox: tsMBox, Serial: 2023030600,
				Refresh: 120, Retry: 120, Expire: 120, MinTTL: 60},
		); err != nil {
			return nil, err
		}
	case dnsmessage.TypeNS:
		if err := b.NSResource(
			dnsmessage.ResourceHeader{Name: q.Name, Class: q.Class, TTL: 120},
			dnsmessage.NSResource{NS: tsMBox},
		); err != nil {
			return nil, err
		}
	}
	return b.Finish()
}

// handleTCPFlow handles a TCP flow from the given source to the given
// destination. It uses the source address to determine the node that sent the
// request and the destination address to determine the domain that the request
// is for based on the IP address assigned to the destination in the DNS
// response.
func (c *connector) handleTCPFlow(src, dst netip.AddrPort) (handler func(net.Conn), intercept bool) {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	who, err := c.lc.WhoIs(ctx, src.Addr().String())
	cancel()
	if err != nil {
		log.Printf("HandleTCPFlow: WhoIs failed: %v\n", err)
		return nil, false
	}

	from := who.Node.ID
	dstAddr := dst.Addr()
	if dstAddr.Is6() {
		dstAddr = v4ForV6(dstAddr)
	}
	domain := c.ipAddrs.DomainForIP(from, dstAddr, time.Now())
	if domain == "" {
		log.Print("handleTCPFlow: found no domain")
		return nil, false
	}
	return func(conn net.Conn) {
		proxyTCPConn(conn, domain)
	}, true
}

// ignoreDestination reports whether any of the provided dstAddrs match the prefixes configured
// in --ignore-destinations
func (c *connector) ignoreDestination(dstAddrs []netip.Addr) bool {
	for _, a := range dstAddrs {
		if _, ok := c.ignoreDsts.Lookup(a); ok {
			return true
		}
	}
	return false
}

func proxyTCPConn(c net.Conn, dest string) {
	if c.RemoteAddr() == nil {
		log.Printf("proxyTCPConn: nil RemoteAddr")
		c.Close()
		return
	}
	addrPortStr := c.LocalAddr().String()
	_, port, err := net.SplitHostPort(addrPortStr)
	if err != nil {
		log.Printf("tcpRoundRobinHandler.Handle: bogus addrPort %q", addrPortStr)
		c.Close()
		return
	}

	p := &tcpproxy.Proxy{
		ListenFunc: func(net, laddr string) (net.Listener, error) {
			return netutil.NewOneConnListener(c, nil), nil
		},
	}
	p.AddRoute(addrPortStr, &tcpproxy.DialProxy{
		Addr: fmt.Sprintf("%s:%s", dest, port),
	})
	p.Start()
}

func (c *connector) v6ForV4(v4 netip.Addr) netip.Addr {
	as16 := c.v6ULA.Addr().As16()
	as4 := v4.As4()
	copy(as16[12:], as4[:])
	v6 := netip.AddrFrom16(as16)
	return v6
}

func v4ForV6(v6 netip.Addr) netip.Addr {
	as16 := v6.As16()
	var as4 [4]byte
	copy(as4[:], as16[12:])
	v4 := netip.AddrFrom4(as4)
	return v4
}
