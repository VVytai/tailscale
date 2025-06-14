// Copyright (c) Tailscale Inc & AUTHORS
// SPDX-License-Identifier: BSD-3-Clause

package udprelay

import (
	"bytes"
	"net"
	"net/netip"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	"github.com/google/go-cmp/cmp/cmpopts"
	"go4.org/mem"
	"tailscale.com/disco"
	"tailscale.com/net/packet"
	"tailscale.com/types/key"
)

type testClient struct {
	vni    uint32
	local  key.DiscoPrivate
	server key.DiscoPublic
	uc     *net.UDPConn
}

func newTestClient(t *testing.T, vni uint32, serverEndpoint netip.AddrPort, local key.DiscoPrivate, server key.DiscoPublic) *testClient {
	rAddr := &net.UDPAddr{IP: serverEndpoint.Addr().AsSlice(), Port: int(serverEndpoint.Port())}
	uc, err := net.DialUDP("udp4", nil, rAddr)
	if err != nil {
		t.Fatal(err)
	}
	return &testClient{
		vni:    vni,
		local:  local,
		server: server,
		uc:     uc,
	}
}

func (c *testClient) write(t *testing.T, b []byte) {
	_, err := c.uc.Write(b)
	if err != nil {
		t.Fatal(err)
	}
}

func (c *testClient) read(t *testing.T) []byte {
	c.uc.SetReadDeadline(time.Now().Add(time.Second))
	b := make([]byte, 1<<16-1)
	n, err := c.uc.Read(b)
	if err != nil {
		t.Fatal(err)
	}
	return b[:n]
}

func (c *testClient) writeDataPkt(t *testing.T, b []byte) {
	pkt := make([]byte, packet.GeneveFixedHeaderLength, packet.GeneveFixedHeaderLength+len(b))
	gh := packet.GeneveHeader{Control: false, VNI: c.vni, Protocol: packet.GeneveProtocolWireGuard}
	err := gh.Encode(pkt)
	if err != nil {
		t.Fatal(err)
	}
	pkt = append(pkt, b...)
	c.write(t, pkt)
}

func (c *testClient) readDataPkt(t *testing.T) []byte {
	b := c.read(t)
	gh := packet.GeneveHeader{}
	err := gh.Decode(b)
	if err != nil {
		t.Fatal(err)
	}
	if gh.Protocol != packet.GeneveProtocolWireGuard {
		t.Fatal("unexpected geneve protocol")
	}
	if gh.Control {
		t.Fatal("unexpected control")
	}
	if gh.VNI != c.vni {
		t.Fatal("unexpected vni")
	}
	return b[packet.GeneveFixedHeaderLength:]
}

func (c *testClient) writeControlDiscoMsg(t *testing.T, msg disco.Message) {
	pkt := make([]byte, packet.GeneveFixedHeaderLength, 512)
	gh := packet.GeneveHeader{Control: true, VNI: c.vni, Protocol: packet.GeneveProtocolDisco}
	err := gh.Encode(pkt)
	if err != nil {
		t.Fatal(err)
	}
	pkt = append(pkt, disco.Magic...)
	pkt = c.local.Public().AppendTo(pkt)
	box := c.local.Shared(c.server).Seal(msg.AppendMarshal(nil))
	pkt = append(pkt, box...)
	c.write(t, pkt)
}

func (c *testClient) readControlDiscoMsg(t *testing.T) disco.Message {
	b := c.read(t)
	gh := packet.GeneveHeader{}
	err := gh.Decode(b)
	if err != nil {
		t.Fatal(err)
	}
	if gh.Protocol != packet.GeneveProtocolDisco {
		t.Fatal("unexpected geneve protocol")
	}
	if !gh.Control {
		t.Fatal("unexpected non-control")
	}
	if gh.VNI != c.vni {
		t.Fatal("unexpected vni")
	}
	b = b[packet.GeneveFixedHeaderLength:]
	headerLen := len(disco.Magic) + key.DiscoPublicRawLen
	if len(b) < headerLen {
		t.Fatal("disco message too short")
	}
	sender := key.DiscoPublicFromRaw32(mem.B(b[len(disco.Magic):headerLen]))
	if sender.Compare(c.server) != 0 {
		t.Fatal("unknown disco public key")
	}
	payload, ok := c.local.Shared(c.server).Open(b[headerLen:])
	if !ok {
		t.Fatal("failed to open sealed disco msg")
	}
	msg, err := disco.Parse(payload)
	if err != nil {
		t.Fatal("failed to parse disco payload")
	}
	return msg
}

func (c *testClient) handshake(t *testing.T) {
	c.writeControlDiscoMsg(t, &disco.BindUDPRelayEndpoint{})
	msg := c.readControlDiscoMsg(t)
	challenge, ok := msg.(*disco.BindUDPRelayEndpointChallenge)
	if !ok {
		t.Fatal("unexepcted disco message type")
	}
	c.writeControlDiscoMsg(t, &disco.BindUDPRelayEndpointAnswer{Answer: challenge.Challenge})
}

func (c *testClient) close() {
	c.uc.Close()
}

func TestServer(t *testing.T) {
	discoA := key.NewDisco()
	discoB := key.NewDisco()

	ipv4LoopbackAddr := netip.MustParseAddr("127.0.0.1")

	server, _, err := NewServer(t.Logf, 0, []netip.Addr{ipv4LoopbackAddr})
	if err != nil {
		t.Fatal(err)
	}
	defer server.Close()

	endpoint, err := server.AllocateEndpoint(discoA.Public(), discoB.Public())
	if err != nil {
		t.Fatal(err)
	}
	dupEndpoint, err := server.AllocateEndpoint(discoA.Public(), discoB.Public())
	if err != nil {
		t.Fatal(err)
	}

	// We expect the same endpoint details pre-handshake.
	if diff := cmp.Diff(dupEndpoint, endpoint, cmpopts.EquateComparable(netip.AddrPort{}, key.DiscoPublic{})); diff != "" {
		t.Fatalf("wrong dupEndpoint (-got +want)\n%s", diff)
	}

	if len(endpoint.AddrPorts) != 1 {
		t.Fatalf("unexpected endpoint.AddrPorts: %v", endpoint.AddrPorts)
	}
	tcA := newTestClient(t, endpoint.VNI, endpoint.AddrPorts[0], discoA, endpoint.ServerDisco)
	defer tcA.close()
	tcB := newTestClient(t, endpoint.VNI, endpoint.AddrPorts[0], discoB, endpoint.ServerDisco)
	defer tcB.close()

	tcA.handshake(t)
	tcB.handshake(t)

	dupEndpoint, err = server.AllocateEndpoint(discoA.Public(), discoB.Public())
	if err != nil {
		t.Fatal(err)
	}
	// We expect the same endpoint details post-handshake.
	if diff := cmp.Diff(dupEndpoint, endpoint, cmpopts.EquateComparable(netip.AddrPort{}, key.DiscoPublic{})); diff != "" {
		t.Fatalf("wrong dupEndpoint (-got +want)\n%s", diff)
	}

	txToB := []byte{1, 2, 3}
	tcA.writeDataPkt(t, txToB)
	rxFromA := tcB.readDataPkt(t)
	if !bytes.Equal(txToB, rxFromA) {
		t.Fatal("unexpected msg A->B")
	}

	txToA := []byte{4, 5, 6}
	tcB.writeDataPkt(t, txToA)
	rxFromB := tcA.readDataPkt(t)
	if !bytes.Equal(txToA, rxFromB) {
		t.Fatal("unexpected msg B->A")
	}
}
