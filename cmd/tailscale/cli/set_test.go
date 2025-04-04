// Copyright (c) Tailscale Inc & AUTHORS
// SPDX-License-Identifier: BSD-3-Clause

package cli

import (
	"flag"
	"net/netip"
	"reflect"
	"testing"

	"tailscale.com/ipn"
	"tailscale.com/net/tsaddr"
	"tailscale.com/types/ptr"
)

func TestCalcAdvertiseRoutesForSet(t *testing.T) {
	pfx := netip.MustParsePrefix
	tests := []struct {
		name      string
		setExit   *bool
		setRoutes *string
		was       []netip.Prefix
		want      []netip.Prefix
	}{
		{
			name: "empty",
		},
		{
			name:    "advertise-exit",
			setExit: ptr.To(true),
			want:    tsaddr.ExitRoutes(),
		},
		{
			name:    "advertise-exit/already-routes",
			was:     []netip.Prefix{pfx("34.0.0.0/16")},
			setExit: ptr.To(true),
			want:    []netip.Prefix{pfx("34.0.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
		},
		{
			name:    "advertise-exit/already-exit",
			was:     tsaddr.ExitRoutes(),
			setExit: ptr.To(true),
			want:    tsaddr.ExitRoutes(),
		},
		{
			name:    "stop-advertise-exit",
			was:     tsaddr.ExitRoutes(),
			setExit: ptr.To(false),
			want:    nil,
		},
		{
			name:    "stop-advertise-exit/with-routes",
			was:     []netip.Prefix{pfx("34.0.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
			setExit: ptr.To(false),
			want:    []netip.Prefix{pfx("34.0.0.0/16")},
		},
		{
			name:      "advertise-routes",
			setRoutes: ptr.To("10.0.0.0/24,192.168.0.0/16"),
			want:      []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16")},
		},
		{
			name:      "advertise-routes/already-exit",
			was:       tsaddr.ExitRoutes(),
			setRoutes: ptr.To("10.0.0.0/24,192.168.0.0/16"),
			want:      []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
		},
		{
			name:      "advertise-routes/already-diff-routes",
			was:       []netip.Prefix{pfx("34.0.0.0/16")},
			setRoutes: ptr.To("10.0.0.0/24,192.168.0.0/16"),
			want:      []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16")},
		},
		{
			name:      "stop-advertise-routes",
			was:       []netip.Prefix{pfx("34.0.0.0/16")},
			setRoutes: ptr.To(""),
			want:      nil,
		},
		{
			name:      "stop-advertise-routes/already-exit",
			was:       []netip.Prefix{pfx("34.0.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
			setRoutes: ptr.To(""),
			want:      tsaddr.ExitRoutes(),
		},
		{
			name:      "advertise-routes-and-exit",
			setExit:   ptr.To(true),
			setRoutes: ptr.To("10.0.0.0/24,192.168.0.0/16"),
			want:      []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
		},
		{
			name:      "advertise-routes-and-exit/already-exit",
			was:       tsaddr.ExitRoutes(),
			setExit:   ptr.To(true),
			setRoutes: ptr.To("10.0.0.0/24,192.168.0.0/16"),
			want:      []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
		},
		{
			name:      "advertise-routes-and-exit/already-routes",
			was:       []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16")},
			setExit:   ptr.To(true),
			setRoutes: ptr.To("10.0.0.0/24,192.168.0.0/16"),
			want:      []netip.Prefix{pfx("10.0.0.0/24"), pfx("192.168.0.0/16"), tsaddr.AllIPv4(), tsaddr.AllIPv6()},
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			curPrefs := &ipn.Prefs{
				AdvertiseRoutes: tc.was,
			}
			sa := setArgsT{}
			if tc.setExit != nil {
				sa.advertiseDefaultRoute = *tc.setExit
			}
			if tc.setRoutes != nil {
				sa.advertiseRoutes = []string{*tc.setRoutes}
			}
			got, err := calcAdvertiseRoutesForSet(tc.setExit != nil, tc.setRoutes != nil, curPrefs, sa)
			if err != nil {
				t.Fatal(err)
			}
			tsaddr.SortPrefixes(got)
			tsaddr.SortPrefixes(tc.want)
			if !reflect.DeepEqual(got, tc.want) {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}

// TestSetDefaultsMatchUpDefaults is meant to ensure that the default values
// for `tailscale set` and `tailscale up` are the same.
// Since `tailscale set` only sets preferences that are explicitly mentioned,
// the default values for its flags are only used for `--help` documentation.
func TestSetDefaultsMatchUpDefaults(t *testing.T) {
	upFlagSet.VisitAll(func(up *flag.Flag) {
		if preflessFlag(up.Name) {
			return
		}

		set := setFlagSet.Lookup(up.Name)
		if set == nil {
			return
		}

		if set.DefValue != up.DefValue {
			t.Errorf("--%s: set defaults to %q, but up defaults to %q", up.Name, set.DefValue, up.DefValue)
		}
	})
}

func TestStringListFlagParsing(t *testing.T) {
	tests := []struct {
		name     string
		args     []string
		want     []string
		flagName string
	}{
		{
			name:     "single tag",
			args:     []string{"--advertise-tags=tag:foo"},
			want:     []string{"tag:foo"},
			flagName: "advertise-tags",
		},
		{
			name:     "comma-separated tags",
			args:     []string{"--advertise-tags=tag:foo,tag:bar"},
			want:     []string{"tag:foo", "tag:bar"},
			flagName: "advertise-tags",
		},
		{
			name:     "multi advertise-tags flags",
			args:     []string{"--advertise-tags=tag:foo", "--advertise-tags=tag:bar"},
			want:     []string{"tag:foo", "tag:bar"},
			flagName: "advertise-tags",
		},
		{
			name:     "mixed comma and multi advertise-tags",
			args:     []string{"--advertise-tags=tag:foo,tag:bar", "--advertise-tags=tag:baz"},
			want:     []string{"tag:foo", "tag:bar", "tag:baz"},
			flagName: "advertise-tags",
		},
		{
			name:     "single advertise-routes parsing",
			args:     []string{"--advertise-routes=10.0.0.0/8,192.168.0.0/24,172.16.0.0/12"},
			want:     []string{"10.0.0.0/8", "192.168.0.0/24", "172.16.0.0/12"},
			flagName: "advertise-routes",
		},
		{
			name:     "multi advertise-routes parsing",
			args:     []string{"--advertise-routes=10.0.0.0/8", "--advertise-routes=192.168.0.0/24,172.16.0.0/12"},
			want:     []string{"10.0.0.0/8", "192.168.0.0/24", "172.16.0.0/12"},
			flagName: "advertise-routes",
		},
		{
			name:     "empty string input should be ignored",
			args:     []string{"--advertise-tags="},
			want:     nil,
			flagName: "advertise-tags",
		},
		{
			name:     "whitespace-only input should be ignored",
			args:     []string{"--advertise-tags=   "},
			want:     nil,
			flagName: "advertise-tags",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			var tags stringSliceMultiFlag
			fs := flag.NewFlagSet("test", flag.ContinueOnError)
			fs.Var(&tags, tt.flagName, "test flag")

			err := fs.Parse(tt.args)
			if err != nil {
				t.Fatalf("flag parsing failed: %v", err)
			}
			got := []string(tags)
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("parsed %q = %v, want %v", tt.args, got, tt.want)
			}
		})
	}
}
