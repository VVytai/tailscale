// Copyright (c) Tailscale Inc & AUTHORS
// SPDX-License-Identifier: BSD-3-Clause

package flakytest

import (
	"os"
	"testing"
)

func TestIssueFormat(t *testing.T) {
	testCases := []struct {
		issue string
		want  bool
	}{
		{"https://github.com/tailscale/cOrp/issues/1234", true},
		{"https://github.com/otherproject/corp/issues/1234", false},
		{"https://github.com/tailscale/corp/issues/", false},
	}
	for _, testCase := range testCases {
		if issueRegexp.MatchString(testCase.issue) != testCase.want {
			ss := ""
			if !testCase.want {
				ss = " not"
			}
			t.Errorf("expected issueRegexp to%s match %q", ss, testCase.issue)
		}
	}
}

// TestFlakeRun is a test that fails when run in the testwrapper
// for the first time, but succeeds on the second run.
// It's used to test whether the testwrapper retries flaky tests.
func TestFlakeRun(t *testing.T) {
	Mark(t, "https://github.com/tailscale/tailscale/issues/0") // random issue
	e := os.Getenv(FlakeAttemptEnv)
	if e == "" {
		t.Skip("not running in testwrapper")
	}
	if e == "1" {
		t.Fatal("First run in testwrapper, failing so that test is retried. This is expected.")
	}
}

// TestFlakePanic is a test that panics when run in the testwrapper
// for the first time, but succeeds on the second run.
// It's used to test whether the testwrapper retries flaky tests.
func TestFlakeExit(t *testing.T) {
	Mark(t, "https://github.com/tailscale/tailscale/issues/0") // random issue
	e := os.Getenv(FlakeAttemptEnv)
	if e == "" {
		t.Skip("not running in testwrapper")
	}
	if e == "1" {
		t.Log("First run in testwrapper, failing so exiting so test is retried. This is expected.")
		os.Exit(0)
	}
}

// TestFlakePanic is a test that panics when run in the testwrapper
// for the first time, but succeeds on the second run.
// It's used to test whether the testwrapper retries flaky tests.
func TestFlakePanic(t *testing.T) {
	Mark(t, "https://github.com/tailscale/tailscale/issues/0") // random issue
	e := os.Getenv(FlakeAttemptEnv)
	if e == "" {
		t.Skip("not running in testwrapper")
	}
	if e == "1" {
		panic("First run in testwrapper, failing so that test is retried. This is expected.")
	}
}
