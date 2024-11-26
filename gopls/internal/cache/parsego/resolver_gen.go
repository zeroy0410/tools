// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build ignore

package main

import (
	"bytes"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

func main() {
	output, err := exec.Command("go", "env", "GOROOT").Output()
	if err != nil {
		log.Fatalf("resolving GOROOT: %v", err)
	}
	goroot := strings.TrimSpace(string(output))
	data, err := os.ReadFile(filepath.Join(goroot, "src/go/parser/resolver.go"))
	if err != nil {
		log.Fatalf("reading resolver.go: %v", err)
	}
	data = bytes.Replace(data, []byte("\npackage parser"), []byte("\n// Code generated by resolver_gen.go. DO NOT EDIT.\n\npackage parsego"), 1)
	if err := os.WriteFile("resolver.go", data, 0666); err != nil {
		log.Fatalf("writing resolver.go: %v", err)
	}
}