# Pinned Z3 API benchmark

This nested module compares GoSMT with Z3's official Go API at commit
`ddb49568d3520e99799e364fb22f35fc67d887b1`. It is isolated so Z3 and CGO are
not dependencies of the released GoSMT module.

On macOS, point the compiler at the verified Z3 4.16.0 release headers and a
directory containing only `libz3.a` (the release dylib has a non-relocatable
install name):

```sh
Z3_ROOT=/path/to/z3-4.16.0-arm64-osx-15.7.3
mkdir -p /tmp/gosmt-z3-static
ln -sf "$Z3_ROOT/bin/libz3.a" /tmp/gosmt-z3-static/libz3.a
CGO_CFLAGS="-I$Z3_ROOT/include" \
CGO_LDFLAGS="-L/tmp/gosmt-z3-static -lc++" \
go test -run '^$' -bench . -benchmem -count=5
```

The artifact SHA-256 must be
`41828fa07d5cb77bfaee326e8e6dac074f26329c09c633f9e66012bb917cf8ae`.

The conditional integer-EUF cold workload uses exact guarded equalities on the
Z3 side because the pinned official Go binding does not expose `Z3_mk_ite`.
GoSMT's compact `IfInt` path uses 13 allocations versus Z3's 34 and is more
than 160 times faster on the recorded Apple M5 Max runs.
