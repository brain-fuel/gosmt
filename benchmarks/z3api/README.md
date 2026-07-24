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

The unary and binary real-predicate workloads use 11 allocations versus Z3's
22 and 25 respectively. Both remain more than 170 times faster on the recorded
Apple M5 Max cold runs.

The ternary real-function bound-aggregation workload uses 16 allocations
versus Z3's 34 and runs about 54 times faster.

The exact ground Int/Real coercion construction workload uses 1 allocation
versus Z3's 4 and runs more than 2 times faster. The pinned official Go binding
does not expose Z3's three arithmetic-coercion constructors, so its side
constructs the unique normalized ground results for the same four operations.

The symbolic `to_real` equality workload uses three independent exact
coercions and validates satisfiability after normalization. It uses 8
allocations versus Z3's 21 and runs more than 225 times faster. The pinned Go
binding omits `Z3_mk_int2real`, so Z3 receives the same unique normalized
integer equalities.

The symbolic coercion round-trip contradiction workload covers both
`to_int(to_real(x)) = x` and `is_int(to_real(x))`. It uses 4 allocations
versus Z3's 12 and runs more than 430 times faster. Z3 receives the unique
normalized identity and integrality terms because its pinned Go binding omits
the coercion constructors.

The affine coercion contradiction workload covers a symbolic integer plus
`3/2`, exact integrality normalization, and context-indexed `AndPair`
short-circuiting. It uses 4 allocations versus Z3's 12 and runs more than 486
times faster.

The affine equality workload compares two differently offset coercions of the
same symbolic integer. It uses 5 allocations versus Z3's 12 and remains more
than 360 times faster at conservative endpoints.

The rational-scaled coercion workload proves
`to_int(3/2*to_real(x)) = 10` and `not is_int(3/2*to_real(x))` under `x = 7`.
Its compact scaled-dividend `div`/`mod` path uses 12 allocations versus Z3's
25 (52% fewer). Across five Apple M5 Max runs against the released std module,
it takes 6.34–6.65 µs versus 1.02–1.15 ms for Z3, more than 154 times faster
at conservative endpoints.

The affine rational-scaled workload adds an exact `1/4` offset before scaling
and checks the same floor/integrality pair. Its compact coefficient-plus-offset
dividend path uses 9 allocations versus Z3's 28 (67.9% fewer). Across five
Apple M5 Max runs against the released std module, it takes 6.45–6.52 µs
versus 1.009–1.108 ms for Z3, more than 154 times faster at conservative
endpoints.

The two-symbol rational-scaled workload uses `x+y+1/4`, checks both assigned
models, and proves the same floor/non-integrality pair. Its compact two-symbol
dividend path uses 18 allocations versus Z3's 38 (52.6% fewer). Across five
Apple M5 Max runs against the released std module, it takes 8.57–8.62 µs
versus 0.963–1.104 ms for Z3, more than 111 times faster at conservative
endpoints.

The ground floating-point workload constructs binary32 positive and negative
zero, infinity, and NaN; checks zero/infinity/NaN predicates; and validates
both signed-zero and NaN `fp.eq` semantics through each public API and solver.
Across five Apple M5 Max runs it uses 4 allocations versus Z3's 17 (76.5%
fewer) and takes 4.077–4.124 µs versus 0.922–1.048 ms, more than 223 times
faster at conservative endpoints.

The symbolic floating-point workload constructs a context- and format-indexed
binary32 constant, solves `fp.isNaN`, extracts its exact IEEE model bits, and
validates the model classification. The solver-neutral std relation retains
the classification without generic bit-blast allocation and synthesizes a
canonical compact model. Across five Apple M5 Max runs it uses 5 allocations
versus Z3's 10 (exactly 50% fewer) and takes 3.890–4.030 µs versus
1.309–1.453 ms, more than 324 times faster at conservative endpoints.

The unconstrained floating-point equality workload constructs two binary32
symbols, solves IEEE `fp.eq`, and validates both synthesized model values.
Across five Apple M5 Max runs it uses 5 allocations versus Z3's 14 (64.3%
fewer) and takes 4.298–4.407 µs versus 1.373–1.493 ms, more than 311 times
faster at conservative endpoints.

The repeated-operand floating-point division workload solves `x/x = 1` and
validates the synthesized binary32 source. Across five Apple M5 Max runs it
uses 5 allocations versus Z3's 13 (61.5% fewer) and takes 4.470–4.974 µs
versus 34.088–45.590 ms, more than 6,850 times faster at conservative
endpoints.

The repeated-operand floating-point multiplication workload solves `x*x = 1`
and validates the synthesized binary32 source. Across five Apple M5 Max runs
it uses 5 allocations versus Z3's 13 (61.5% fewer) and takes 4.359–5.184 µs
versus 86.660–87.532 ms, more than 16,700 times faster at conservative
endpoints.

The repeated-operand fused-multiply-add workload aliases its multiplicands,
solves the exact result `1.5`, and validates both synthesized binary32
symbols. Across five Apple M5 Max runs it uses 5 allocations versus Z3's 17
(70.6% fewer) and takes 4.764–5.672 µs versus 13.982–14.297 ms, more than
2,465 times faster at conservative endpoints.

The all-aliased fused-multiply-add workload solves `fma(x,x,x) = 0.75` and
validates the synthesized binary32 source. Across five Apple M5 Max runs it
uses 5 allocations versus Z3's 13 (61.5% fewer) and takes 4.962–4.994 µs
versus 58.056–72.045 ms, more than 11,626 times faster at conservative
endpoints.

The shared floating-point equality-graph workload combines a positive
equivalence, a cross-class disequality, and a NaN-backed self-disequality,
then validates all synthesized models. Across five Apple M5 Max runs it uses
10 allocations versus Z3's 24 (58.3% fewer) and takes 9.834–10.083 µs versus
1.344–1.443 ms, more than 133 times faster at conservative endpoints.
