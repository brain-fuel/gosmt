# Performance contract

The baseline oracle is Z3 4.16.0. Each benchmark records semantic work only
(construction separately from solving), warm and cold modes, satisfiable and
unsatisfiable instances, bytes/op, allocations/op, and result/model validation.

Release gate for every declared workload family:

- GoSMT throughput is at least 2× Z3's corresponding API/CLI workload.
- GoSMT allocations are at most 50% of the pinned Go-facing baseline.
- No timeout, `unknown`, invalid model, or omitted workload counts as a win.

After replacing exhaustive assignment enumeration with linear-size Tseitin CNF
and unit-propagating DPLL, an immutable warm check of the deliberately tiny
two-variable Boolean solve is approximately 1.45 ns/op with 0 B/op and 0
allocations/op on Apple M5 Max. After arena sizing, the corresponding cold
construct-and-solve path is approximately 316 ns/op, 1,272 B/op, and 5
allocations/op. Warm reuse is a
real API workload, but it cannot mask the still-red cold gate.

With adaptive scan/CDCL propagation, the current 70-variable cold Boolean
workload is approximately 10.14–10.37 us/op, 63,640 B/op, and 21 allocations/op. The
256-variable implication-chain workload is approximately 22.68–23.05 us/op, 156,289
B/op, and 16 allocations/op. The 256-variable QF_IDL chain is approximately
20.1 us/op, 43,728 B/op, and 32 allocations/op. These are explicit red scale baselines for clause
learning and denser watcher storage, not Z3-relative gate results.

The new core removes the old 62-variable ceiling and gives larger formulas an
actual search procedure. Watched literals, arena-backed clauses, incremental
reuse across assertion descendants, learning, and non-chronological
backtracking remain required before the Boolean family may pass its complete
performance gate.

QF_IDL now retains inline `int64` values and promotes only out-of-range values
to immutable arbitrary-precision integers. Migrating weights, distances, and
models initially moved the cold public workload to 15 allocations. Compact
inline difference constraints and graph storage reduced it to 8 allocations,
60% fewer than Z3's 20, while the slowest GoSMT endpoint remains over 1,000x
faster than Z3's fastest endpoint. Wide 101-bit bounds use the same exact path.

This measurement is not yet a Z3 comparison and therefore does not satisfy a
compatibility or performance gate.

## Official Go API comparison

`benchmarks/z3api` links both solvers into the same benchmark process using
Z3's official Go binding at the pinned commit. Current Apple M5 Max results:

| QF_BOOL workload | GoSMT | Z3 4.16.0 | Throughput gate | Allocation gate |
|---|---:|---:|---|---|
| QF_BOOL warm check | ~3.33 ns, 0 B, 0 allocs | ~40 us, 0 B, 0 allocs | green | green |
| QF_BOOL cold construct + check | ~467–475 ns, 1,584 B, 10 allocs | ~0.98–1.08 ms, 200 B, 13 allocs | green | red (target ≤6 allocs) |
| QF_IDL warm check | ~3.33 ns, 0 B, 0 allocs | ~147 us, 0 B, 0 allocs | green | green |
| QF_IDL cold construct + check | ~827 ns–1.02 us, 2,704 B, 8 allocs | ~1.07–1.23 ms, 320 B, 20 allocs | green | green (target ≤10 allocs) |
| QF_LIA exact single-equation model construction + evaluation | ~763–772 ns, 3,264 B, 6 allocs | ~1.30–1.40 ms, 224 B, 15 allocs | green | green (target ≤7 allocs) |
| QF_LIA general two-row model construction + two evaluations | ~5.68–5.74 us, 3,680 B, 13 allocs | ~1.45–1.53 ms, 424 B, 28 allocs | green | green (target ≤14 allocs) |
| Boolean QF_LIA disjunction+disequality model construction + evaluation | ~7.19–7.24 us, 3,552 B, 7 allocs | ~1.28–1.41 ms, 304 B, 20 allocs | green | green (target ≤10 allocs) |
| ground QF_UF cold construct + check | ~398–399 ns, 1,504 B, 14 allocs | ~0.86–1.01 ms, 304 B, 21 allocs | green | red (target ≤10 allocs) |
| binary ground QF_UF cold construct + check | ~667–789 ns, 2,008 B, 15 allocs | ~0.85–1.01 ms, 480 B, 30 allocs | green | green (target ≤15 allocs) |
| QF_BOOL 5-into-4 pigeonhole construct + check | ~11.13–11.22 us, 30,320 B, 27 allocs | ~1.12–1.21 ms, 6,536 B, 360 allocs | green | green (target ≤180 allocs) |
| QF_BOOL 7-into-6 pigeonhole construct + check | ~1.19–1.21 ms, 277,217 B, 44 allocs | ~2.89–2.91 ms, 24,728 B, 1,078 allocs | green | green (target ≤539 allocs) |
| QF_LRA cold construct + exact check | ~5.08–5.22 us, 3,200 B, 5 allocs | ~1.77–2.81 ms, 304 B, 19 allocs | green | green (target ≤9 allocs) |
| disjoint EUF+QF_LRA cold construct + check | ~2.17–2.41 us, 3,808 B, 13 allocs | ~1.04–1.19 ms, 416 B, 27 allocs | green | green (target ≤13 allocs) |
| shared Real→Real EUF+QF_LRA equality exchange | ~1.32–1.50 us, 3,144 B, 7 allocs | ~1.05–1.16 ms, 344 B, 23 allocs | green | green (target ≤11 allocs) |
| purified Real→Real applications inside linear arithmetic | ~10.84–11.09 us, 5,720 B, 9 allocs | ~0.88–1.07 ms, 344 B, 23 allocs | green | green (target ≤11 allocs) |
| purified binary Real×Real→Real applications | ~11.39–12.61 us, 6,104 B, 9 allocs | ~0.89–1.05 ms, 368 B, 23 allocs | green | green (target ≤11 allocs) |
| QF_BV 8-bit mask contradiction | ~509–579 ns, 1,064 B, 4 allocs | ~0.89–1.06 ms, 280 B, 18 allocs | green | green (target ≤9 allocs) |
| QF_BV 8-bit unsigned-order contradiction | ~483–583 ns, 1,064 B, 4 allocs | ~0.89–1.04 ms, 232 B, 15 allocs | green | green (target ≤7 allocs) |
| QF_BV 8-bit symbol-dependent multiplication | ~573–683 ns, 1,160 B, 4 allocs | ~0.89–1.05 ms, 280 B, 18 allocs | green | green (target ≤9 allocs) |
| QF_BV 8-bit symbol-dependent logical shift | ~588–675 ns, 1,160 B, 4 allocs | ~0.89–1.04 ms, 280 B, 18 allocs | green | green (target ≤9 allocs) |
| QF_BV 8-bit symbol-dependent unsigned division | ~569–630 ns, 1,160 B, 4 allocs | ~0.89–1.05 ms, 280 B, 18 allocs | green | green (target ≤9 allocs) |
| QF_BV symbol-dependent 8→4 extraction | ~563–635 ns, 1,224 B, 4 allocs | ~0.89–1.05 ms, 248 B, 16 allocs | green | green (target ≤8 allocs) |
| QF_BV 8-bit symbol-dependent rotate-left | ~561–640 ns, 1,224 B, 4 allocs | ~0.90–1.05 ms, 280 B, 18 allocs | green | green (target ≤9 allocs) |
| QF_BV 8-bit unsigned-add overflow | ~516–670 ns, 1,256 B, 4 allocs | ~0.90–1.05 ms, 248 B, 16 allocs | green | green (target ≤8 allocs) |
| ground QF_UFBV unary congruence contradiction | ~854 ns–1.09 us, 2,424 B, 8 allocs | ~0.94–1.13 ms, 336 B, 23 allocs | green | green (target ≤11 allocs) |
| QF_BV unsigned BV-to-Int contradiction | ~698–700 ns, 1,568 B, 6 allocs | ~0.89–1.03 ms, 200 B, 13 allocs | green | green (target ≤6 allocs) |
| ground QF_ALIA integer-array read-over-write | ~318–320 ns, 920 B, 5 allocs | ~0.79–1.00 ms, 200 B, 13 allocs | green | green (target ≤6 allocs) |
| ground QF_ALIA equal-array select congruence | ~531–537 ns, 936 B, 6 allocs | ~0.84–1.03 ms, 264 B, 17 allocs | green | green (target ≤8 allocs) |
| ground QF_ALIA symbolic-index store/read congruence | ~863–865 ns, 1,176 B, 9 allocs | ~0.90–1.05 ms, 328 B, 21 allocs | green | green (target ≤10 allocs) |
| ground QF_ALIA extensional model construction + evaluation | ~1.281–1.284 us, 3,096 B, 10 allocs | ~1.023–1.123 ms, 320 B, 21 allocs | green | green (target ≤10 allocs) |
| ground QF_ALIA shared-base store-chain extensionality | ~489–495 ns, 1,384 B, 7 allocs | ~1.012–1.151 ms, 264 B, 17 allocs | green | green (target ≤8 allocs) |
| ground QF_ALIA cross-base store equality + outside read | ~664–686 ns, 1,288 B, 8 allocs | ~1.012–1.147 ms, 328 B, 21 allocs | green | green (target ≤10 allocs) |
| ground QF_ALIA symbolic-to-constant equality + read | ~596–641 ns, 1,056 B, 6 allocs | ~0.830–1.031 ms, 248 B, 16 allocs | green | green (target ≤8 allocs) |
| mixed QF_AUFLIA IDL-to-array index equality exchange | ~830–834 ns, 2,328 B, 7 allocs | ~0.941–1.110 ms, 352 B, 22 allocs | green | green (target ≤11 allocs) |
| ground QF_AUFBV exact-index read-over-write | ~554–560 ns, 2,088 B, 4 allocs | ~1.06–1.15 ms, 248 B, 16 allocs | green | green (target ≤8 allocs) |
| ground QF_AUFBV symbolic-index equality exchange | ~865–868 ns, 2,296 B, 5 allocs | ~1.05–1.16 ms, 360 B, 23 allocs | green | green (target ≤11 allocs) |
| ground QF_AUFBV extensional model + two evaluations | ~1.31–1.32 us, 8,208 B, 8 allocs | ~1.12–1.18 ms, 272 B, 18 allocs | green | green (target ≤9 allocs) |
| ground QF_AUFBV two-store extensionality | ~769–770 ns, 2,088 B, 4 allocs | ~1.01–1.12 ms, 344 B, 22 allocs | green | green (target ≤11 allocs) |

The warm result is cached immutable-state checking in both APIs. The cold row
includes context, term, solver, assertion, solve, and result construction. No
throughput result is used to waive either independent cold allocation failure.

The QF_LRA result uses the same three-constraint satisfiable workload in both
official Go APIs. Exact hybrid rationals retain an inline normalized int64 path
with automatic arbitrary-precision promotion. Inline affine constraints and a
contiguous simplex tableau first reduced GoSMT from 45 to 9 allocations; fixed
small-tableau arenas with unbounded overflow then reduced it to 5 (89%) while
the pinned Z3 binding remained at 19. Across five equal-count comparative runs,
the slowest GoSMT endpoint was still more than 300x faster than the fastest Z3
endpoint; both independent gates are green.

The compact QF_LIA workload solves `2*x = 2`, constructs an exact integer model, and
evaluates `x` through both official APIs. A compact divisibility path reduced
the first branch-and-bound implementation from 95 allocations to 6. Across
three equal-count runs, the slowest GoSMT endpoint remained over 1,500x faster
than Z3's fastest endpoint and used fewer than half its 15 allocations. General
multi-row branch-and-bound is gated separately: inline coefficient/problem and
simplex arenas, small exact conversions, and direct LIA routing reduced it from
104 allocations to 13, below half of Z3's 28, while remaining over 250x faster
on conservative endpoints. Both workloads validate the returned model.

The Boolean QF_LIA workload selects between `x = 1` and `x = 2`, excludes the
first value, and evaluates the resulting model. Typed compact equality,
choice, and disequality terms plus a concrete branch arena reduced the initial
implementation from 48 allocations to 7. The slowest GoSMT endpoint remains
over 175x faster than Z3's fastest endpoint while using 35% of its allocation
count.

The mixed EUF+QF_LRA row partitions normalized conjuncts into inline,
polarity-aware theory arenas and merges independent arithmetic models. It fell
from an initial 26 allocations to 13, just under half of Z3's 27. The overflow
tableau path is separately exercised with ten exact variables and twenty
constraints; the small arena does not impose a capacity limit.

The shared QF_UFLRA workload forces LRA's reciprocal bounds to imply `x = y`
and then makes `f(x) != f(y)` contradict EUF congruence. Symbolic real-function
applications and direct equality evidence reduced the first working result
from 23 allocations and roughly 6.3 us to 7 allocations and 1.32–1.50 us.
Nontrivial implied equalities retain the exact auxiliary-simplex fallback.

The purified QF_UFLRA workload places `f(x)` and `f(y)` directly inside
opposing linear bounds while arithmetic proves `x = y`. Collision-free fresh
symbols and exact defining equalities preserve the application semantics.
Keeping symbol equalities and unary application comparisons concrete until a
single fused conjunction reduced the working implementation from 70 to 9
allocations. Across three equal-count runs, GoSMT remained at least 79x faster
than Z3 and used under 40% of its Go allocation count.

The binary QF_UFLRA workload swaps two arithmetic-equal real arguments across
`combine(x,y)` and `combine(y,x)` and places the results under contradictory
bounds. The initial materializing GoSMT surface used 32 allocations and failed
the gate. Retaining binary function identity and both argument symbols in the
deferred Go+ representation reduced it to 9 allocations; conservative
equal-count endpoints remain over 70x faster than Z3.

The first QF_BV workload fixes an 8-bit symbol, masks its low nibble, and
disequates the forced result. The general bit-blaster initially measured 38
allocations. Deferred width-indexed values plus a compact unary relation arena
reduced the public cold path to 4 allocations while preserving the general
SAT fallback and arbitrary-width representation. Across five equal-count
runs, the conservative throughput endpoints are over 1,500x apart and GoSMT
uses fewer than one quarter of Z3's Go allocations.

The independent ordering workload fixes an 8-bit symbol to `0x7f` and denies
that it is unsigned-less than `0x80`. Compact assigned-symbol relations cover
signed and unsigned `<`/`<=` without bypassing the general comparator circuit.
Across five equal-count runs it uses 4 allocations versus Z3's 15 and remains
over 1,500x faster at conservative endpoints.

The multiplication workload fixes a symbolic byte to 13 and contradicts the
derived modular product `x * 7 = 91`. The general schoolbook multiplier remains
available to the SAT backend; the public assigned-symbol relation avoids
building that circuit when the exact assignment already decides it. Five
equal-count runs use 4 allocations versus Z3's 18 and remain over 1,300x
faster at conservative endpoints.

The shift workload fixes a symbolic byte to `0x81` and contradicts its logical
right shift by four. The general backend handles variable amounts, including
amounts at least the width and non-power-of-two widths; the compact assigned
relation decides this public case without constructing the full selector
circuit. Five equal-count runs use 4 allocations versus Z3's 18 and remain
over 1,300x faster conservatively.

The division workload fixes a symbolic byte to 100 and contradicts
`bvudiv(x,7) = 14`. The general restoring divider covers UDIV/UREM and signed
normalization for SDIV/SREM, including all SMT-LIB zero-divisor outcomes. The
assigned-symbol path uses 4 allocations versus Z3's 18 and is over 1,400x
faster at conservative five-run endpoints.

The structural workload fixes an 8-bit symbol to `0xab` and contradicts
extracting bits 7 through 4 as the indexed 4-bit value `0xa`. General concat,
extract, zero extension, and sign extension preserve computed widths through
the bit-blaster and model evaluator. The compact extraction path uses 4
allocations versus Z3's 16 and remains over 1,390x faster conservatively.

The rotation workload fixes an 8-bit symbol to `0x81` and contradicts its
one-bit left rotation being `0x03`. GoSMT retains the indexed operation as a
compact relation and uses 4 allocations versus Z3's 18, a 77.8% reduction;
the conservative equal-count endpoint remains over 1,400x faster. The pinned
Z3 Go binding does not expose `Z3_mk_rotate_left`, so its benchmark constructs
the identical one-bit rotation from two extracts and a concat.

The overflow workload fixes an 8-bit symbol to `0xff` and contradicts overflow
from adding one. Inline exact arithmetic initially left the compact public path
at 9 allocations; allocation-free small-width overflow checks reduced it to 4,
versus Z3's 16, while preserving arbitrary-precision checks above 64 bits. The
pinned Z3 Go binding omits the dedicated overflow constructor, so its benchmark
uses the equivalent unsigned identity `(x + 1) < x`.

The ground QF_UFBV workload equates two indexed 8-bit symbols and disequates
the 4-bit results of applying the same unary function. The general congruence
bit-blaster initially used 54 allocations. A compact typed UFBV relation plus
inline congruence closure reduced the contradiction path to 8 allocations,
65.2% fewer than Z3's 23, while the conservative endpoint remains over 860x
faster. Satisfiable and arithmetic-coupled formulas continue through the full
bit-blasted application model rather than the contradiction-only fast path.

The unsigned BV-to-Int workload fixes an 8-bit symbol and contradicts its
exact unsigned integer image. A compact mixed conversion relation, preserved
through the GoSMT façade and copied directly into the solver arena, reduced the
initial bit-blasted path from 46 allocations and ~3.33–3.38 us to 6
allocations and ~698–700 ns: an 87.0% allocation reduction and more than 4.7x
internal speedup. It uses less than half of Z3's 13 visible Go allocations and
remains over 1,270x faster conservatively. The Z3 Go binding omits
`Z3_mk_bv2int`, so the comparison uses the equivalent boundary equality
`x = #xff`.

The first array workload contradicts the read-over-write identity at a ground
integer index. Its initial generic façade path used 9 allocations and
~410–415 ns. Preserving a one-store array witness through GoSMT, folding exact
integer equality, and short-circuiting constant Boolean assertions reduced it
to 5 allocations and ~318–320 ns. That is 44.4% fewer allocations and roughly
23% less latency than the initial array path, while using under 39% of Z3's
visible Go allocations and remaining over 2,400x faster conservatively.

The symbolic array workload equates two integer arrays and contradicts
congruence of reads at the same exact index. The initial map-backed solver and
materializing façade used 23 allocations and ~1.17 us. Inline union-find arenas
and compact array/read relations reduced it to 6 allocations and ~531–537 ns:
73.9% fewer allocations and over 2.1x internal speedup. It uses 35% of Z3's
17 visible Go allocations and remains over 1,550x faster conservatively.

The symbolic-index array workload equates two integer indices and denies the
read-over-write result across those equivalent indices. Compact one-word
integer variables and a deferred symbolic store/read relation reduced the
working path from 14 to 9 allocations and ~863–865 ns. It uses under 43% of
Z3's 21 visible Go allocations and remains over 1,040x faster conservatively.

The extensional-model workload constrains one observed read, requires two
array symbols to differ, retrieves the satisfying model, and evaluates that
read. A shared immutable finite interpretation records defaults, observed
overrides, and a witness value for each distinct array class. The complete
path uses 10 allocations versus Z3's 21 and ~1.281–1.284 us versus
~1.023–1.123 ms, remaining over 796x faster conservatively.

The store-chain workload denies equality between two extensionally identical
two-update arrays whose distinct-index stores occur in opposite order. The
standard-library solver compares every updated index over the shared base;
GoSMT preserves two exact updates in its deferred representation and can fold
the finite comparison before materialization. The resulting path uses 7
allocations versus Z3's 17 and ~489–495 ns versus ~1.012–1.151 ms, remaining
over 2,040x faster conservatively.

The cross-base workload equates one-update arrays rooted at distinct symbols
and then denies equality of their base reads at an unmodified index. An
exception-aware bridge propagates equality outside the overwritten cells while
leaving those hidden base cells independent. A compact typed store/read
conjunction reduced the first public path from 24 to 8 allocations and from
~1.55 us to ~664–686 ns. Z3 uses 21 allocations and ~1.012–1.147 ms, leaving
GoSMT over 1,475x faster at conservative endpoints.

The constant-base workload equates a symbolic array with the all-zero array and
then denies a zero read. Exact constant-array defaults and read-to-value atoms
remain typed deferred relations, while the general solver records the default
constraint for model construction and conflicting-equation detection. The
public path fell from 11 to 6 allocations and from ~1.33 us to ~596–641 ns.
Z3 uses 16 allocations and ~0.830–1.031 ms, leaving GoSMT over 1,290x faster
at conservative endpoints.

The mixed QF_AUFLIA workload uses reciprocal IDL bounds to imply equality of
two symbolic integer indices, then denies the corresponding store/read result.
The general product rejects falsely independent shared-symbol models, proves
the equality in the difference graph, and seeds the array model from the IDL
assignment. Compact Go+ integer variables and a typed equality-exchange term
reduced the first path from 15 to 7 allocations and from ~1.75 us to
~830–834 ns. Z3 uses 22 allocations and ~0.941–1.110 ms, leaving GoSMT over
1,120x faster conservatively.

The exact-index QF_AUFBV workload denies a width-indexed read-over-write law.
A compact Go+ array witness folds the exact address and value without building
generic interface terms. It uses 4 allocations versus Z3's 16 and
~554–560 ns versus ~1.06–1.15 ms: 75% fewer visible Go allocations and over
1,890x conservative throughput.

The symbolic-index QF_AUFBV workload equates two 4-bit addresses and denies the
corresponding 8-bit stored value. The stdlib's typed
`BitVectorArrayEqualityExchange` carries the BV equality into array
congruence, while GoSMT preserves the one-store witness compactly. It uses 5
allocations versus Z3's 23 and ~865–868 ns versus ~1.05–1.16 ms: over 78%
fewer visible Go allocations and over 1,200x conservative throughput.

The QF_AUFBV extensional-model workload requires two arrays to differ, checks
the generated 4-bit witness, and evaluates both 8-bit values. Width-aware
symbols retain the evidence needed after dependent-index erasure. The complete
path uses 8 allocations versus Z3's 18 and ~1.31–1.32 us versus
~1.12–1.18 ms: 55.6% fewer visible Go allocations and over 840x conservative
throughput.

The two-store QF_AUFBV workload denies equality between extensionally
identical arrays whose distinct updates occur in opposite order. The compact
GoSMT witness normalizes overwrites and compares the finite update maps before
materialization. It uses 4 allocations versus Z3's 22 and ~769–770 ns versus
~1.01–1.12 ms: 81.8% fewer visible Go allocations and over 1,300x
conservative throughput.

Inside the solver-neutral `std/smt` layer, QF_BOOL cold allocation count fell
from 20 in the initial CNF/DPLL implementation to 5, a 75% reduction; warm
checks remain allocation-free. GoSMT's QF_BOOL compatibility-layer count fell
from 25 to 12 (52%), clearing its internal reduction milestone. The stricter
Z3-relative target of at most 6 allocations remains independently red.

The ground-EUF standard-library core fell from 12 to 4 allocations per cold
congruence check (67%) after moving its union-find and relation storage into
inline arenas. Its latency improved from 275–277 ns to 235–240 ns. The GoSMT
compatibility construction boundary still records 14 allocations, so the
independent Z3-relative allocation gate remains red even though throughput is
more than three orders of magnitude faster.

Binary EUF retains both argument sorts and the result sort in Go+ indices. Its
same-harness contradiction equates both arguments and disequates the two
applications. A compact polarity-bearing Boolean conjunction reduced the
initial GoSMT result from 17 to 15 allocations, exactly half of the pinned Z3
binding's 30, while the conservative throughput endpoints remain over 1,000x
apart. This new binary workload clears both gates; it does not retroactively
waive the independently red unary cold-allocation row.

The first-UIP CDCL implementation learns 17 clauses on the direct 5-into-4
pigeonhole workload. Reusing conflict-analysis state reduced that core
benchmark from 55 to 17 allocations (69%). GoSMT's clause/CNF fusion then
reduced the full public workload from 342 to 27 allocations while retaining
more than two orders of magnitude throughput advantage over Z3.

On the harder 7-into-6 pigeonhole workload, activity selection and geometric
restarts are exercised rather than merely present. Expanding the reusable
first-UIP clause arena reduced the initial 582 allocations to 34 (94%); the
current direct-core cold solve is approximately 1.17–1.20 ms, 180,544 B/op,
and 25 allocations. The full GoSMT construction-and-solve comparison also
clears both independent Z3-relative gates, at over 2.3× throughput and fewer
than 5% of Z3's Go allocation count.

## SMT-LIB front-end baseline

The first measured standard-library parser and command-execution baseline on
Apple M5 Max is:

| workload | ns/op range | B/op | allocs/op |
|---|---:|---:|---:|
| parse a 9-command QF_IDL script | 2,480–2,491 | 9,816 | 106 |
| parse and execute a 7-command QF_BOOL script | 2,722–2,732 | 11,872 | 104 |
| parse and execute an 8-command QF_IDL script | 3,320–3,330 | 12,712 | 129 |

These measurements include syntax-tree construction and are red internal
baselines. The first allocation milestone is at most 53, 52, and 64
allocations respectively, while preserving spans, arbitrary-size numeral
syntax, raw-command round trips, and exhaustive Go+ result types. They are not
yet Z3-relative gates because the official Go binding does not expose the
SMT-LIB parser as an equivalent Go allocation workload.
