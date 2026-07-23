# Performance contract

The baseline oracle is Z3 4.16.0. Each benchmark records semantic work only
(construction separately from solving), warm and cold modes, satisfiable and
unsatisfiable instances, bytes/op, allocations/op, and result/model validation.

Release gate for every declared workload family:

- GoSMT throughput is at least 2× Z3's corresponding API/CLI workload.
- GoSMT allocations are at most 50% of the pinned Go-facing baseline.
- No timeout, `unknown`, invalid model, or omitted workload counts as a win.

The current Boolean core combines direct constants, allocation-free inline
CNF, fixed-bitset choice solving, linear-size Tseitin encoding, scanning DPLL,
and watched first-UIP CDCL with learned clauses, backjumping, activity, and
geometric restarts. The old 62-variable ceiling is gone. Immutable warm checks
remain allocation-free, while every cold public workload below is gated
independently against the official pinned Z3 Go API.

QF_IDL retains inline `int64` values and promotes only out-of-range values to
immutable arbitrary-precision integers. Compact difference constraints and
graph storage use 7 allocations in the current cold public workload versus
Z3's 20, while wide 101-bit bounds use the same exact path.

## Official Go API comparison

`benchmarks/z3api` links both solvers into the same benchmark process using
Z3's official Go binding at the pinned commit. Current Apple M5 Max results:

| QF_BOOL workload | GoSMT | Z3 4.16.0 | Throughput gate | Allocation gate |
|---|---:|---:|---|---|
| QF_BOOL warm check | ~3.33 ns, 0 B, 0 allocs | ~40 us, 0 B, 0 allocs | green | green |
| QF_BOOL cold construct + check | ~1.315–1.335 us, 4,176 B, 5 allocs | ~0.85–1.05 ms, 200 B, 13 allocs | green | green (target ≤6 allocs) |
| QF_IDL warm check | ~3.33 ns, 0 B, 0 allocs | ~147 us, 0 B, 0 allocs | green | green |
| QF_IDL cold construct + check | ~827 ns–1.02 us, 2,704 B, 8 allocs | ~1.07–1.23 ms, 320 B, 20 allocs | green | green (target ≤10 allocs) |
| QF_LIA exact single-equation model construction + evaluation | ~763–772 ns, 3,264 B, 6 allocs | ~1.30–1.40 ms, 224 B, 15 allocs | green | green (target ≤7 allocs) |
| QF_LIA general two-row model construction + two evaluations | ~5.68–5.74 us, 3,680 B, 13 allocs | ~1.45–1.53 ms, 424 B, 28 allocs | green | green (target ≤14 allocs) |
| Boolean QF_LIA disjunction+disequality model construction + evaluation | ~7.19–7.24 us, 3,552 B, 7 allocs | ~1.28–1.41 ms, 304 B, 20 allocs | green | green (target ≤10 allocs) |
| QF_LIA signed Euclidean div/mod model construction + two evaluations | ~1.65–1.69 us, 4,392 B, 8 allocs | ~1.27–1.40 ms, 352 B, 23 allocs | green | green (target ≤11 allocs) |
| ground QF_UF cold construct + check | ~1.330–1.341 us, 4,680 B, 8 allocs | ~0.78–1.00 ms, 304 B, 21 allocs | green | green (target ≤10 allocs) |
| binary ground QF_UF cold construct + check | ~1.691–1.712 us, 4,824 B, 9 allocs | ~0.83–0.97 ms, 480 B, 30 allocs | green | green (target ≤15 allocs) |
| finite QF_DT enum construct + model evaluation | ~1.98 us, 6,320 B, 11 allocs | ~1.17 ms, 512 B, 31 allocs | green | green (target ≤15 allocs) |
| unary recursive QF_DT construct + selector + model evaluation | ~2.75 us, 7,152 B, 18 allocs | ~1.06 ms, 544 B, 38 allocs | green | green (target ≤19 allocs) |
| binary recursive QF_DT construct + two selectors + model evaluation | ~3.154–3.271 us, 7,296 B, 20 allocs | ~0.989–1.081 ms, 656 B, 43 allocs | green (>302x) | green (target ≤21 allocs) |
| QF_BOOL 5-into-4 pigeonhole construct + check | ~76.60–79.80 us, 185,177 B, 13 allocs | ~1.091–1.173 ms, 6,536 B, 360 allocs | green (>13.6x) | green (target ≤180 allocs) |
| QF_BOOL 7-into-6 pigeonhole construct + check | ~326.05–326.89 us, 1,111,514 B, 23 allocs | ~2.962–3.068 ms, 24,728 B, 1,078 allocs | green (>9.0x) | green (target ≤539 allocs) |
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
| QF_BV unsigned BV-to-Int contradiction | ~1.398–1.443 us, 3,688 B, 5 allocs | ~0.938–1.048 ms, 200 B, 13 allocs | green | green (target ≤6 allocs) |
| ground QF_ALIA integer-array read-over-write | ~318–320 ns, 920 B, 5 allocs | ~0.79–1.00 ms, 200 B, 13 allocs | green | green (target ≤6 allocs) |
| ground QF_ALIA equal-array select congruence | ~531–537 ns, 936 B, 6 allocs | ~0.84–1.03 ms, 264 B, 17 allocs | green | green (target ≤8 allocs) |
| ground QF_ALIA symbolic-index store/read congruence | ~1.213–1.222 us, 3,256 B, 7 allocs | ~0.894–1.083 ms, 328 B, 21 allocs | green | green (target ≤10 allocs) |
| ground QF_ALIA extensional model construction + evaluation | ~1.569–1.608 us, 5,120 B, 8 allocs | ~0.998–1.136 ms, 320 B, 21 allocs | green | green (target ≤10 allocs) |
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

The div/mod workload fixes `x = -7`, proves `div(x,-3) = 3` and
`mod(x,-3) = 2`, and evaluates both model terms. Sharing a typed compact
quotient/remainder system reduced the first general-elimination result from 39
allocations and roughly 34 us to 8 allocations and roughly 1.7 us. The general
elimination remains available for unassigned symbols; the compact official
path is over 750x faster than Z3 and uses under 35% of its allocations.

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
initial bit-blasted path from 46 allocations to 5. The current façade defers a
symbol conversion without boxing either its bit-vector symbol or conversion
AST; equality emits the standard library's compact relation directly. It uses
38.5% of Z3's 13 visible Go allocations and remains over 650x faster at the
current conservative endpoints. The Z3 Go binding omits
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
working path from 14 to 7 allocations and ~1.213–1.222 us. It uses one third
of Z3's 21 visible Go allocations and remains over 730x faster conservatively.

The extensional-model workload constrains one observed read, requires two
array symbols to differ, retrieves the satisfying model, and evaluates that
read. A shared immutable finite interpretation records defaults, observed
overrides, and a witness value for each distinct array class. The complete
path uses 8 allocations versus Z3's 21 and ~1.569–1.608 us versus
~0.998–1.136 ms, remaining over 620x faster conservatively.

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

Inside the solver-neutral `std/smt` layer, a fixed-capacity `BooleanInlineCNF`
keeps small authored clauses, propagation state, and models stack-backed while
the existing watched-literal solver remains the general path. GoSMT's complete
cold public workload now uses 5 allocations versus the pinned Z3 binding's 13,
clearing the stricter Z3-relative target of at most 6; warm checks remain
allocation-free.

The ground-EUF standard-library core retains union-find and relation storage in
inline arenas. Compact, sort-bearing `UninterpretedEUFTerm` relations now let
Go+ preserve dependent sort indices without allocating the general AST for
symbol and shallow-application workloads. The complete unary public workload
uses 8 allocations versus Z3's 21, clearing the target of at most 10.

Binary EUF retains both argument sorts and the result sort in Go+ indices. Its
same-harness contradiction equates both arguments and disequates the two
applications. Compact terms plus the polarity-bearing conjunction reduce the
full public workload from 15 to 9 allocations versus the pinned binding's 30;
both unary and binary EUF rows now clear their independent gates.

The finite QF_DT workload constrains a symbolic three-constructor enumeration
with constructor disequality and a recognizer, then evaluates its exact model.
Inline union-find and disequality arenas reduced the first implementation from
17 to 11 allocations versus Z3's 31, while remaining over 550x faster on the
same official-API cold workload.

The unary recursive QF_DT workload constructs `succ(succ(zero))`, constrains
and evaluates its selector and recognizer, and validates the nested model. A
small retained-child arena reduces the public workload to 19 allocations
versus Z3's 38; storing the datatype interpretation once behind the immutable
model reduces the current path further to 18 allocations. Conservative
same-process endpoints remain more than 350x apart.

The binary recursive QF_DT workload constructs a branching `node(left,right)`,
evaluates both selectors, and validates the exact tree model. Per-field
injectivity and graph acyclicity share the same indexed datatype arena. It uses
20 allocations versus Z3's 43 and 3.154–3.271 us versus 0.989–1.081 ms,
clearing both gates independently.

The mixed recursive QF_DT workload constructs `node(payload Int, next Tree)`,
checks a scalar selector and recognizer, and extracts the exact nested model
through the public context-indexed API. Constant scalar fields now bypass the
inner arithmetic solver while symbolic fields retain explicit model evidence.
On Apple M5 Max, five 1,000-iteration samples use 19 allocations and
4.244–5.027 us for GoSMT versus 41 allocations and 0.922–1.073 ms for the
pinned Z3 4.16.0 Go API. This is 53.7% fewer allocations and at least 183x
faster (about 226x at the median), including declaration, construction,
solving, and exact model evaluation.

The mutually recursive QF_DT workload builds a `Tree`/`Forest` declaration
group, crosses both target-indexed selector boundaries, solves the nested
constructor equality, and extracts the complete model. Three 500-iteration
Apple M5 Max samples use 22 allocations and 6.584–7.439 us for GoSMT versus
58 allocations and 0.875–1.060 ms for pinned Z3. This is 62.1% fewer
allocations and at least 117x faster (about 146x at the median), including
both declarations, construction, solving, and model evaluation.

The unary parametric QF_DT workload instantiates `PList Int`, then constructs,
selects, recognizes, solves, and evaluates a `cons` model through both public
APIs. Three 500-iteration Apple M5 Max samples use 19 allocations and
5.412–6.407 us for GoSMT versus 41 allocations and 0.909–1.065 ms for pinned
Z3. This is 53.7% fewer allocations and about 172x faster at the median.

Normalized CNF now recognizes disjoint positive choice groups constrained only
by binary incompatibilities, the common core of one-hot allocation, graph
coloring, and finite scheduling. A fixed 64-variable bit-set search avoids
remapping these formulas through Tseitin/CDCL while the general watched solver
remains the fallback. The full 5-into-4 public workload uses 13 allocations
versus Z3's 360 and is at least 13.6x faster. The harder 7-into-6 workload uses
23 allocations versus 1,078 and 326.05–326.89 us versus 2.962–3.068 ms, at
least 9.0x faster. Both results include public expression construction.

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
