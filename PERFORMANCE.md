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
| Boolean QF_S model selection + evaluation | ~3.902–3.910 us, 7,120 B, 6 allocs | ~1.018–1.072 ms, 464 B, 30 allocs | green (>260x) | green (target ≤15 allocs) |
| single-unknown QF_SLIA word equation + evaluation | ~1.575–1.586 us, 8,192 B, 6 allocs | ~0.979–1.059 ms, 256 B, 17 allocs | green (>617x) | green (target ≤8 allocs) |
| two-symbol uniquely delimited QF_SLIA word equation + evaluation | ~1.728–1.755 us, 7,888 B, 6 allocs | ~1.951–2.042 ms, 368 B, 23 allocs | green (>1,111x) | green (target ≤11 allocs) |
| two-adjacent-symbol canonical QF_SLIA word equation + evaluation | ~1.698–1.714 us, 7,888 B, 6 allocs | ~1.195–1.264 ms, 288 B, 20 allocs | green (>697x) | green (target ≤10 allocs) |
| repeated-symbol QF_SLIA word equation + evaluation | ~1.711–1.740 us, 7,888 B, 6 allocs | ~2.711–2.820 ms, 240 B, 16 allocs | green (>1,558x) | green (target ≤8 allocs) |
| ambiguous word equation + ground equality interaction | ~3.354–3.359 us, 9,296 B, 8 allocs | ~0.987–1.084 ms, 432 B, 27 allocs | green (>293x) | green (target ≤13 allocs) |
| word equation + exact code-point length interaction | ~3.351–3.366 us, 9,328 B, 10 allocs | ~1.518–1.584 ms, 384 B, 26 allocs | green (>450x) | green (target ≤13 allocs) |
| word equation + code-point length bounds | ~4.395–4.413 us, 10,608 B, 13 allocs | ~1.673–1.752 ms, 440 B, 29 allocs | green (>379x) | green (target ≤14 allocs) |
| word equation + derived substring equality | ~5.879–5.897 us, 8,168 B, 12 allocs | ~1.813–1.866 ms, 424 B, 29 allocs | green (>307x) | green (target ≤14 allocs) |
| ground `Seq Int` construction + equality/length/model evaluation | ~3.176–3.193 us, 8,368 B, 12 allocs | ~0.955–1.039 ms, 456 B, 30 allocs | green (>299x) | green (target ≤15 allocs) |
| ground `Seq Int` extract/contains/index/replace + model evaluation | ~5.969–5.978 us, 9,680 B, 23 allocs | ~0.927–1.061 ms, 848 B, 53 allocs | green (>155x) | green (target ≤26 allocs) |
| ground-assigned symbolic `Seq Int` + derived model evaluation | ~6.247–6.337 us, 16,760 B, 22 allocs | ~1.049–1.109 ms, 768 B, 48 allocs | green (>165x) | green (target ≤24 allocs) |
| positive symbolic `Seq Int` prefix/contains/suffix witness | ~5.099–5.112 us, 14,936 B, 16 allocs | ~5.635–5.769 ms, 528 B, 34 allocs | green (>1,102x) | green (target ≤17 allocs) |
| exact-length symbolic `Seq Int` witness + overlap placement | ~5.722–5.792 us, 14,984 B, 18 allocs | ~3.601–3.744 ms, 584 B, 37 allocs | green (>621x) | green (target ≤18 allocs) |
| relational-length symbolic `Seq Int` witness + bounded placement | ~6.882–6.897 us, 14,992 B, 20 allocs | ~4.140–4.292 ms, 656 B, 41 allocs | green (>600x) | green (target ≤20 allocs) |
| affine-length symbolic `Seq Int` witness + bounded placement | ~7.394–7.411 us, 15,120 B, 25 allocs | ~4.123–4.288 ms, 800 B, 50 allocs | green (>556x) | green (target ≤25 allocs) |
| symbolic `Seq Int` equality-class model + compatible requirement merging | ~8.840–8.850 us, 13,144 B, 29 allocs | ~4.217–4.391 ms, 1,000 B, 60 allocs | green (>476x) | green (target ≤30 allocs) |
| two-symbol affine `Seq Int` lengths + paired exact models | ~5.282–5.295 us, 10,824 B, 19 allocs | ~1.400–1.446 ms, 720 B, 46 allocs | green (>264x) | green (target ≤23 allocs) |
| three-symbol affine `Seq Int` lengths + atomic exact models | ~6.566–6.589 us, 12,480 B, 24 allocs | ~1.450–1.503 ms, 864 B, 56 allocs | green (>220x) | green (target ≤28 allocs) |
| three-symbol affine `Seq Int` inequality + exact bounded models | ~6.818–6.903 us, 12,480 B, 24 allocs | ~1.432–1.490 ms, 864 B, 56 allocs | green (>207x) | green (target ≤28 allocs) |
| interacting affine `Seq Int` relation system + atomic models | ~8.737–8.753 us, 17,472 B, 32 allocs | ~1.680–1.735 ms, 1,192 B, 72 allocs | green (>191x) | green (target ≤36 allocs) |
| four-symbol affine `Seq Int` relation system + atomic models | ~11.175–11.233 us, 19,688 B, 38 allocs | ~1.793–1.886 ms, 1,496 B, 90 allocs | green (>159x) | green (target ≤45 allocs) |
| five-symbol affine `Seq Int` relation system + atomic models | ~13.553–13.704 us, 23,008 B, 45 allocs | ~2.006–2.078 ms, 1,912 B, 109 allocs | green (>146x) | green (target ≤54 allocs) |
| disjunctive symbolic `Seq Int` branch backtracking + exact model | ~6.129–6.166 us, 20,272 B, 20 allocs | ~2.547–2.598 ms, 712 B, 44 allocs | green (>413x) | green (target ≤22 allocs) |
| two shared-symbol word equations + global backtracking | ~3.716–3.732 us, 8,224 B, 8 allocs | ~1.710–1.763 ms, 480 B, 32 allocs | green (>458x) | green (target ≤16 allocs) |
| word equation + regular-language candidate selection | ~4.177–4.193 us, 8,552 B, 9 allocs | ~1.270–1.360 ms, 432 B, 29 allocs | green (>302x) | green (target ≤14 allocs) |
| word equation + general Boolean-regex split selection | ~5.504–5.516 us, 9,144 B, 13 allocs | ~1.423–1.496 ms, 480 B, 32 allocs | green (>257x) | green (target ≤16 allocs) |
| word equation + string disequality split selection | ~4.513–4.560 us, 10,576 B, 9 allocs | ~1.289–1.354 ms, 368 B, 25 allocs | green (>282x) | green (target ≤12 allocs) |
| word equation + contains/prefix split selection | ~6.425–6.457 us, 15,696 B, 13 allocs | ~1.852–1.916 ms, 392 B, 26 allocs | green (>286x) | green (target ≤13 allocs) |

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

The `update-field` cold workload constructs a `PList Int`, solves its original
value, applies a typed head update, and evaluates the rebuilt model. Three
500-iteration samples use 14 allocations and 2.868–3.405 us for GoSMT versus
35 allocations and 0.906–1.052 ms for pinned Z3. This is 60.0% fewer
allocations and about 330x faster at the median.

The parametric differential corpus also leaves a second `PList Int`
unconstrained and requires its scalar `match` result to equal a nonzero
integer. Constructor coloring and scalar solving are therefore checked as one
decision: both GoSMT and pinned Z3 must select `cons` and solve its synthetic
head field. Exact model extraction is covered separately in the standard
library tests.

The datatype-valued match cold workload leaves a two-constructor input
unconstrained, requires its `Color` result to be `blue`, solves the resulting
constructor choice, and extracts the selected input model. Three 500-iteration
Apple M5 Max samples use 18 allocations and 3.531–4.053 us for GoSMT versus
46 allocations and 1.017–1.167 ms for pinned Z3. This is 60.9% fewer
allocations and about 300x faster at the median. The pinned Go binding omits
the ITE constructor, so its side uses the logically equivalent guarded
disjunction through the public API.

The multi-parameter datatype cold workload constructs a monomorphized
`Pair Int Bool`, solves its two-field value, and extracts the complete value
and both fields. Three 500-iteration Apple M5 Max samples use 14 allocations
and 3.172–3.642 us for GoSMT versus 37 allocations and 0.872–1.053 ms for
pinned Z3. This is 62.2% fewer allocations and about 300x faster at the
median.

The mutually parametric datatype cold workload constructs concrete
`Tree Int`/`Forest Int` identities jointly, crosses both family boundaries,
solves a scalar-bearing nested value, and extracts its exact model. Three
500-iteration Apple M5 Max samples use 21 allocations and 4.955–5.559 us for
GoSMT versus 57 allocations and 0.862–1.064 ms for pinned Z3. This is 63.2%
fewer allocations and about 200x faster at the median.

The Boolean QF_DT cold workload solves a disjunction plus a negated datatype
equality, then validates the selected value, both constructor values, both
recognizers, both equality atoms, and the complete authored formula. Three
500-iteration Apple M5 Max samples use 19 allocations and 4.765–5.350 us for
GoSMT versus 47 allocations and 0.890–1.063 ms for pinned Z3. This is 59.6%
fewer allocations and about 200x faster at the median. Inline branch and atom
arenas replace the initial heap-slice implementation, which used 56
allocations.

The QF_SLIA cold workload constructs a symbolic string, concatenation, length,
contains, prefix, and suffix constraints, solves them, and validates the
string, length, and complete formula model. The initial public façade used 28
allocations. Compact inline string terms and relation systems reduce three
Apple M5 Max samples to 9 allocations and 2.894–2.927 us versus 31 visible Go
allocations and 1.044–1.097 ms for pinned Z3. This is 71.0% fewer allocations
and about 360x faster at the median. Z3's count does not include its native C
heap. Constant concatenation canonicalization also lowers the standard-library
core from 6 allocations and 0.684–0.708 us to 3 allocations and
0.645–0.671 us.

The indexed QF_SLIA cold workload constructs and validates `str.at`,
`str.substr`, `str.indexof`, and first-occurrence `str.replace`. Its initial
façade path used 35 allocations. Constant folding lowers three Apple M5 Max
samples to 11 allocations and 3.575–3.605 us versus pinned Z3's 39 visible Go
allocations and 0.983–1.049 ms. This is 71.8% fewer allocations and about 285x
faster at the median.

The conversion QF_SLIA cold workload constructs and validates string-to-int
and int-to-string round trips. Small-decimal parsing and known equality
propagation reduce the initial 13-allocation path to 8 allocations and
1.224–1.233 us across three Apple M5 Max samples. Pinned Z3 uses 18 visible Go
allocations and 0.978–1.061 ms. This is 55.6% fewer allocations and about 800x
faster at the median.

The QF_S regular-language cold workload constructs a string literal, converts
another literal to a regex, checks membership, solves it, and validates the
Boolean model through each public API. Compact ground-regex construction uses
5 allocations and 1.023–1.044 us across five Apple M5 Max samples. Pinned Z3
uses 10 visible Go allocations and 0.809–1.023 ms. This is exactly 50.0% fewer
allocations and about 900x faster at the median; Z3's native C heap is not
included.

The symbolic QF_S cold workload constructs a literal-prefix plus bounded
character-range language, constrains an otherwise free string, synthesizes its
shortest witness, solves, extracts that string, and validates the authored
membership formula. An inline postfix regex program lowers five Apple M5 Max
samples to 9 allocations and 1.897–1.938 us. Pinned Z3 uses 20 visible Go
allocations and 2.807–2.903 ms. This is 55.0% fewer allocations and about
1,480x faster at the median.

The interacting QF_S cold workload constrains one symbolic string by two
overlapping unions and one negative membership, synthesizes their shared
witness, solves, extracts the string, and validates the full conjunction.
Direct fixed-bitset evaluation plus single-pass inline constraint collection
uses 13 allocations and 4.658–4.701 us across five Apple M5 Max samples.
Pinned Z3 uses 27 visible Go allocations and 1.239–1.353 ms. This is 51.9%
fewer allocations and about 275x faster at the median.

The Boolean QF_S cold workload combines singleton-regex memberships through
disjunction, negation, and Boolean ITE, selects the exact surviving model, and
validates the complete formula. A standard-library inline postfix Boolean
program and fixed four-atom model search reduce the initial public path from
23 allocations and roughly 10.2 us to 6 allocations and 3.902–3.910 us.
Pinned Z3 uses 30 visible Go allocations and 1.018–1.072 ms. This is 80.0%
fewer allocations and over 260x conservative-endpoint throughput.

The single-unknown word-equation workload solves
`"go-" ++ x ++ "!" = "go-forge!"`, extracts `x = "forge"`, and validates the
authored equality. A compact prefix/symbol/suffix term plus allocation-free
matching reduces the initial generic path from 25 allocations to 6 and
1.575–1.586 us. Pinned Z3 uses 17 visible Go allocations and
0.979–1.059 ms. This is 64.7% fewer allocations and over 617x
conservative-endpoint throughput.

The ground-assigned symbolic sequence workload binds context-indexed `x` to
`[1, 2, 3]`, validates containment and length, replaces `2` with `9`, and
extracts both the symbolic and derived models. Std stores sequence assignments
inline, rejects conflicts exactly, carries them through temporary assumptions,
and returns `unknown` rather than inventing an underconstrained witness. It
uses 22 allocations and 6.247–6.337 us versus pinned Z3's 48 visible Go
allocations and 1.049–1.109 ms. This is 54.2% fewer allocations and over 165x
conservative-endpoint throughput.

The positive symbolic sequence workload constructs a context-indexed witness
for simultaneous `[1, 2]` prefix, `[3, 4]` containment, and `[5, 6]` suffix
requirements, then extracts and validates the exact model. Std keeps four
symbols and four containment requirements per symbol inline, merges compatible
prefixes and suffixes, and rejects incompatible boundaries before model
evaluation. It uses 16 allocations and 5.099–5.112 us versus pinned Z3's 34
visible Go allocations and 5.635–5.769 ms. This is 52.9% fewer allocations
and over 1,102x conservative-endpoint throughput.

The disjunctive symbolic sequence workload first offers an impossible
three-element length with a four-element prefix, then falls back to a
four-element suffix alternative and extracts its exact model. Bounded positive
Boolean expansion handles nested `and`/`or` formulas under a 4,096-branch
limit, while the top-level `or` path tries inline alternatives without building
the full normal form. It uses 20 allocations and 6.129–6.166 us versus pinned
Z3's 44 visible Go allocations and 2.547–2.598 ms. This is 54.5% fewer
allocations and over 413x conservative-endpoint throughput.

The exact-length sequence workload adds length eight to simultaneous two-value
prefix, containment, and suffix requirements, then extracts and validates the
complete model. Std places fixed boundaries and backtracks containment offsets
within a 4,096-state limit, including overlapping prefix/suffix witnesses, and
fills unconstrained positions deterministically with zero. It uses 18
allocations and 5.722–5.792 us versus pinned Z3's 37 visible Go allocations and
3.601–3.744 ms. This is 51.4% fewer allocations and over 621x
conservative-endpoint throughput.

The relational-length sequence workload constrains the same symbolic witness
between lengths six and eight while retaining its prefix, containment, and
suffix requirements. Std normalizes strict and non-strict comparisons into
lower/upper requirements, searches admissible lengths under one shared
placement budget, and proves contradictory bounds without order dependence.
The façade reuses the length expression across both relations. It uses 20
allocations and 6.882–6.897 us versus pinned Z3's 41 visible Go allocations and
4.140–4.292 ms. This is 51.2% fewer allocations and over 600x
conservative-endpoint throughput.

The affine-length sequence workload constrains a shared symbolic length with
one negatively scaled lower-bound form and one shifted positively scaled
upper-bound form while retaining prefix, containment, and suffix requirements.
Std normalizes addition, subtraction, and arbitrary-precision scaling into one
coefficient and constant, uses exact Euclidean division for sign-correct
floor/ceiling bounds, and proves non-divisible equalities unsatisfiable. It uses
25 allocations and 7.394–7.411 us versus pinned Z3's 50 visible Go allocations
and 4.123–4.288 ms. This is exactly 50.0% fewer allocations and over 556x
conservative-endpoint throughput.

The sequence equality-class workload aliases three symbols, contributes
prefix, containment, suffix, exact-length, and compatible shorter requirements
through different aliases, and extracts all three exact models at the full
eight-element inline capacity. Std keeps eight aliases inline, canonicalizes
their requirements before witness construction, and expands the resulting
model back to every public symbol. It uses 29 allocations and 8.840–8.850 us
versus pinned Z3's 60 visible Go allocations and 4.217–4.391 ms. This is 51.7%
fewer allocations and over 476x conservative-endpoint throughput.

The paired affine-length workload solves `2*len(x)+len(y)=9` while requiring a
three-element prefix for `x` and a three-element suffix for `y`, then extracts
both exact models. Std keeps four relations inline, canonicalizes aliases,
enumerates the first bounded length, derives the second by exact Euclidean
division, and commits both witnesses only after local constraints succeed. It
uses 19 allocations and 5.282–5.295 us versus pinned Z3's 46 visible Go
allocations and 1.400–1.446 ms. This is 58.7% fewer allocations and over 264x
conservative-endpoint throughput.

The three-symbol affine-length workload solves
`2*len(x)+len(y)+len(z)=8`, contributes two-element constructive boundaries
to all three symbols, and extracts every exact model. Std stores three
canonical coefficients inline, derives constructive minimum lengths before
bounded recursive enumeration, computes the final length by exact Euclidean
division, rejects coefficient-GCD divisibility conflicts without search, and
commits all witnesses atomically. It uses 24 allocations and
6.566–6.589 us versus pinned Z3's 56 visible Go allocations and
1.450–1.503 ms. This is 57.1% fewer allocations and over 220x
conservative-endpoint throughput.

The multi-symbol affine-inequality workload solves
`2*len(x)+len(y)+len(z)<=8`, contributes two-element constructive boundaries
to all three symbols, and extracts every exact model. Std normalizes strict
and non-strict relations over three inline coefficients, uses sign-correct
integer division for the final bound, and prunes partial assignments whose
minimum possible continuation cannot satisfy the inequality. It uses 24
allocations and 6.818–6.903 us versus pinned Z3's 56 visible Go allocations
and 1.432–1.490 ms. This is 57.1% fewer allocations and over 207x
conservative-endpoint throughput.

The interacting affine-relation workload constrains
`len(x)+len(y)+len(z)>=12` and `2*len(x)+len(y)+len(z)<=16`, contributes
four-element inline prefixes to all three symbols, and extracts every exact
model. Std globally searches three canonical lengths, prunes each partial
assignment against every relation's attainable interval, intersects all final
equalities and inequality bounds, and builds witnesses only after the complete
length tuple succeeds. It uses 32 allocations and 8.737–8.753 us versus pinned
Z3's 72 visible Go allocations and 1.680–1.735 ms. This is 55.6% fewer
allocations and over 191x conservative-endpoint throughput.

The four-symbol affine-relation workload constrains
`len(x)+len(y)+len(z)+len(w)>=16` and
`2*len(x)+len(y)+len(z)+len(w)<=20`, contributes four-element inline
boundaries to all four symbols, and extracts every exact model. Std extends
the fixed coefficient and global-search records to four canonical roots while
retaining interval pruning, exact final-bound intersection, and atomic witness
construction. It uses 38 allocations and 11.175–11.233 us versus pinned Z3's
90 visible Go allocations and 1.793–1.886 ms. This is 57.8% fewer allocations
and over 159x conservative-endpoint throughput.

The five-symbol affine-relation workload constrains the five-length sum to at
least 20 and its first-coefficient-doubled form to at most 24, contributes
four-element inline boundaries to all five symbols, and extracts every exact
model. Std aligns affine root storage with the existing eight-entry inline
alias/value capacities, retaining global interval pruning and atomic witness
construction without changing the four-root allocation count. It uses 45
allocations and 13.553–13.704 us versus pinned Z3's 109 visible Go allocations
and 2.006–2.078 ms. This is 58.7% fewer allocations and over 146x
conservative-endpoint throughput.

The uniquely delimited word-equation workload solves
`"[" ++ x ++ "]" ++ y ++ "!" = "[go]forge!"`, extracts both exact values,
and validates the complete equality. The standard library represents up to
four distinct symbols and their five literal delimiters in a fixed value;
ambiguous, empty, or repeated delimiters use bounded exhaustive search with an
explicit resource limit. This
reduces the initial generic façade from 29 allocations and roughly 2.35 us to
6 allocations and 1.728–1.755 us. Pinned Z3 uses 23 visible Go allocations
and 1.951–2.042 ms. This is 73.9% fewer allocations and over 1,111x
conservative-endpoint throughput.

The canonical bounded word-equation workload solves `x ++ y = "forge"`,
selects the deterministic model `x = ""`, `y = "forge"`, extracts both
values, and validates the equality. The same bounded pattern representation
uses a leftmost split for repeated delimiters and an empty earlier component
for adjacent symbols only when constructing a standalone model; conjunction
propagation still requires a unique forced split. It uses 6 allocations and
1.698–1.714 us versus pinned Z3's 20 visible Go allocations and
1.195–1.264 ms. This is 70.0% fewer allocations and over 697x
conservative-endpoint throughput.

The repeated-symbol workload solves `x ++ "-" ++ x = "go-go"`, extracts
`x = "go"`, and validates the complete equation. Bounded exhaustive search
tries every valid Unicode byte boundary in deterministic shortest-first order,
reuses assignments at repeated occurrences, and returns `unknown` after 4,096
states rather than approximating. It uses 6 allocations and 1.711–1.740 us
versus pinned Z3's 16 visible Go allocations and 2.711–2.820 ms. This is 62.5%
fewer allocations and over 1,558x conservative-endpoint throughput.

The interacting ambiguous workload constrains
`"[" ++ x ++ "]" ++ y ++ "!" = "[a]b]c!"` together with `x = "a]b"`,
thereby selecting the later delimiter split and `y = "c"`. It extracts both
values and validates the conjunction; the paired corpus also proves
incompatible fixed prefixes unsatisfiable. Fixed conjunct storage and
model-seeded bounded search use 8 allocations and 3.354–3.359 us versus pinned
Z3's 27 visible Go allocations and 0.987–1.084 ms. This is 70.4% fewer
allocations and over 293x conservative-endpoint throughput.

The length-interaction workload solves `x ++ y = "forge"` together with
`str.len(x) = 3`, extracts `x = "for"` and `y = "ge"`, and validates the
conjunction. Exact length metadata prunes the Unicode-boundary search by SMT
code-point count and also proves out-of-range lengths unsatisfiable. It uses
10 allocations and 3.351–3.366 us versus pinned Z3's 26 visible Go allocations
and 1.518–1.584 ms. This is 61.5% fewer allocations and over 450x
conservative-endpoint throughput.

The length-bound workload solves the same equation with
`1 < str.len(x) <= 3`, selects the shortest satisfying split `x = "fo"`, and
validates both bounds. Compact order relations avoid materializing generic
integer ASTs, reducing the first public implementation from 18 allocations to
13. Pinned Z3 uses 29 visible Go allocations and 1.673–1.752 ms versus
GoSMT's 4.395–4.413 us. This is 55.2% fewer allocations and over 379x
conservative-endpoint throughput.

The relational-length workload solves `x ++ y = "abcd"` together with
`str.len(x) = str.len(y)`, selecting `x = "ab"` and `y = "cd"` and validating
the complete formula. Compact std relational-length terms preserve both string
operands through the GoSMT façade and compare Unicode code-point counts during
terminal backtracking. It uses 9 allocations and 5.142–5.167 us versus pinned
Z3's 24 visible Go allocations and 2.325–2.436 ms. This is 62.5% fewer
allocations and over 449x conservative-endpoint throughput.

The affine-length workload solves `x ++ y = "abc"` together with
`str.len(y) - str.len(x) = 1`, selecting `x = "a"` and `y = "bc"`.
The same exact evaluator covers n-ary addition and arbitrary-precision
constant scaling, with a separate corpus exercising all three forms and
Boolean combinations. The cold workload uses 14 allocations and
4.720–4.738 us versus pinned Z3's 28 visible Go allocations and
2.452–2.498 ms. This is exactly 50.0% fewer allocations and over 517x
conservative-endpoint throughput.

The integer-valued string-operation workload solves `x ++ y = "abc"` together
with `str.indexof(x, "b", 0) = 1`, selecting `x = "ab"` and `y = "c"`.
The same exact candidate evaluator covers `str.to_int`, `str.to_code`, and
affine integer combinations, with arbitrary-precision conversion checked
separately. Allocation-free Unicode/WTF-8 code-point boundary scanning reduced
the cold workload from 21 allocations to 12. It uses 12 allocations and
5.075–5.080 us versus pinned Z3's 27 visible Go allocations and
2.725–2.811 ms. This is 55.6% fewer allocations and over 536x
conservative-endpoint throughput.

The derived-string workload solves `x ++ y = "abcd"` together with
`str.substr(x, 1, 2) = "bc"`, selecting `x = "abc"` and `y = "d"` and
validating both the derived value and complete formula. The same candidate
path covers `str.at`, first/all replacement, `str.from_int`, and
`str.from_code`; pinned Z3 returns `unknown` for the `str.replace_all`
QF_SLIA case, so that operator remains independently covered by direct
semantic laws. Allocation-free Unicode/WTF-8 boundary scanning keeps the cold
workload at 12 allocations and 5.879–5.897 us versus pinned Z3's 29 visible Go
allocations and 1.813–1.866 ms. This is 58.6% fewer allocations and over 307x
conservative-endpoint throughput.

The ground integer-sequence workload constructs `[7, 11]` through typed
`empty`, `unit`, and `concat`, proves equality with a separately constructed
sequence and length two, then evaluates the sequence, length, and complete
formula. Std and the context-indexed GoSMT façade keep the first eight exact
integer elements inline before exact overflow. It uses 12 allocations and
3.176–3.193 us versus pinned Z3's 30 visible Go allocations and
0.955–1.039 ms. This is 60.0% fewer allocations and over 299x
conservative-endpoint throughput.

The ground integer-sequence operator workload constructs `[1, 2, 3, 2]`,
extracts `[2, 3]`, proves containment, finds the later `2` at index three,
replaces the first `[2, 3]` with `[9]`, and evaluates every derived result and
the complete formula. The same exact evaluator covers `at`, prefix, suffix,
empty subsequences, and out-of-range behavior. It uses 23 allocations and
5.969–5.978 us versus pinned Z3's 53 visible Go allocations and
0.927–1.061 ms. This is 56.6% fewer allocations and over 155x
conservative-endpoint throughput.

The multiple-equation workload solves `x ++ y = "abc"` together with
`x ++ "-" ++ z = "a-tail"`. The second equation forces global backtracking
from the first equation's initial empty split to `x = "a"`, after which the
model contains `y = "bc"` and `z = "tail"`. One fixed-capacity search shares
assignments and the 4,096-state limit across both equations. It uses
8 allocations and 3.716–3.732 us versus pinned Z3's 32 visible Go allocations
and 1.710–1.763 ms. This is 75.0% fewer allocations and over 458x
conservative-endpoint throughput.

The eight-equation workload globally couples four symbols across eight
ground-target equations, including prefix/suffix-wrapped repetitions. A later
equation forces `x = "a"`, after which the exact shared model is `y = "bc"`,
`z = "tail"`, and `w = "!"`. Sixteen fixed conjunct slots and eight fixed
equation slots avoid heap-backed search metadata while preserving the shared
4,096-state limit. It uses 15 allocations and 12.196–12.216 us versus pinned
Z3's 62 visible Go allocations and 2.992–3.069 ms. This is 75.8% fewer
allocations and over 244x conservative-endpoint throughput.

The overflow-equation workload extends the same four-symbol model to twelve
coupled ground-target equations. Equation storage grows only after the eight
inline slots are exhausted, while conjunct storage similarly remains inline
through sixteen entries. The previously gated two- and eight-equation paths
remain at 8 and 15 allocations respectively. The twelve-equation workload uses
20 allocations and 15.280–15.290 us versus pinned Z3's 84 visible Go
allocations and 3.035–3.130 ms. This is 76.2% fewer allocations and over 198x
conservative-endpoint throughput.

The overflow-constraint workload combines two shared word equations with five
distinct exact symbol-length constraints and five regex memberships, crossing
both former four-entry family ceilings while extracting five string values and
validating the whole formula. Length evaluation now counts SMT code points
without allocating rune slices. The cold workload uses 28 allocations and
13.801–13.824 us versus pinned Z3's 60 visible Go allocations and
1.403–1.527 ms. This is 53.3% fewer allocations and over 101x
conservative-endpoint throughput. Separate semantic and 64-case differential
tests exercise five nontrivial regexes and five general string predicates
together.

The regex-coupled workload solves `x ++ y = "abc"` while requiring
`x` to belong to the union of the singleton languages `"a"` and `"ab"`.
Membership is checked while assigning candidate splits, so the initial empty
split is rejected inside the same bounded search. It uses 9 allocations and
4.177–4.193 us versus pinned Z3's 29 visible Go allocations and
1.270–1.360 ms. This is 69.0% fewer allocations and over 302x
conservative-endpoint throughput.

The Boolean-regex-coupled workload selects between two non-singleton range
membership atoms over `x`; only the second permits the split `x = "a"`.
General Boolean evaluation occurs before accepting an equation model, so a
false candidate resumes the bounded search. It uses 13 allocations and
5.504–5.516 us versus pinned Z3's 32 visible Go allocations and
1.423–1.496 ms. This is 59.4% fewer allocations and over 257x
conservative-endpoint throughput.

The string-disequality workload solves `x ++ y = "ab"` while requiring
`x != ""`. Global predicate validation rejects the canonical empty split and
continues to `x = "a"`, `y = "b"`. It uses 9 allocations and
4.513–4.560 us versus pinned Z3's 25 visible Go allocations and
1.289–1.354 ms. This is 64.0% fewer allocations and over 282x
conservative-endpoint throughput.

The string-predicate workload solves `x ++ y = "abc"` while requiring
`contains(x,"b")` and `prefixof("a",x)`, forcing `x = "ab"` and `y = "c"`.
Compact public relations remain value-resident and participate in terminal
global-model validation. It uses 13 allocations and 6.425–6.457 us versus
pinned Z3's 26 visible Go allocations and 1.852–1.916 ms. This is exactly
50.0% fewer allocations and over 286x conservative-endpoint throughput.

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
