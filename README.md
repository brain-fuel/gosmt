# GoSMT

GoSMT is a native Go+/Go SMT solver and compatibility project pinned against
Microsoft Z3 4.16.0 (`ddb49568d3520e99799e364fb22f35fc67d887b1`, MIT).
It does not bind to Z3: differential tests use Z3 as an oracle while released
artifacts remain pure generated Go.

Ground floating-point values retain their context, exponent width, and
significand width as Go+ indices. Exact IEEE/SMT-LIB bit-pattern construction
and round trips cover arbitrary valid formats, with NaN, infinity, zero,
subnormal, normal, positive, and negative classification plus exact `fp.eq`
semantics for NaNs and signed zeros. This is deliberately a ground foundation:
symbolic FP terms, rounding modes, arithmetic, conversions, SMT-LIB execution,
and QF_FP/QF_FPBV solving remain future work.

The essential, solver-neutral surface lives in `goforge.dev/goplus/std/smt`:
sorted terms, exhaustive results, context-indexed models and proofs, checked
incremental scopes, temporary assumptions, minimized unsat cores, and native
Boolean, integer-difference, general exact-linear-integer, exact-linear-real,
and typed unary/binary EUF
solving, including finite, arbitrary-arity same-sort, mixed-sort, mutually
recursive, unary/multi-parameter, and mutually parametric algebraic datatypes
with exhaustive
Bool/Int/Real/bit-vector/datatype pattern matching—including constructor
selection from branch constraints—and typed field updates, plus Euclidean integer
division/modulo by nonzero constants,
plus bounded complete Boolean QF_DT branching and sound conjunctive
combination while those signatures remain
disjoint and fixed-point shared equality exchange for unary/binary Real and
integer EUF.
Built-in integer EUF includes context-indexed unary `Int -> Int`, binary
`Int × Int -> Int`, and ternary `Int × Int × Int -> Int` declarations. The
typed API and SMT-LIB `QF_UFLIA` purify
applications inside affine arithmetic and exchange implied equality between
LIA and EUF to a fixed point, including affine arguments. Compact direct-symbol
paths avoid materializing application trees. Unary `Int -> Bool` and binary
`Int × Int -> Bool` predicates use the same context indices, affine argument
purification, and LIA-driven congruence.
Integer-valued `IfInt` terms preserve exact branch semantics around unary EUF
applications in the typed API and SMT-LIB `ite`. A compact conditional system
keeps the common QF_UFLIA path allocation-safe while the general solver uses
exact guarded case splitting.
Unary `Real -> Bool` and binary `Real × Real -> Bool` predicates retain their
mixed signatures and context identity in Go+, accept affine arguments, and
share exact LRA/EUF equality exchange.
Ternary `Real × Real × Real -> Real` functions likewise retain context and
arity indices, purify affine arguments, aggregate exact rational bounds, and
participate in fixed-point QF_UFLRA congruence.
Ground `Int`/`Real` coercions are exact and arbitrary precision: `ToReal`
preserves every integer, `ToIntReal` implements SMT-LIB floor semantics, and
`IsIntReal` decides exact integrality. Their Go+ façade retains the context
index. Symbolic `to_real` is exact when direct coerced integer terms are
compared with another coerced integer or an exact rational constant, including
floor/ceiling normalization of fractional bounds. Exact rational scaling of a
supported affine coerced integer is also normalized:
`to_int((p/q)*(to_real(x)+r))` becomes Euclidean division over one exact affine
integer numerator, and `is_int` becomes its zero-remainder condition, including
negative coefficients, rational offsets, one- and two-symbol affine integer
terms, and floor behavior. Other symbolic mixed expressions deliberately
remain `unknown` until broader mixed LIA/LRA integrality solving is complete.
Exact symbolic round trips normalize before solving:
`ToIntReal(ToReal(x))` is `x`, and `IsIntReal(ToReal(x))` is true for every
integer expression. Reflexive integer equality and constant Boolean
disjunctions likewise fold in the façade.
Affine expressions built from coerced integers, exact rational offsets,
addition/subtraction, and integral scaling also normalize exactly:
`to_int(n+r)` becomes `n+floor(r)`, while `is_int(n+r)` depends only on the
exact offset. `AndPair` provides a context-indexed, allocation-free
short-circuit path for two Boolean expressions.
Equality and ordering between two such affine expressions lower to integer
relations with an exact rational residual bound. Fractional equality becomes
false, while strict and non-strict order use the correct integer rounding.
Strings include exact ground regular-language membership, constructive
symbolic, shared-conjunction, and bounded non-conjunctive witnesses,
equality-forced and singleton-intersection contradiction proofs, constructive
single-unknown, uniquely delimited, adjacent-symbol, repeated-symbol, and
canonically split bounded word equations with exact ground-equality
and code-point-length equality/inequality interaction, plus globally
backtracked shared-symbol systems with inline storage through eight equations
and exact overflow under a shared resource limit. Length, regex, and general
string-predicate constraints likewise remain inline through four entries per
family before exact overflow. The façade recognizes one-symbol
prefix/suffix equations directly. Compact relational length terms preserve
`len(x) = len(y)`, `<`, and `<=` without generic AST materialization, including
Boolean-nested constraints during bounded backtracking. Affine combinations
of lengths support exact addition, subtraction, and constant scaling, plus
integer-valued `str.indexof`, `str.to_int`, and `str.to_code` predicates
coupled to word-equation candidates with exact arbitrary-precision conversion,
and derived-string equalities over `str.at`, `str.substr`, `str.replace`,
`str.replace_all`, `str.from_int`, and `str.from_code`. Indexed extraction
uses allocation-free Unicode/WTF-8 boundary scans on valid SMT strings.
Direct-symbol `str.at` and `str.substr` equalities with ground indices and
results additionally solve without a bounding word equation: overlapping
requirements reduce exactly to code-point placements and lower/upper length
bounds, with canonical models and contradiction proofs. The GoSMT façade
retains these as compact indexed equalities until std solving. Direct-symbol
first-replacement equalities with ground source, replacement, and target also
solve standalone. Std enumerates the complete finite preimage, including
unchanged, empty-source, empty-replacement, ambiguous, Unicode, and
multi-constraint intersection cases; the façade retains a compact replacement
equality. The same exhaustive candidates compose exactly with direct-symbol
ground-index `str.at` and `str.substr` constraints, selecting a compatible
preimage or proving that every preimage fails. They also filter through the
bounded same-symbol string predicate language: equality/disequality,
contains/prefix/suffix/digit/regex, length/index/conversion arithmetic, and
supported Boolean composition. Predicates owning another unbound symbol
remain `unknown`. Direct-symbol all-replacement equalities now also solve
standalone when source, replacement, and target are ground and the replacement
is nonempty. Std enumerates every target parse into literal output and replaced
source occurrences, validates candidates without allocating replacement
strings, and shares the same indexed/predicate filtering and 4,096-state
contract. Empty source retains SMT-LIB identity semantics. Empty replacement
uses an exact finite-state deletion transducer to construct the shortest
standalone preimage or prove that none exists. Direct ground equalities force
one candidate immediately, while other secondary predicates breadth-first
enumerate distinct cyclic transducer paths under the shared 4,096-node limit;
unexplored paths remain explicit `unknown`. Regex-coupled
candidate selection includes bounded Boolean predicates and string
disequalities, the core SMT-LIB regex, globally backtracked
contains/prefix/suffix constraints, and context-indexed GoSMT construction.
The standard library keeps
regexes element-sort indexed and small Boolean-regex formulas in an inline
postfix representation. Core SMT-LIB lexicographic `str.<` and reflexive
`str.<=` compare Unicode code points without decoded-slice allocations.
Compact direct-symbol systems construct ordered models, merge literal
lower/upper bounds, and prove reflexive, boundary, strict-cycle, and mixed
strict/non-strict cycle contradictions. Checked std and context-indexed GoSMT
character constructors cover the complete SMT-LIB 0..0x2ffff domain, while
the executor validates and evaluates indexed `(_ char #xH)` constants.
Ground integer sequences now have exact `empty`, `unit`, `concat`, equality,
disequality, length arithmetic, indexed `at`/extract, contains/prefix/suffix,
index-of, first replacement, Boolean composition, and inline model evaluation.
Go+ retains both the sequence element sort in std and the context identity in
the GoSMT façade. Ground-assigned symbolic sequence constants retain exact
model values across derived operators and assumptions. Positive conjunctive
`contains`, `prefix`, and `suffix` constraints construct deterministic exact
witnesses, merge compatible prefix/suffix requirements, and reject conflicts.
Exact ground length constraints add bounded placement/backtracking, overlapping
prefix/suffix models, zero-filled unconstrained positions, and exact
negative/conflicting/too-short proofs. Bounded positive Boolean `and`/`or`
formulas over symbolic integer-sequence constraints expand nested disjunctions
under a 4,096-branch limit, try alternatives left to right, validate exact
models, and prove all-unsatisfiable alternatives. Polarity-aware normalization
extends that bounded fragment through nested negation, implication,
equivalence, and Boolean `if`; negated affine length equality and order become
exact positive relations before constructive solving. Symbolic integer
sequences also support finite ground-value disequality: exact exclusions share
the placement search, discriminate free elements, backtrack fixed containment
placements, and prove exhaustive conflicts under the same 4,096-resource
contract. Negated ground `contains`, `prefix`, and `suffix` constraints use a
fresh integer absent from every forbidden pattern for unconstrained positions;
fixed violations backtrack through positive containment placements and length
choices, while empty-pattern contradictions are exact. Disequality between two
symbolic sequence roots is also constructive: ordered candidate building
excludes every earlier neighbor model inside single- and multi-relation affine
search, so fully constrained equality backtracks to another length assignment.
Negated `contains`, `prefix`, and `suffix` also accept a distinct symbolic
pattern root. Patterns are nonempty, affine candidates prefer dependency
order, and the later root receives both value-side and pattern-side exact
constraints against every earlier model. This also closes cyclic dependency
graphs without approximating them; assigned targets and final model validation
use the same bidirectional representation. Affine systems keep sixteen roots
inline and continue through exact overflow storage and dynamic global search
under the shared 4,096-resource contract. Symbolic-element sequence search
remains explicit future work.
Ground strict
and non-strict length bounds now normalize into exact lower/upper requirements,
search admissible lengths with the same placement engine, and prove
order-independent bound conflicts.
Single-symbol affine length expressions support exact addition, subtraction,
and arbitrary-precision constant scaling, including divisibility proofs,
coefficient-sign reversal, integer floor/ceiling bounds, and cancellation.
Positive sequence-symbol equalities now form compact equality classes.
Assignments, constructive constraints, lengths, assumptions, derived
evaluation, and exact models propagate across every alias; conflicting alias
assignments are unsatisfiable.
Exact affine equations across two distinct symbolic sequence lengths now use
bounded joint search, exact partner-length division, per-symbol constructive
requirements, alias canonicalization, and atomic paired model commitment.
The same exact normalization extends to three canonical sequence symbols:
constructive minima prune bounded recursive search, the final length is
derived by exact division, and all three witnesses commit atomically. A
coefficient-GCD divisibility check proves impossible affine systems before
bounded search.
Strict and non-strict affine inequalities across two or three canonical
sequence lengths use sign-correct integer bounds, constructive feasibility
pruning, and exact models. Equality relations are solved first regardless of
assertion order.
Multiple affine equalities and inequalities over as many as sixteen canonical
sequence roots now share one bounded global search. Partial interval proofs
prune infeasible branches, final exact values and inequality bounds intersect,
and all local witnesses commit atomically. Normalization, aliases,
requirements, candidate search, and exact models share the sixteen-root
capacity; equality interval pruning proves impossible totals before bounded
enumeration. Larger root sets retain those sixteen inline entries and continue
through exact overflow relations, requirements, candidates, and atomic models
up to the shared 4,096-resource boundary.
Function arguments and results retain Go+ sort indices. The
solver-neutral SMT-LIB syntax lives
in `goforge.dev/goplus/std/smtlib`. This module adds Z3-shaped contexts,
SMT-LIB execution, theories, tactics, optimization, fixedpoint, compatibility,
and portfolio engineering.

This repository is at foundation stage; see [COMPATIBILITY.md](COMPATIBILITY.md)
for the versioned scope and [ROADMAP.md](ROADMAP.md) for the non-negotiable path
to broad Z3 functionality. Unsupported theories return `unknown`; they are not
silently approximated.
