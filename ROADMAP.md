# Roadmap

1. Typed hash-consed AST, symbols, contexts, immutable snapshots, diagnostics.
2. CDCL SAT with watched literals, VSIDS, restarts, clause learning, cores.
3. Congruence closure and Nelson–Oppen theory combination.
4. Exact rationals plus simplex/cuts for LRA/LIA and difference logic. LRA,
   difference logic, branch-and-bound QF_LIA, and bounded Boolean-QF_LIA
   foundations plus nonzero constant-divisor Euclidean div/mod are
   implemented; cutting planes and full shared-theory exchange remain.
5. Bit-blasting, arrays, algebraic datatypes, strings/sequences, floating point.
   Finite enumerations plus arbitrary-arity same-sort recursive datatypes with
   arity-indexed Go+ constructor vectors, bounded selector proofs,
   recognizers, graph acyclicity, exact n-ary models, and SMT-LIB execution are
   implemented. Mixed-sort Bool/Int/Real/bit-vector/Self fields, scalar product
   constructors, sort-refining selector cursors, exact models, context-indexed
   GoSMT construction, and SMT-LIB execution are implemented. Target-indexed
   cross-declaration references, productive mutually recursive groups,
   cross-sort acyclicity/models, and SMT-LIB `declare-datatypes` are
   implemented. Unary `par` families now monomorphize lazily into distinct
   concrete identities across scalar, datatype, and nested parametric
   arguments; qualified constructors, indexed recognizers, exact scalar
   selector models, exhaustive Bool/Int/Real/bit-vector/datatype `match` for
   both constructor-determined and unconstrained terms, and
   typed/SMT-LIB `update-field` agree with pinned Z3. Updates rebuild the
   selector's owning constructor, preserve every other constructor, work from
   symbolic recognizer evidence, and retain exact models. Multi-parameter
   families support identity-distinct instantiations, regular recursion, and
   nested substituted fields. Mutually parametric groups monomorphize jointly
   across cross-family cycles, including families with different arities, and
   validate group productivity before installation. Boolean QF_DT supports
   disjunction, implication, equivalence, Boolean equality/ITE, nested
   negation, and `distinct`, with an explicit bounded-expansion limit.
   Strings now include exact ground regular-language membership with
   literal/range/empty/full/all-character languages, Boolean language
   operations, closure, optionality, and indexed exact/bounded repetition.
   Constructive symbolic membership now synthesizes shortest witnesses for
   the literal/range/concat/union/closure/bounded-loop fragment, and
   equality-forced symbols produce exact contradiction proofs. Conjunctive
   positive/negative memberships now synthesize a shared witness, and
   incompatible singleton intersections are proved unsatisfiable. Bounded
   non-conjunctive Boolean regex formulas now select exact models, and
   literal-prefix/suffix equations with one unbound string symbol construct
   their exact middle value. Up to four distinct symbols separated by unique
   nonempty literal delimiters also receive exact constructive models,
   including interaction with additional equalities. Standalone bounded
   equations with adjacent symbols or multiply occurring delimiters select a
   deterministic shortest-first canonical model without treating that choice
   as forced during conjunction propagation. Bounded exhaustive search now
   covers repeated symbols and every Unicode-boundary split under an explicit
   4,096-state limit. Ambiguous bounded equations now combine exactly with
   ground assignments, including alternative-split models and contradiction
   proofs. Exact symbol-length equalities now prune that search by Unicode
   code-point length, construct satisfying splits, and prove impossible
   lengths contradictory. Unbounded/general Boolean regex constraints and
   lower/upper string-length inequalities now merge independently of assertion
   order and prune the same Unicode-boundary search. Unbounded/general Boolean
   regex constraints remain. Arbitrary-count bounded ground-target equation
   systems now share one globally backtracked model and resource limit,
   retaining fixed inline storage through eight equations and sixteen
   conjuncts before exact overflow. Alternative splits forced by later
   equations are revisited. Length, regular-language, and general string
   predicate families also retain four inline entries before exact overflow.
   One-symbol prefix/suffix concatenations lower directly into shared word
   equations in the GoSMT façade. Relational string lengths (`=`, `<`, `<=`)
   now compare bound string expressions exactly, including within Boolean
   choices, using compact std terms. Affine length arithmetic now covers exact
   addition, subtraction, and arbitrary-precision constant scaling against
   affine or constant bounds. Integer predicates over `str.indexof`,
   `str.to_int`, and `str.to_code`, including affine combinations, now
   participate in the same exact candidate validation. `str.indexof` scans
   Unicode/WTF-8 code-point boundaries without temporary rune slices.
   Derived-string equalities over `str.at`, `str.substr`, `str.replace`,
   `str.replace_all`, `str.from_int`, and `str.from_code` now validate the
   same globally backtracked candidates. `str.at` and `str.substr` share the
   allocation-free boundary scanner while preserving malformed-input fallback.
   Unbounded-target or unbounded Boolean-regex
   equation systems remain. Positive and negative
   regular-language memberships now prune bounded equation candidates and
   participate in final global-model validation; bounded `or`, nested `not`,
   implication, equivalence, Boolean equality, and ITE predicates backtrack
   over alternative equation splits. String equality/disequality predicates
   and Boolean choices over them participate in the same global validation,
   as do contains, prefix, suffix, and digit predicates.
   Ground `Seq Int` now evaluates exact empty/unit/concatenated values,
   equality/disequality, length arithmetic, and Boolean combinations. The
   first eight values remain inline in std and in the context-indexed GoSMT
   façade before exact overflow. Indexed `at`/extract, contains, prefix,
   suffix, index-of, and first replacement share that evaluator, including
   empty-sequence and out-of-range semantics. Generic sequence symbols and
   exact integer-sequence model storage now support ground assignments,
   conflicting-assignment proofs, derived operators, and temporary
   assumptions. Positive conjunctive contains/prefix/suffix requirements now
   construct deterministic witnesses for multiple symbols, merge compatible
   boundaries, and prove incompatible boundaries unsatisfiable.
   Exact ground lengths now use bounded complete containment placement,
   prefix/suffix overlap, deterministic zero filling, and exact
   negative/conflicting/too-short proofs. Non-conjunctive, multi-symbol-length,
   and non-integer symbolic sequence solving remain. Ground strict/non-strict
   lower and upper length bounds now search admissible lengths with shared
   placement resources and prove contradictory bounds independently of
   assertion order.
   Single-symbol affine length expressions now normalize exact addition,
   subtraction, and arbitrary-precision constant scaling with divisibility,
   sign reversal, integer rounding, and cancellation.
6. Quantifiers, E-matching, MBQI, nonlinear arithmetic, transcendental bounds.
7. SMT-LIB 2.7 commands, models, proofs, cores, options, statistics.
8. Tactics/probes, Optimize/MaxSMT, fixedpoint/Horn clauses, portfolio solving.
9. Z3 differential farm, SMT-COMP corpus, proof/model validation, fuzz/race.
10. Per-family 2× throughput and 50% allocation reductions, independent consumer,
    versioned GoForge/pkg.go.dev release.

Performance is gated separately for construction, simplification, SAT, each
theory, incremental traces, parsing, model extraction, and optimization. No
aggregate score can compensate for a workload family below either target.
