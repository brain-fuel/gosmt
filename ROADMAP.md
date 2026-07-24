# Roadmap

1. Typed hash-consed AST, symbols, contexts, immutable snapshots, diagnostics.
2. CDCL SAT with watched literals, VSIDS, restarts, clause learning, cores.
3. Congruence closure and Nelson–Oppen theory combination.
4. Exact rationals plus simplex/cuts for LRA/LIA and difference logic. LRA,
   difference logic, branch-and-bound QF_LIA, and bounded Boolean-QF_LIA
   foundations plus nonzero constant-divisor Euclidean div/mod are
   implemented. Exact arbitrary-precision ground `to_real`, floor-correct
   `to_int`, and `is_int` are implemented in typed and SMT-LIB surfaces;
   symbolic mixed LIA/LRA coercions, cutting planes, and full shared-theory
   exchange remain.
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
   negative/conflicting/too-short proofs. Bounded positive Boolean `and`/`or`
   formulas now expand nested symbolic integer-sequence disjunctions under a
   4,096-branch limit, try alternatives left to right, validate exact models,
   and prove all-unsatisfiable alternatives. Polarity-aware normalization now
   covers nested negation, implication, equivalence, and Boolean `if`; negated
   affine length equality and order lower to exact positive relations.
   Finite ground-value disequalities now participate in constructive witness
   search, discriminate free elements, backtrack fully fixed containment
   placements, and prove exhaustive conflicts under the same resource bound.
   Negated ground contains/prefix/suffix constraints now fill free positions
   with an integer absent from every forbidden pattern, backtrack fixed
   violations through positive placements and lengths, and prove empty-pattern
   contradictions. Pairwise symbolic sequence disequality now orders candidate
   roots, excludes prior neighbor models inside single/global affine search,
   and backtracks coupled lengths when a current assignment cannot be made
   distinct. Negated contains/prefix/suffix predicates with a symbolic pattern
   now require a nonempty pattern, prefer dependency order through independent
   and affine construction, support assigned targets with exact pattern-side
   requirements, and validate final models. Cyclic dependency graphs are exact:
   whichever root is built later receives both value-side and pattern-side
   constraints against earlier models. Affine systems retain sixteen roots
   inline, then continue through exact overflow normalization, dynamic global
   search, and atomic models under the 4,096-resource contract. Non-integer
   symbolic sequence solving remains. Ground strict/non-strict
   lower and upper length bounds now search admissible lengths with shared
   placement resources and prove contradictory bounds independently of
   assertion order.
   Standalone direct-symbol `str.replace_all` equalities with ground operands
   now invert every finite nonempty-replacement target parse, compose with
   same-symbol indexed and general string predicates, and preserve explicit
   resource-limit outcomes. Empty replacement now uses a finite-state
   leftmost deletion transducer for complete standalone shortest witnesses and
   impossibility proofs. Forced ground values validate directly, and bounded
   breadth-first cyclic-path enumeration lets length and general predicates
   select longer deletion preimages.
   Core code-point lexicographic `str.<` and `str.<=` now have typed std and
   context-indexed GoSMT terms, chainable SMT-LIB execution, allocation-free
   Unicode/WTF-8 comparison, compact symbolic witnesses, literal interval
   contradiction proofs, and strict-cycle detection across mixed strict and
   non-strict relations.
   Indexed SMT-LIB singleton constants `(_ char #xH)` now validate the exact
   one-to-five-digit hexadecimal grammar and 0..0x2ffff domain, backed by
   checked solver-neutral std and context-indexed GoSMT constructors.
   Unary Int→Int, binary Int×Int→Int, and ternary Int×Int×Int→Int
   uninterpreted functions now retain
   built-in sorts in std and solver context in Go+, execute through SMT-LIB,
   purify applications in affine arithmetic, and exchange EUF/LIA equality to
   a fixed point. Reciprocal inequalities, affine arguments, reverse
   propagation, compact direct-symbol paths, and exact integer-valued
   conditionals around unary applications are covered. Arity above three,
   other mixed signatures, and nonlinear arithmetic remain. Unary Int→Bool
   and binary Int×Int→Bool predicates now
   preserve their mixed signatures in Go+, accept affine arguments, execute
   through SMT-LIB, and share fixed-point LIA/EUF congruence.
   Unary Real→Bool and binary Real×Real→Bool predicates preserve their mixed
   signatures in Go+, accept affine arguments, execute through SMT-LIB, and
   share fixed-point LRA/EUF congruence.
   Ternary Real×Real×Real→Real functions now retain their arity/context in
   Go+, purify affine arguments, execute through SMT-LIB, and share the same
   fixed-point LRA/EUF congruence.
   Single-symbol affine length expressions now normalize exact addition,
   subtraction, and arbitrary-precision constant scaling with divisibility,
   sign reversal, integer rounding, and cancellation.
   Positive sequence-symbol equalities now canonicalize compact equality
   classes, merge constructive and length requirements, propagate exact models
   to every alias, and prove conflicting assignments unsatisfiable.
   Exact two-symbol affine length equations now jointly search one bounded
   length, derive the partner by exact division, build both local witnesses,
   and commit paired models atomically. Multi-symbol inequalities remain.
   Exact three-symbol affine equations now recursively search the first two
   constructively pruned length ranges, derive the third by exact division,
   canonicalize aliases, prove coefficient-GCD divisibility contradictions,
   and atomically commit all three witnesses.
   One strict or non-strict affine inequality across two or three canonical
   lengths now uses sign-correct integer bounds, minimum-feasibility pruning,
   and exact witness construction after equality relations.
   Multiple affine equalities and inequalities over up to sixteen canonical
   roots now use one bounded global search, interval feasibility pruning,
   equality interval contradiction proofs, final-bound intersection, and
   atomic witness commitment. Normalization, aliases, requirements, candidates,
   and exact models share the sixteen-root inline capacity. Larger systems use
   exact overflow relations and dynamically sized global-search vectors under
   the same 4,096-resource boundary.
6. Quantifiers, E-matching, MBQI, nonlinear arithmetic, transcendental bounds.
7. SMT-LIB 2.7 commands, models, proofs, cores, options, statistics.
8. Tactics/probes, Optimize/MaxSMT, fixedpoint/Horn clauses, portfolio solving.
9. Z3 differential farm, SMT-COMP corpus, proof/model validation, fuzz/race.
10. Per-family 2× throughput and 50% allocation reductions, independent consumer,
    versioned GoForge/pkg.go.dev release.

Performance is gated separately for construction, simplification, SAT, each
theory, incremental traces, parsing, model extraction, and optimization. No
aggregate score can compensate for a workload family below either target.
