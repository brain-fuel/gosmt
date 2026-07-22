# Z3 4.16.0 compatibility matrix

Pinned source: `Z3Prover/z3` tag `z3-4.16.0`, commit
`ddb49568d3520e99799e364fb22f35fc67d887b1`, MIT.

| Surface | Status | Differential family |
|---|---|---|
| Sorted Boolean terms and models | foundation: Tseitin CNF, scanning DPLL for small formulas, watched first-UIP CDCL with learned clauses, backjumping, activity branching, and geometric restarts for scaled formulas | truth tables, randomized CNF, models, and pinned-Z3 pigeonhole corpus |
| Incremental assert/push/restore | foundation: immutable scopes | incremental QF_BOOL traces |
| Temporary assumptions and unsat cores | foundation: deletion-minimized cores | assumption/core corpus |
| SMT-LIB 2 syntax/parser/printer | foundation: spans, core commands, lossless raw commands, Z3 format oracle | SMT-COMP scripts and round trips |
| SMT-LIB command execution | foundation: declarations, assertions, push/pop, assumptions, checks, models and values for QF_BOOL/QF_IDL/QF_LRA plus ground QF_UF | incremental Boolean, IDL, exact-LRA, assumption, and ground-EUF traces agree with pinned Z3 |
| EUF | foundation: typed uninterpreted sorts, unary and binary functions with indexed argument/result sorts, nested ground conjunctive equality/disequality, congruence closure | pinned-Z3 satisfiable/non-injective and unary/binary unsatisfiable congruence cases; compile-time rejection of an incorrect binary argument sort |
| Integer difference logic | foundation: inline-small/arbitrary-precision integer values, exact arbitrary-width graph weights and models, strict bounds, negative cycles, compatibility `int64` projection, and exact GoSMT/SMT-LIB model values | QF_IDL, explicit 101-bit bounds, and 64 deterministic wide-integer systems agree with pinned Z3 |
| Exact linear real arithmetic | foundation: arbitrary-precision rationals, unrestricted variables, exact simplex models, and symbolic strict-inequality slack | explicit fractional/tiny-strict cases and 100 deterministic random QF_LRA systems agree with pinned Z3 |
| Disjoint theory combination | foundation: complete conjunctive direct product of typed EUF, QF_IDL, and QF_LRA signatures with merged arithmetic models | mixed incremental EUF+LRA trace agrees with pinned Z3; EUF-unsat propagation and simultaneous integer/real models are covered |
| Shared QF_UFLRA equality exchange and purification | foundation: indexed unary Real→Real and binary Real×Real→Real functions, collision-free purification inside linear arithmetic, exact defining equalities for linear arguments, convex LRA-to-EUF entailment, and EUF-to-LRA equality propagation to a fixed point | direct, nested-argument, binary-affine, transitive-simplex, reverse-propagation, satisfiable-disequality, randomized SMT-LIB, compile-rejection, and pinned-Z3 cases |
| General linear integer arithmetic | planned | QF_LIA |
| Bit-vectors and ground QF_UFBV | foundation: arbitrary positive widths indexed in Go+ types; exact literals and symbols; equality/disequality; NOT/AND/OR/XOR; modular addition/subtraction/multiplication; UDIV/UREM/SDIV/SREM including zero divisors; full SHL/LSHR/ASHR semantics; indexed rotate-left/rotate-right/repeat; unsigned/signed add/subtract/multiply overflow plus signed-divide and negate overflow predicates; signed and unsigned `<`/`<=`; computed-width concat/extract/zero/sign extension; exact unsigned/signed BV-to-Int and indexed modulo Int-to-BV conversion; indexed unary and binary bit-vector uninterpreted functions with nested congruence, non-injective models, general SAT coupling, and compact symbolic contradiction closure | width, conversion-result, structural-result, repeat-product, and function-domain compile rejection; masking, wraparound, ordering, product, division, shift, rotation, repetition, overflow, conversion, layout, unary/binary/nested congruence, and model laws; 130-bit values; 640 deterministic pinned-Z3 cases; SMT-LIB QF_BV/QF_UFBV; and ten official-API performance gates |
| Arrays | foundation: sort-indexed `Array[I,E]`, symbols, constant arrays, `select`, `store`, sound ground read-over-write normalization, equality-driven select congruence, symbolic integer- and bit-vector-index equivalence, finite integer- and bit-vector-array models, extensional witnesses, store-chain extensionality with overwrite normalization and commuting updates, exception-aware cross-base integer equality, exact symbolic-to-constant integer defaults, disjoint array/IDL/BV products, and IDL/BV-implied shared-index equality exchange; width-indexed GoSMT bit-vector-array façade; SMT-LIB `(Array Int Int)` and QF_AUFBV execution/model values | cross-package index/element sort rejection; direct and nested store/select laws; 768 deterministic array, mixed QF_AUFLIA, and QF_AUFBV cases agree with pinned Z3; twelve official-API cold performance gates |
| Datatypes and sequences/strings | planned | QF_DT, QF_S, QF_SLIA |
| Floating point | planned | QF_FP, QF_FPBV |
| Nonlinear arithmetic | planned | QF_NIA, QF_NRA |
| Quantifiers and E-matching | planned | quantified SMT-LIB corpus |
| Optimization | planned | Optimize/MaxSMT/Pareto/Lex corpus |
| Tactics, goals, probes | planned | Z3 tactic behavior corpus |
| Fixedpoint/Horn clauses | planned | HORN/Datalog corpus |
| Proof objects and interpolation | planned | proof-check/interpolation corpus |
| C/Python/.NET/Java API parity | out of Go API scope | SMT-LIB is wire boundary |

“Foundation” means implemented and tested, not Z3-complete. A theory advances
only with syntax, sort checking, model validation, differential outcomes, fuzz
coverage, incremental behavior, and per-family performance/allocation gates.
Shared exchange currently covers unary Real→Real and binary Real×Real→Real
applications in EUF atoms and linear arithmetic, including non-symbol linear
arguments through exact defining equalities. Int-sorted functions, arity above
two, mixed built-in signatures, conditionals around applications, and
nonlinear arithmetic remain outside this foundation and must not be inferred
from it.

The array foundation now combines disjoint array, IDL, bit-vector, EUF, and
linear-real conjuncts, and exchanges IDL- or BV-entailed equality between
shared integer or bit-vector indices. General non-difference LIA exchange and
symbolic bit-vector array models remain outside this foundation. Finite store chains support exact and symbolic integer indices, overwrite elimination,
commuting distinct updates, extensional disequality groups, equality across
distinct symbolic bases, and symbolic-to-constant equality. Cross-base bridges
equate every observed unmodified index without equating overwritten base cells.
Constant bridges constrain the true unobserved default and detect incompatible
default equations. Ground integer-array symbols have finite model
interpretations, observed read assignments, store overlays, and disequality
witnesses.
The BV/Int bridge currently solves conversion against exact integer constants,
constant modulo conversion, and BV-to-Int-to-BV round trips. General symbolic
BV/Int arithmetic coupling remains explicit `unknown`. Arrays, floating point,
quantifiers, optimization, tactics, and the remaining cross-theory operators
remain planned.
