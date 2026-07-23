module goforge.dev/gosmt/benchmarks/z3api

go 1.26.0

require (
	github.com/Z3Prover/z3/src/api/go v0.0.0-20260218225751-ddb49568d352
	goforge.dev/gosmt v0.0.0
)

require goforge.dev/goplus/std v0.61.0

replace goforge.dev/goplus/std => ../../../goplus/std

replace goforge.dev/gosmt => ../..
