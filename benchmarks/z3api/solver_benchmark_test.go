package z3api

import (
	"testing"

	z3 "github.com/Z3Prover/z3/src/api/go"
	"goforge.dev/goplus/std/smt"
	"goforge.dev/gosmt"
)

func BenchmarkBooleanWarm(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		context := gosmt.NewContext(1)
		a := gosmt.BoolConst(context, "a", 1)
		other := gosmt.BoolConst(context, "b", 2)
		formula := gosmt.And(gosmt.Or(a, other), gosmt.Not(a))
		solver := gosmt.Assert(1, gosmt.NewSolver(context), formula)
		if _, ok := gosmt.Check(solver).(gosmt.Sat); !ok {
			b.Fatal("unexpected result")
		}
		b.ReportAllocs()
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if _, ok := gosmt.Check(solver).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		context := z3.NewContext()
		a := context.MkBoolConst("a")
		other := context.MkBoolConst("b")
		formula := context.MkAnd(context.MkOr(a, other), context.MkNot(a))
		solver := context.NewSolver()
		solver.Assert(formula)
		if solver.Check() != z3.Satisfiable {
			b.Fatal("unexpected result")
		}
		b.ReportAllocs()
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBooleanCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(1)
			a := gosmt.BoolConst(context, "a", 1)
			other := gosmt.BoolConst(context, "b", 2)
			formula := gosmt.And(gosmt.Or(a, other), gosmt.Not(a))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			a := context.MkBoolConst("a")
			other := context.MkBoolConst("b")
			formula := context.MkAnd(context.MkOr(a, other), context.MkNot(a))
			solver := context.NewSolver()
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkIntegerDifferenceWarm(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		context := gosmt.NewContext(2)
		x := gosmt.IntConst(context, "x", 1)
		y := gosmt.IntConst(context, "y", 2)
		formula := gosmt.And(
			gosmt.Le(gosmt.Sub(x, y), gosmt.IntVal(context, 3)),
			gosmt.Le(y, gosmt.IntVal(context, 2)),
			gosmt.Le(gosmt.IntVal(context, 4), x),
		)
		solver := gosmt.Assert(1, gosmt.NewSolver(context), formula)
		if _, ok := gosmt.Check(solver).(gosmt.Sat); !ok {
			b.Fatal("unexpected result")
		}
		b.ReportAllocs()
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if _, ok := gosmt.Check(solver).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		context := z3.NewContext()
		x := context.MkIntConst("x")
		y := context.MkIntConst("y")
		intSort := context.MkIntSort()
		formula := context.MkAnd(
			context.MkLe(context.MkSub(x, y), context.MkInt(3, intSort)),
			context.MkLe(y, context.MkInt(2, intSort)),
			context.MkLe(context.MkInt(4, intSort), x),
		)
		solver := context.NewSolverForLogic("QF_IDL")
		solver.Assert(formula)
		if solver.Check() != z3.Satisfiable {
			b.Fatal("unexpected result")
		}
		b.ReportAllocs()
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkIntegerDifferenceCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(2)
			x := gosmt.IntConst(context, "x", 1)
			y := gosmt.IntConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.Le(gosmt.Sub(x, y), gosmt.IntVal(context, 3)),
				gosmt.Le(y, gosmt.IntVal(context, 2)),
				gosmt.Le(gosmt.IntVal(context, 4), x),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkIntConst("x")
			y := context.MkIntConst("y")
			intSort := context.MkIntSort()
			formula := context.MkAnd(
				context.MkLe(context.MkSub(x, y), context.MkInt(3, intSort)),
				context.MkLe(y, context.MkInt(2, intSort)),
				context.MkLe(context.MkInt(4, intSort), x),
			)
			solver := context.NewSolverForLogic("QF_IDL")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkLinearRealWarm(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		context := gosmt.NewContext(6)
		x := gosmt.RealConst(context, "x", 1)
		y := gosmt.RealConst(context, "y", 2)
		formula := gosmt.And(
			gosmt.LeReal(gosmt.AddReal(x, y), gosmt.RealVal(context, gosmt.Rational(3, 1))),
			gosmt.LeReal(gosmt.RealVal(context, gosmt.Rational(1, 2)), x),
			gosmt.LtReal(gosmt.RealVal(context, gosmt.Rational(1, 3)), y),
		)
		solver := gosmt.Assert(1, gosmt.NewSolver(context), formula)
		if _, ok := gosmt.Check(solver).(gosmt.Sat); !ok {
			b.Fatal("unexpected result")
		}
		b.ReportAllocs()
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if _, ok := gosmt.Check(solver).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		context := z3.NewContext()
		x := context.MkRealConst("x")
		y := context.MkRealConst("y")
		solver := context.NewSolverForLogic("QF_LRA")
		solver.Assert(context.MkAnd(
			context.MkLe(context.MkAdd(x, y), context.MkReal(3, 1)),
			context.MkLe(context.MkReal(1, 2), x),
			context.MkLt(context.MkReal(1, 3), y),
		))
		if solver.Check() != z3.Satisfiable {
			b.Fatal("unexpected result")
		}
		b.ReportAllocs()
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkLinearRealCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(6)
			x := gosmt.RealConst(context, "x", 1)
			y := gosmt.RealConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.LeReal(gosmt.AddReal(x, y), gosmt.RealVal(context, gosmt.Rational(3, 1))),
				gosmt.LeReal(gosmt.RealVal(context, gosmt.Rational(1, 2)), x),
				gosmt.LtReal(gosmt.RealVal(context, gosmt.Rational(1, 3)), y),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkRealConst("x")
			y := context.MkRealConst("y")
			solver := context.NewSolverForLogic("QF_LRA")
			solver.Assert(context.MkAnd(
				context.MkLe(context.MkAdd(x, y), context.MkReal(3, 1)),
				context.MkLe(context.MkReal(1, 2), x),
				context.MkLt(context.MkReal(1, 3), y),
			))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundEUFCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(3)
			a := gosmt.UninterpretedConst(1, context, "a", 1)
			other := gosmt.UninterpretedConst(1, context, "b", 2)
			function := gosmt.DeclareUnary(1, 1, context, "f", 1)
			formula := gosmt.And(
				gosmt.EqUninterpreted(a, other),
				gosmt.Not(gosmt.EqUninterpreted(gosmt.ApplyUninterpreted(function, a), gosmt.ApplyUninterpreted(function, other))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			sort := context.MkTypeVariable(context.MkStringSymbol("U"))
			a := context.MkConst(context.MkStringSymbol("a"), sort)
			other := context.MkConst(context.MkStringSymbol("b"), sort)
			function := context.MkFuncDecl(context.MkStringSymbol("f"), []*z3.Sort{sort}, sort)
			formula := context.MkAnd(
				context.MkEq(a, other),
				context.MkNot(context.MkEq(context.MkApp(function, a), context.MkApp(function, other))),
			)
			solver := context.NewSolverForLogic("QF_UF")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundBinaryEUFCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(7)
			a := gosmt.UninterpretedConst(1, context, "a", 1)
			aPrime := gosmt.UninterpretedConst(1, context, "a2", 2)
			left := gosmt.UninterpretedConst(2, context, "b", 3)
			right := gosmt.UninterpretedConst(2, context, "b2", 4)
			function := gosmt.DeclareBinary(1, 2, 3, context, "combine", 5)
			formula := gosmt.And(
				gosmt.EqUninterpreted(a, aPrime),
				gosmt.EqUninterpreted(left, right),
				gosmt.Not(gosmt.EqUninterpreted(
					gosmt.ApplyBinaryUninterpreted(function, a, left),
					gosmt.ApplyBinaryUninterpreted(function, aPrime, right),
				)),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			firstSort := context.MkTypeVariable(context.MkStringSymbol("A"))
			secondSort := context.MkTypeVariable(context.MkStringSymbol("B"))
			rangeSort := context.MkTypeVariable(context.MkStringSymbol("R"))
			a := context.MkConst(context.MkStringSymbol("a"), firstSort)
			aPrime := context.MkConst(context.MkStringSymbol("a2"), firstSort)
			left := context.MkConst(context.MkStringSymbol("b"), secondSort)
			right := context.MkConst(context.MkStringSymbol("b2"), secondSort)
			function := context.MkFuncDecl(context.MkStringSymbol("combine"), []*z3.Sort{firstSort, secondSort}, rangeSort)
			formula := context.MkAnd(
				context.MkEq(a, aPrime),
				context.MkEq(left, right),
				context.MkNot(context.MkEq(context.MkApp(function, a, left), context.MkApp(function, aPrime, right))),
			)
			solver := context.NewSolverForLogic("QF_UF")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkDisjointEUFLinearRealCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(8)
			a := gosmt.UninterpretedConst(1, context, "a", 1)
			other := gosmt.UninterpretedConst(1, context, "b", 2)
			function := gosmt.DeclareUnary(1, 1, context, "f", 3)
			x := gosmt.RealConst(context, "x", 4)
			formula := gosmt.And(
				gosmt.Not(gosmt.EqUninterpreted(a, other)),
				gosmt.EqUninterpreted(gosmt.ApplyUninterpreted(function, a), gosmt.ApplyUninterpreted(function, other)),
				gosmt.LeReal(gosmt.RealVal(context, gosmt.Rational(1, 1)), x),
				gosmt.LeReal(x, gosmt.RealVal(context, gosmt.Rational(2, 1))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			sort := context.MkTypeVariable(context.MkStringSymbol("U"))
			a := context.MkConst(context.MkStringSymbol("a"), sort)
			other := context.MkConst(context.MkStringSymbol("b"), sort)
			function := context.MkFuncDecl(context.MkStringSymbol("f"), []*z3.Sort{sort}, sort)
			x := context.MkRealConst("x")
			formula := context.MkAnd(
				context.MkNot(context.MkEq(a, other)),
				context.MkEq(context.MkApp(function, a), context.MkApp(function, other)),
				context.MkLe(context.MkReal(1, 1), x),
				context.MkLe(x, context.MkReal(2, 1)),
			)
			solver := context.NewSolver()
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkSharedRealEUFCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(9)
			x := gosmt.RealConst(context, "x", 1)
			y := gosmt.RealConst(context, "y", 2)
			function := gosmt.DeclareRealFunction(context, "f", 3)
			formula := gosmt.And(
				gosmt.LeReal(x, y),
				gosmt.LeReal(y, x),
				gosmt.Not(gosmt.EqReal(gosmt.ApplyRealFunction(function, x), gosmt.ApplyRealFunction(function, y))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkRealConst("x")
			y := context.MkRealConst("y")
			realSort := context.MkRealSort()
			function := context.MkFuncDecl(context.MkStringSymbol("f"), []*z3.Sort{realSort}, realSort)
			formula := context.MkAnd(
				context.MkLe(x, y),
				context.MkLe(y, x),
				context.MkNot(context.MkEq(context.MkApp(function, x), context.MkApp(function, y))),
			)
			solver := context.NewSolverForLogic("QF_UFLRA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkPurifiedRealEUFArithmeticCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(10)
			x := gosmt.RealConst(context, "x", 1)
			y := gosmt.RealConst(context, "y", 2)
			zero := gosmt.RealVal(context, gosmt.Rational(0, 1))
			function := gosmt.DeclareRealFunction(context, "f", 3)
			formula := gosmt.And(
				gosmt.EqReal(x, y),
				gosmt.LeReal(gosmt.ApplyRealFunction(function, x), zero),
				gosmt.LtReal(zero, gosmt.ApplyRealFunction(function, y)),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkRealConst("x")
			y := context.MkRealConst("y")
			realSort := context.MkRealSort()
			function := context.MkFuncDecl(context.MkStringSymbol("f"), []*z3.Sort{realSort}, realSort)
			zero := context.MkReal(0, 1)
			formula := context.MkAnd(
				context.MkEq(x, y),
				context.MkLe(context.MkApp(function, x), zero),
				context.MkLt(zero, context.MkApp(function, y)),
			)
			solver := context.NewSolverForLogic("QF_UFLRA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkPurifiedBinaryRealEUFArithmeticCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(11)
			x := gosmt.RealConst(context, "x", 1)
			y := gosmt.RealConst(context, "y", 2)
			zero := gosmt.RealVal(context, gosmt.Rational(0, 1))
			function := gosmt.DeclareRealBinary(context, "combine", 3)
			formula := gosmt.And(
				gosmt.EqReal(x, y),
				gosmt.LeReal(gosmt.ApplyRealBinary(function, x, y), zero),
				gosmt.LtReal(zero, gosmt.ApplyRealBinary(function, y, x)),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkRealConst("x")
			y := context.MkRealConst("y")
			realSort := context.MkRealSort()
			function := context.MkFuncDecl(context.MkStringSymbol("combine"), []*z3.Sort{realSort, realSort}, realSort)
			zero := context.MkReal(0, 1)
			formula := context.MkAnd(
				context.MkEq(x, y),
				context.MkLe(context.MkApp(function, x, y), zero),
				context.MkLt(zero, context.MkApp(function, y, x)),
			)
			solver := context.NewSolverForLogic("QF_UFLRA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(12)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0xa5)),
				gosmt.Not(gosmt.EqBitVec(gosmt.AndBitVec(x, gosmt.BitVecValue(8, context, 0x0f)), gosmt.BitVecValue(8, context, 0x05))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			value := context.MkBV(0xa5, 8)
			mask := context.MkBV(0x0f, 8)
			expected := context.MkBV(0x05, 8)
			formula := context.MkAnd(context.MkEq(x, value), context.MkNot(context.MkEq(context.MkBVAnd(x, mask), expected)))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorOrderingCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(13)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0x7f)),
				gosmt.Not(gosmt.UltBitVec(x, gosmt.BitVecValue(8, context, 0x80))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			formula := context.MkAnd(context.MkEq(x, context.MkBV(0x7f, 8)), context.MkNot(context.MkBVULT(x, context.MkBV(0x80, 8))))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorToIntegerCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(21)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0xff)),
				gosmt.Not(gosmt.EqInt(gosmt.BvToNat(x), gosmt.IntVal(context, 255))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			maximum := context.MkBV(0xff, 8)
			// The pinned Go binding omits Z3_mk_bv2int. At this boundary,
			// ubv_to_int(x) = 255 is equivalent to x = #xff, so this keeps
			// the same contradiction while exercising Z3's public Go API.
			formula := context.MkAnd(context.MkEq(x, maximum), context.MkNot(context.MkEq(x, maximum)))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundIntegerArrayCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(32)
			array := gosmt.IntArrayConst(context, "a", 1)
			updated := gosmt.StoreIntArray(array, gosmt.IntVal(context, 7), gosmt.IntVal(context, 42))
			formula := gosmt.Not(gosmt.EqInt(gosmt.SelectIntArray(updated, gosmt.IntVal(context, 7)), gosmt.IntVal(context, 42)))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			array := context.MkConst(context.MkStringSymbol("a"), arraySort)
			index, value := context.MkInt(7, integerSort), context.MkInt(42, integerSort)
			formula := context.MkNot(context.MkEq(context.MkSelect(context.MkStore(array, index, value), index), value))
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundBitVectorArrayCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(33)
			array := gosmt.BitVecArrayConst(4, 8, context, "a", 1)
			index := gosmt.BitVecValue(4, context, 7)
			value := gosmt.BitVecValue(8, context, 42)
			updated := gosmt.StoreBitVecArray(array, index, value)
			formula := gosmt.Not(gosmt.EqBitVec(gosmt.SelectBitVecArray(updated, index), value))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			indexSort, elementSort := context.MkBvSort(4), context.MkBvSort(8)
			arraySort := context.MkArraySort(indexSort, elementSort)
			array := context.MkConst(context.MkStringSymbol("a"), arraySort)
			index, value := context.MkBV(7, 4), context.MkBV(42, 8)
			formula := context.MkNot(context.MkEq(context.MkSelect(context.MkStore(array, index, value), index), value))
			solver := context.NewSolverForLogic("QF_AUFBV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundBitVectorArraySymbolicIndexCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(34)
			array := gosmt.BitVecArrayConst(4, 8, context, "a", 1)
			left := gosmt.BitVecConst(4, context, "i", 2)
			right := gosmt.BitVecConst(4, context, "j", 3)
			value := gosmt.BitVecValue(8, context, 42)
			formula := gosmt.And(
				gosmt.EqBitVec(left, right),
				gosmt.Not(gosmt.EqBitVec(gosmt.SelectBitVecArray(gosmt.StoreBitVecArray(array, left, value), right), value)),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			indexSort, elementSort := context.MkBvSort(4), context.MkBvSort(8)
			arraySort := context.MkArraySort(indexSort, elementSort)
			array := context.MkConst(context.MkStringSymbol("a"), arraySort)
			left := context.MkBVConst("i", 4)
			right := context.MkBVConst("j", 4)
			value := context.MkBV(42, 8)
			formula := context.MkAnd(context.MkEq(left, right), context.MkNot(context.MkEq(context.MkSelect(context.MkStore(array, left, value), right), value)))
			solver := context.NewSolverForLogic("QF_AUFBV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundBitVectorArrayExtensionalModelCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(35)
			left := gosmt.BitVecArrayConst(4, 8, context, "a", 1)
			right := gosmt.BitVecArrayConst(4, 8, context, "b", 2)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), gosmt.Not(gosmt.EqBitVecArray(left, right)))).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			index := smt.NewBitVectorUint64(4, 0)
			leftValue, leftOK := gosmt.EvalBitVecArray(result.Value, left, index)
			rightValue, rightOK := gosmt.EvalBitVecArray(result.Value, right, index)
			if !leftOK || !rightOK || smt.EqualBitVectorValue(leftValue, rightValue) {
				b.Fatal("invalid model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			indexSort, elementSort := context.MkBvSort(4), context.MkBvSort(8)
			arraySort := context.MkArraySort(indexSort, elementSort)
			left := context.MkConst(context.MkStringSymbol("a"), arraySort)
			right := context.MkConst(context.MkStringSymbol("b"), arraySort)
			solver := context.NewSolverForLogic("QF_AUFBV")
			solver.Assert(context.MkNot(context.MkEq(left, right)))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			index := context.MkBV(0, 4)
			if _, ok := solver.Model().Eval(context.MkSelect(left, index), true); !ok {
				b.Fatal("invalid model")
			}
		}
	})
}

func BenchmarkGroundBitVectorArrayStoreExtensionalityCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(36)
			array := gosmt.BitVecArrayConst(4, 8, context, "a", 1)
			three, four := gosmt.BitVecValue(4, context, 3), gosmt.BitVecValue(4, context, 4)
			one, two := gosmt.BitVecValue(8, context, 1), gosmt.BitVecValue(8, context, 2)
			left := gosmt.StoreBitVecArray(gosmt.StoreBitVecArray(array, three, one), four, two)
			right := gosmt.StoreBitVecArray(gosmt.StoreBitVecArray(array, four, two), three, one)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), gosmt.Not(gosmt.EqBitVecArray(left, right)))).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			indexSort, elementSort := context.MkBvSort(4), context.MkBvSort(8)
			arraySort := context.MkArraySort(indexSort, elementSort)
			array := context.MkConst(context.MkStringSymbol("a"), arraySort)
			three, four := context.MkBV(3, 4), context.MkBV(4, 4)
			one, two := context.MkBV(1, 8), context.MkBV(2, 8)
			left := context.MkStore(context.MkStore(array, three, one), four, two)
			right := context.MkStore(context.MkStore(array, four, two), three, one)
			solver := context.NewSolverForLogic("QF_AUFBV")
			solver.Assert(context.MkNot(context.MkEq(left, right)))
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundIntegerArrayCongruenceCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(33)
			a := gosmt.IntArrayConst(context, "a", 1)
			other := gosmt.IntArrayConst(context, "b", 2)
			index := gosmt.IntVal(context, 7)
			formula := gosmt.And(gosmt.EqArray(a, other), gosmt.Not(gosmt.EqInt(gosmt.SelectIntArray(a, index), gosmt.SelectIntArray(other, index))))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			a := context.MkConst(context.MkStringSymbol("a"), arraySort)
			other := context.MkConst(context.MkStringSymbol("b"), arraySort)
			index := context.MkInt(7, integerSort)
			formula := context.MkAnd(context.MkEq(a, other), context.MkNot(context.MkEq(context.MkSelect(a, index), context.MkSelect(other, index))))
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundIntegerArraySymbolicIndexCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(34)
			array := gosmt.IntArrayConst(context, "a", 1)
			left := gosmt.IntConst(context, "i", 11)
			right := gosmt.IntConst(context, "j", 12)
			updated := gosmt.StoreIntArray(array, left, gosmt.IntVal(context, 42))
			formula := gosmt.And(gosmt.EqInt(left, right), gosmt.Not(gosmt.EqInt(gosmt.SelectIntArray(updated, right), gosmt.IntVal(context, 42))))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			array := context.MkConst(context.MkStringSymbol("a"), arraySort)
			left := context.MkIntConst("i")
			right := context.MkIntConst("j")
			value := context.MkInt(42, integerSort)
			formula := context.MkAnd(context.MkEq(left, right), context.MkNot(context.MkEq(context.MkSelect(context.MkStore(array, left, value), right), value)))
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundIntegerArrayExtensionalModelCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(35)
			a := gosmt.IntArrayConst(context, "a", 1)
			other := gosmt.IntArrayConst(context, "b", 2)
			index := gosmt.IntVal(context, 7)
			formula := gosmt.And(gosmt.Not(gosmt.EqArray(a, other)), gosmt.EqInt(gosmt.SelectIntArray(a, index), gosmt.IntVal(context, 42)))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalIntArray(result.Value, a, smt.NewIntegerValue(7)); !found || smt.CompareIntegerValue(value, smt.NewIntegerValue(42)) != 0 {
				b.Fatal("invalid model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			a := context.MkConst(context.MkStringSymbol("a"), arraySort)
			other := context.MkConst(context.MkStringSymbol("b"), arraySort)
			index, value := context.MkInt(7, integerSort), context.MkInt(42, integerSort)
			formula := context.MkAnd(context.MkNot(context.MkEq(a, other)), context.MkEq(context.MkSelect(a, index), value))
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(context.MkSelect(a, index), true); !ok {
				b.Fatal("invalid model")
			}
		}
	})
}

func BenchmarkGroundIntegerArrayStoreExtensionalityCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(36)
			a := gosmt.IntArrayConst(context, "a", 1)
			seven, eight := gosmt.IntVal(context, 7), gosmt.IntVal(context, 8)
			left := gosmt.StoreIntArray(gosmt.StoreIntArray(a, seven, gosmt.IntVal(context, 1)), eight, gosmt.IntVal(context, 2))
			right := gosmt.StoreIntArray(gosmt.StoreIntArray(a, eight, gosmt.IntVal(context, 2)), seven, gosmt.IntVal(context, 1))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), gosmt.Not(gosmt.EqArray(left, right)))).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			a := context.MkConst(context.MkStringSymbol("a"), arraySort)
			seven, eight := context.MkInt(7, integerSort), context.MkInt(8, integerSort)
			one, two := context.MkInt(1, integerSort), context.MkInt(2, integerSort)
			left := context.MkStore(context.MkStore(a, seven, one), eight, two)
			right := context.MkStore(context.MkStore(a, eight, two), seven, one)
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(context.MkNot(context.MkEq(left, right)))
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundIntegerArrayCrossBaseEqualityCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(37)
			a := gosmt.IntArrayConst(context, "a", 1)
			other := gosmt.IntArrayConst(context, "b", 2)
			seven, eight := gosmt.IntVal(context, 7), gosmt.IntVal(context, 8)
			left := gosmt.StoreIntArray(a, seven, gosmt.IntVal(context, 1))
			right := gosmt.StoreIntArray(other, seven, gosmt.IntVal(context, 1))
			formula := gosmt.And(gosmt.EqArray(left, right), gosmt.Not(gosmt.EqInt(gosmt.SelectIntArray(a, eight), gosmt.SelectIntArray(other, eight))))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			a := context.MkConst(context.MkStringSymbol("a"), arraySort)
			other := context.MkConst(context.MkStringSymbol("b"), arraySort)
			seven, eight, one := context.MkInt(7, integerSort), context.MkInt(8, integerSort), context.MkInt(1, integerSort)
			left, right := context.MkStore(a, seven, one), context.MkStore(other, seven, one)
			formula := context.MkAnd(context.MkEq(left, right), context.MkNot(context.MkEq(context.MkSelect(a, eight), context.MkSelect(other, eight))))
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundIntegerArrayConstantBaseEqualityCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(38)
			a := gosmt.IntArrayConst(context, "a", 1)
			zero := gosmt.ConstIntArray(gosmt.IntVal(context, 0))
			index := gosmt.IntVal(context, 8)
			formula := gosmt.And(gosmt.EqArray(a, zero), gosmt.Not(gosmt.EqInt(gosmt.SelectIntArray(a, index), gosmt.IntVal(context, 0))))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			a := context.MkConst(context.MkStringSymbol("a"), arraySort)
			zero, index := context.MkInt(0, integerSort), context.MkInt(8, integerSort)
			constant := context.MkConstArray(integerSort, zero)
			formula := context.MkAnd(context.MkEq(a, constant), context.MkNot(context.MkEq(context.MkSelect(a, index), zero)))
			solver := context.NewSolverForLogic("QF_ALIA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkMixedArrayIntegerEqualityExchangeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(39)
			a := gosmt.IntArrayConst(context, "a", 1)
			left := gosmt.IntConst(context, "i", 11)
			right := gosmt.IntConst(context, "j", 12)
			value := gosmt.IntVal(context, 42)
			formula := gosmt.And(gosmt.Le(left, right), gosmt.Le(right, left), gosmt.Not(gosmt.EqInt(gosmt.SelectIntArray(gosmt.StoreIntArray(a, left, value), right), value)))
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			integerSort := context.MkIntSort()
			arraySort := context.MkArraySort(integerSort, integerSort)
			a := context.MkConst(context.MkStringSymbol("a"), arraySort)
			left, right := context.MkIntConst("i"), context.MkIntConst("j")
			value := context.MkInt(42, integerSort)
			formula := context.MkAnd(context.MkLe(left, right), context.MkLe(right, left), context.MkNot(context.MkEq(context.MkSelect(context.MkStore(a, left, value), right), value)))
			solver := context.NewSolverForLogic("QF_AUFLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorMultiplicationCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(14)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 13)),
				gosmt.Not(gosmt.EqBitVec(gosmt.MulBitVec(x, gosmt.BitVecValue(8, context, 7)), gosmt.BitVecValue(8, context, 91))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			formula := context.MkAnd(context.MkEq(x, context.MkBV(13, 8)), context.MkNot(context.MkEq(context.MkBVMul(x, context.MkBV(7, 8)), context.MkBV(91, 8))))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorShiftCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(15)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0x81)),
				gosmt.Not(gosmt.EqBitVec(gosmt.LshrBitVec(x, gosmt.BitVecValue(8, context, 4)), gosmt.BitVecValue(8, context, 8))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			formula := context.MkAnd(context.MkEq(x, context.MkBV(0x81, 8)), context.MkNot(context.MkEq(context.MkBVLShr(x, context.MkBV(4, 8)), context.MkBV(8, 8))))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorDivisionCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(16)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 100)),
				gosmt.Not(gosmt.EqBitVec(gosmt.UdivBitVec(x, gosmt.BitVecValue(8, context, 7)), gosmt.BitVecValue(8, context, 14))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			formula := context.MkAnd(context.MkEq(x, context.MkBV(100, 8)), context.MkNot(context.MkEq(context.MkBVUDiv(x, context.MkBV(7, 8)), context.MkBV(14, 8))))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorExtractionCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(17)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0xab)),
				gosmt.Not(gosmt.EqBitVec(gosmt.ExtractBitVec(7, 4, x), gosmt.BitVecValue(4, context, 0xa))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			formula := context.MkAnd(context.MkEq(x, context.MkBV(0xab, 8)), context.MkNot(context.MkEq(context.MkExtract(7, 4, x), context.MkBV(0xa, 4))))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorRotationCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(18)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0x81)),
				gosmt.Not(gosmt.EqBitVec(gosmt.RotateLeftBitVec(1, x), gosmt.BitVecValue(8, context, 0x03))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			// The pinned Go binding omits Z3_mk_rotate_left, so express the
			// identical one-bit rotation with extract and concat.
			rotated := context.MkConcat(context.MkExtract(6, 0, x), context.MkExtract(7, 7, x))
			formula := context.MkAnd(context.MkEq(x, context.MkBV(0x81, 8)), context.MkNot(context.MkEq(rotated, context.MkBV(0x03, 8))))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBitVectorUnsignedAddOverflowCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(19)
			x := gosmt.BitVecConst(8, context, "x", 1)
			formula := gosmt.And(
				gosmt.EqBitVec(x, gosmt.BitVecValue(8, context, 0xff)),
				gosmt.Not(gosmt.UaddOverflowBitVec(x, gosmt.BitVecValue(8, context, 1))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			x := context.MkBVConst("x", 8)
			one := context.MkBV(1, 8)
			// The pinned Go binding omits Z3_mk_bvadd_no_overflow. Unsigned
			// add overflow is equivalently (x + 1) < x.
			overflow := context.MkBVULT(context.MkBVAdd(x, one), x)
			formula := context.MkAnd(context.MkEq(x, context.MkBV(0xff, 8)), context.MkNot(overflow))
			solver := context.NewSolverForLogic("QF_BV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkGroundUFBVUnaryCongruenceCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(20)
			x := gosmt.BitVecConst(8, context, "x", 1)
			y := gosmt.BitVecConst(8, context, "y", 2)
			function := gosmt.DeclareBitVecFunction(8, 4, context, "f", 3)
			formula := gosmt.And(
				gosmt.EqBitVec(x, y),
				gosmt.Not(gosmt.EqBitVec(gosmt.ApplyBitVecFunction(function, x), gosmt.ApplyBitVecFunction(function, y))),
			)
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			domain, rangeSort := context.MkBvSort(8), context.MkBvSort(4)
			function := context.MkFuncDecl(context.MkStringSymbol("f"), []*z3.Sort{domain}, rangeSort)
			x, y := context.MkBVConst("x", 8), context.MkBVConst("y", 8)
			formula := context.MkAnd(context.MkEq(x, y), context.MkNot(context.MkEq(context.MkApp(function, x), context.MkApp(function, y))))
			solver := context.NewSolverForLogic("QF_UFBV")
			solver.Assert(formula)
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkLinearIntegerModelCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(24)
			x := gosmt.IntConst(context, "x", 1)
			formula := gosmt.EqInt(gosmt.ScaleInt64(2, x), gosmt.IntVal(context, 2))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalInt(result.Value, x); !found || value != 1 {
				b.Fatal("invalid model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			intSort := context.MkIntSort()
			x := context.MkIntConst("x")
			formula := context.MkEq(context.MkMul(context.MkInt(2, intSort), x), context.MkInt(2, intSort))
			solver := context.NewSolverForLogic("QF_LIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(x, true); !ok {
				b.Fatal("invalid model")
			}
		}
	})
}

func BenchmarkLinearIntegerMultiRowModelCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(25)
			x := gosmt.IntConst(context, "x", 1)
			y := gosmt.IntConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.Le(gosmt.Add(x, y), gosmt.IntVal(context, 10)),
				gosmt.Le(gosmt.IntVal(context, 11), gosmt.Add(gosmt.ScaleInt64(2, x), y)),
			)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			xValue, xFound := gosmt.EvalInt(result.Value, x)
			if !xFound {
				b.Fatal("invalid model")
			}
			yValue, yFound := gosmt.EvalInt(result.Value, y)
			if !yFound || xValue+yValue > 10 || 2*xValue+yValue < 11 {
				b.Fatal("invalid model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			intSort := context.MkIntSort()
			x, y := context.MkIntConst("x"), context.MkIntConst("y")
			formula := context.MkAnd(
				context.MkLe(context.MkAdd(x, y), context.MkInt(10, intSort)),
				context.MkLe(context.MkInt(11, intSort), context.MkAdd(context.MkMul(context.MkInt(2, intSort), x), y)),
			)
			solver := context.NewSolverForLogic("QF_LIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, ok := model.Eval(x, true); !ok {
				b.Fatal("invalid x model")
			}
			if _, ok := model.Eval(y, true); !ok {
				b.Fatal("invalid y model")
			}
		}
	})
}

func BenchmarkBooleanLinearIntegerModelCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(26)
			x := gosmt.IntConst(context, "x", 1)
			one, two := gosmt.IntVal(context, 1), gosmt.IntVal(context, 2)
			formula := gosmt.And(gosmt.Or(gosmt.EqInt(x, one), gosmt.EqInt(x, two)), gosmt.NeInt(x, one))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalInt(result.Value, x); !found || value != 2 {
				b.Fatal("invalid model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			intSort := context.MkIntSort()
			x := context.MkIntConst("x")
			one, two := context.MkInt(1, intSort), context.MkInt(2, intSort)
			formula := context.MkAnd(context.MkOr(context.MkEq(x, one), context.MkEq(x, two)), context.MkNot(context.MkEq(x, one)))
			solver := context.NewSolverForLogic("QF_LIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(x, true); !ok {
				b.Fatal("invalid model")
			}
		}
	})
}

func BenchmarkIntegerDivModModelCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(27)
			x := gosmt.IntConst(context, "x", 1)
			quotient, remainder := gosmt.DivInt64(x, 3), gosmt.ModInt64(x, 3)
			formula := gosmt.And(
				gosmt.EqInt(x, gosmt.IntVal(context, -7)),
				gosmt.EqInt(quotient, gosmt.IntVal(context, -3)),
				gosmt.EqInt(remainder, gosmt.IntVal(context, 2)),
			)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalInt(result.Value, quotient); !found || value != -3 {
				b.Fatal("invalid quotient")
			}
			if value, found := gosmt.EvalInt(result.Value, remainder); !found || value != 2 {
				b.Fatal("invalid remainder")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			intSort := context.MkIntSort()
			x := context.MkIntConst("x")
			three := context.MkInt(3, intSort)
			quotient, remainder := context.MkDiv(x, three), context.MkMod(x, three)
			formula := context.MkAnd(
				context.MkEq(x, context.MkInt(-7, intSort)),
				context.MkEq(quotient, context.MkInt(-3, intSort)),
				context.MkEq(remainder, context.MkInt(2, intSort)),
			)
			solver := context.NewSolverForLogic("QF_LIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, ok := model.Eval(quotient, true); !ok {
				b.Fatal("invalid quotient")
			}
			if _, ok := model.Eval(remainder, true); !ok {
				b.Fatal("invalid remainder")
			}
		}
	})
}

func BenchmarkBooleanPigeonholeCold(b *testing.B) {
	const pigeons, holes = 5, 4
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(4)
			variables := make([][]gosmt.BoolExpr, pigeons)
			clauses := make([]gosmt.BoolExpr, 0, 75)
			for pigeon := 0; pigeon < pigeons; pigeon++ {
				variables[pigeon] = make([]gosmt.BoolExpr, holes)
				for hole := 0; hole < holes; hole++ {
					variables[pigeon][hole] = gosmt.BoolConst(context, "p", pigeon*holes+hole+1)
				}
				clauses = append(clauses, gosmt.Or(variables[pigeon]...))
				for left := 0; left < holes; left++ {
					for right := left + 1; right < holes; right++ {
						clauses = append(clauses, gosmt.Or(gosmt.Not(variables[pigeon][left]), gosmt.Not(variables[pigeon][right])))
					}
				}
			}
			for hole := 0; hole < holes; hole++ {
				for left := 0; left < pigeons; left++ {
					for right := left + 1; right < pigeons; right++ {
						clauses = append(clauses, gosmt.Or(gosmt.Not(variables[left][hole]), gosmt.Not(variables[right][hole])))
					}
				}
			}
			if _, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), gosmt.And(clauses...))).(gosmt.Unsat); !ok {
				b.Fatal("unexpected result")
			}
		}
	})

	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			variables := make([][]*z3.Expr, pigeons)
			clauses := make([]*z3.Expr, 0, 75)
			for pigeon := 0; pigeon < pigeons; pigeon++ {
				variables[pigeon] = make([]*z3.Expr, holes)
				for hole := 0; hole < holes; hole++ {
					variables[pigeon][hole] = context.MkBoolConst("p" + string(rune('a'+pigeon*holes+hole)))
				}
				clauses = append(clauses, context.MkOr(variables[pigeon]...))
				for left := 0; left < holes; left++ {
					for right := left + 1; right < holes; right++ {
						clauses = append(clauses, context.MkOr(context.MkNot(variables[pigeon][left]), context.MkNot(variables[pigeon][right])))
					}
				}
			}
			for hole := 0; hole < holes; hole++ {
				for left := 0; left < pigeons; left++ {
					for right := left + 1; right < pigeons; right++ {
						clauses = append(clauses, context.MkOr(context.MkNot(variables[left][hole]), context.MkNot(variables[right][hole])))
					}
				}
			}
			solver := context.NewSolverForLogic("QF_UF")
			solver.Assert(context.MkAnd(clauses...))
			if solver.Check() != z3.Unsatisfiable {
				b.Fatal("unexpected result")
			}
		}
	})
}

func BenchmarkBooleanPigeonholeHardCold(b *testing.B) {
	const pigeons, holes = 7, 6
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			if !solveGoSMTPigeonhole(pigeons, holes) {
				b.Fatal("unexpected result")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			if !solveZ3Pigeonhole(pigeons, holes) {
				b.Fatal("unexpected result")
			}
		}
	})
}

func solveGoSMTPigeonhole(pigeons, holes int) bool {
	context := gosmt.NewContext(5)
	variables := make([][]gosmt.BoolExpr, pigeons)
	clauses := make([]gosmt.BoolExpr, 0, pigeons*holes*holes+holes*pigeons*pigeons)
	for pigeon := 0; pigeon < pigeons; pigeon++ {
		variables[pigeon] = make([]gosmt.BoolExpr, holes)
		for hole := 0; hole < holes; hole++ {
			variables[pigeon][hole] = gosmt.BoolConst(context, "p", pigeon*holes+hole+1)
		}
		clauses = append(clauses, gosmt.Or(variables[pigeon]...))
		for left := 0; left < holes; left++ {
			for right := left + 1; right < holes; right++ {
				clauses = append(clauses, gosmt.Or(gosmt.Not(variables[pigeon][left]), gosmt.Not(variables[pigeon][right])))
			}
		}
	}
	for hole := 0; hole < holes; hole++ {
		for left := 0; left < pigeons; left++ {
			for right := left + 1; right < pigeons; right++ {
				clauses = append(clauses, gosmt.Or(gosmt.Not(variables[left][hole]), gosmt.Not(variables[right][hole])))
			}
		}
	}
	_, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), gosmt.And(clauses...))).(gosmt.Unsat)
	return ok
}

func solveZ3Pigeonhole(pigeons, holes int) bool {
	context := z3.NewContext()
	variables := make([][]*z3.Expr, pigeons)
	clauses := make([]*z3.Expr, 0, pigeons*holes*holes+holes*pigeons*pigeons)
	for pigeon := 0; pigeon < pigeons; pigeon++ {
		variables[pigeon] = make([]*z3.Expr, holes)
		for hole := 0; hole < holes; hole++ {
			variables[pigeon][hole] = context.MkBoolConst("p" + string(rune(0x100+pigeon*holes+hole)))
		}
		clauses = append(clauses, context.MkOr(variables[pigeon]...))
		for left := 0; left < holes; left++ {
			for right := left + 1; right < holes; right++ {
				clauses = append(clauses, context.MkOr(context.MkNot(variables[pigeon][left]), context.MkNot(variables[pigeon][right])))
			}
		}
	}
	for hole := 0; hole < holes; hole++ {
		for left := 0; left < pigeons; left++ {
			for right := left + 1; right < pigeons; right++ {
				clauses = append(clauses, context.MkOr(context.MkNot(variables[left][hole]), context.MkNot(variables[right][hole])))
			}
		}
	}
	solver := context.NewSolverForLogic("QF_UF")
	solver.Assert(context.MkAnd(clauses...))
	return solver.Check() == z3.Unsatisfiable
}
