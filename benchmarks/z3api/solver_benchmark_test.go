package z3api

import (
	"testing"

	z3 "github.com/Z3Prover/z3/src/api/go"
	"goforge.dev/goplus/std/smt"
	"goforge.dev/goplus/std/vec"
	"goforge.dev/gosmt"
)

func BenchmarkStringQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(8)
			x := gosmt.StringConst(context, "x", 1)
			formula := gosmt.And(
				gosmt.EqString(x, gosmt.ConcatString(gosmt.StringVal(context, "go-"), gosmt.StringVal(context, "forge"))),
				gosmt.EqInt(gosmt.LengthString(x), gosmt.IntVal(context, 8)),
				gosmt.ContainsString(x, gosmt.StringVal(context, "-")),
				gosmt.HasPrefixString(x, gosmt.StringVal(context, "go")),
				gosmt.HasSuffixString(x, gosmt.StringVal(context, "forge")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "go-forge" {
				b.Fatal("invalid string model")
			}
			if length, found := gosmt.EvalInt(result.Value, gosmt.LengthString(x)); !found || length != 8 {
				b.Fatal("invalid string length model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid formula model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			formula := context.MkAnd(
				context.MkEq(x, context.MkSeqConcat(context.MkString("go-"), context.MkString("forge"))),
				context.MkEq(context.MkSeqLength(x), context.MkInt(8, context.MkIntSort())),
				context.MkSeqContains(x, context.MkString("-")),
				context.MkSeqPrefix(context.MkString("go"), x),
				context.MkSeqSuffix(context.MkString("forge"), x),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid string model")
			}
			if _, found := model.Eval(context.MkSeqLength(x), true); !found {
				b.Fatal("invalid string length model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid formula model")
			}
		}
	})
}

func BenchmarkStringIndexedQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(9)
			value := gosmt.StringVal(context, "aXbcX")
			at := gosmt.AtString(value, gosmt.IntVal(context, 1))
			substring := gosmt.Substring(value, gosmt.IntVal(context, 1), gosmt.IntVal(context, 3))
			position := gosmt.IndexOfString(value, gosmt.StringVal(context, "X"), gosmt.IntVal(context, 2))
			replaced := gosmt.ReplaceString(value, gosmt.StringVal(context, "X"), gosmt.StringVal(context, "!"))
			formula := gosmt.And(
				gosmt.EqString(at, gosmt.StringVal(context, "X")),
				gosmt.EqString(substring, gosmt.StringVal(context, "Xbc")),
				gosmt.EqInt(position, gosmt.IntVal(context, 4)),
				gosmt.EqString(replaced, gosmt.StringVal(context, "a!bcX")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := gosmt.EvalString(result.Value, at); !found {
				b.Fatal("missing at model")
			}
			if _, found := gosmt.EvalString(result.Value, substring); !found {
				b.Fatal("missing substring model")
			}
			if _, found := gosmt.EvalInt(result.Value, position); !found {
				b.Fatal("missing index model")
			}
			if _, found := gosmt.EvalString(result.Value, replaced); !found {
				b.Fatal("missing replace model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			value := context.MkString("aXbcX")
			at := context.MkSeqAt(value, context.MkInt(1, context.MkIntSort()))
			substring := context.MkSeqExtract(value, context.MkInt(1, context.MkIntSort()), context.MkInt(3, context.MkIntSort()))
			position := context.MkSeqIndexOf(value, context.MkString("X"), context.MkInt(2, context.MkIntSort()))
			replaced := context.MkSeqReplace(value, context.MkString("X"), context.MkString("!"))
			formula := context.MkAnd(
				context.MkEq(at, context.MkString("X")),
				context.MkEq(substring, context.MkString("Xbc")),
				context.MkEq(position, context.MkInt(4, context.MkIntSort())),
				context.MkEq(replaced, context.MkString("a!bcX")),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, term := range []*z3.Expr{at, substring, position, replaced} {
				if _, found := model.Eval(term, true); !found {
					b.Fatal("missing model value")
				}
			}
		}
	})
}

func BenchmarkStringConversionQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(10)
			parsed := gosmt.ToIntString(gosmt.StringVal(context, "1234567890"))
			rendered := gosmt.FromIntString(parsed)
			formula := gosmt.And(
				gosmt.EqInt(parsed, gosmt.IntVal(context, 1234567890)),
				gosmt.EqString(rendered, gosmt.StringVal(context, "1234567890")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := gosmt.EvalInt(result.Value, parsed); !found {
				b.Fatal("missing integer model")
			}
			if _, found := gosmt.EvalString(result.Value, rendered); !found {
				b.Fatal("missing string model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			parsed := context.MkStrToInt(context.MkString("1234567890"))
			rendered := context.MkIntToStr(parsed)
			formula := context.MkAnd(
				context.MkEq(parsed, context.MkInt(1234567890, context.MkIntSort())),
				context.MkEq(rendered, context.MkString("1234567890")),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(parsed, true); !found {
				b.Fatal("missing integer model")
			}
			if _, found := model.Eval(rendered, true); !found {
				b.Fatal("missing string model")
			}
		}
	})
}

func BenchmarkStringRegexQFS(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(11)
			language := gosmt.ToRegexString(gosmt.StringVal(context, "go-forge"))
			value := gosmt.StringVal(context, "go-forge")
			formula := gosmt.InRegexString(value, language)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid regex model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			language := context.MkToRe(context.MkString("go-forge"))
			value := context.MkString("go-forge")
			formula := context.MkInRe(value, language)
			solver := context.NewSolverForLogic("QF_S")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid regex model")
			}
		}
	})
}

func BenchmarkStringRegexSymbolicQFS(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(12)
			x := gosmt.StringConst(context, "x", 1)
			language := gosmt.ConcatRegexExpr(
				gosmt.ToRegexString(gosmt.StringVal(context, "go-")),
				gosmt.LoopRegexExpr(2, 4, gosmt.RangeRegexString(gosmt.StringVal(context, "a"), gosmt.StringVal(context, "z"))),
			)
			formula := gosmt.InRegexString(x, language)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "go-aa" {
				b.Fatal("invalid symbolic regex model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid symbolic regex formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			language := context.MkReConcat(
				context.MkToRe(context.MkString("go-")),
				context.MkReLoop(context.MkReRange(context.MkString("a"), context.MkString("z")), 2, 4),
			)
			formula := context.MkInRe(x, language)
			solver := context.NewSolverForLogic("QF_S")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid symbolic regex model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid symbolic regex formula")
			}
		}
	})
}

func BenchmarkStringRegexInteractingQFS(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(13)
			x := gosmt.StringConst(context, "x", 1)
			a := gosmt.ToRegexString(gosmt.StringVal(context, "a"))
			middle := gosmt.ToRegexString(gosmt.StringVal(context, "b"))
			c := gosmt.ToRegexString(gosmt.StringVal(context, "c"))
			formula := gosmt.And(
				gosmt.InRegexString(x, gosmt.UnionRegexExpr(a, middle)),
				gosmt.InRegexString(x, gosmt.UnionRegexExpr(middle, c)),
				gosmt.Not(gosmt.InRegexString(x, a)),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "b" {
				b.Fatal("invalid interacting regex model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid interacting regex formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			a := context.MkToRe(context.MkString("a"))
			middle := context.MkToRe(context.MkString("b"))
			c := context.MkToRe(context.MkString("c"))
			formula := context.MkAnd(
				context.MkInRe(x, context.MkReUnion(a, middle)),
				context.MkInRe(x, context.MkReUnion(middle, c)),
				context.MkNot(context.MkInRe(x, a)),
			)
			solver := context.NewSolverForLogic("QF_S")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid interacting regex model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid interacting regex formula")
			}
		}
	})
}

func BenchmarkStringRegexBooleanQFS(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(14)
			x := gosmt.StringConst(context, "x", 1)
			a := gosmt.InRegexString(x, gosmt.ToRegexString(gosmt.StringVal(context, "a")))
			middle := gosmt.InRegexString(x, gosmt.ToRegexString(gosmt.StringVal(context, "b")))
			formula := gosmt.And(
				gosmt.Or(a, middle),
				gosmt.Not(a),
				gosmt.IfBool(a, gosmt.BoolValue(context, false), middle),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "b" {
				b.Fatal("invalid Boolean regex model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid Boolean regex formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			a := context.MkInRe(x, context.MkToRe(context.MkString("a")))
			middle := context.MkInRe(x, context.MkToRe(context.MkString("b")))
			formula := context.MkAnd(
				context.MkOr(a, middle),
				context.MkNot(a),
				context.MkOr(
					context.MkAnd(a, context.MkFalse()),
					context.MkAnd(context.MkNot(a), middle),
				),
			)
			solver := context.NewSolverForLogic("QF_S")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid Boolean regex model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid Boolean regex formula")
			}
		}
	})
}

func BenchmarkStringWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(15)
			x := gosmt.StringConst(context, "x", 1)
			formula := gosmt.EqString(
				gosmt.ConcatString(gosmt.StringVal(context, "go-"), x, gosmt.StringVal(context, "!")),
				gosmt.StringVal(context, "go-forge!"),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "forge" {
				b.Fatal("invalid word-equation model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			formula := context.MkEq(
				context.MkSeqConcat(context.MkString("go-"), x, context.MkString("!")),
				context.MkString("go-forge!"),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid word-equation model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid word-equation formula")
			}
		}
	})
}

func BenchmarkStringWordEquationLengthQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(20)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "forge"),
				),
				gosmt.EqInt(gosmt.LengthString(x), gosmt.IntVal(context, 3)),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "for" {
				b.Fatal("invalid left word-equation model")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "ge" {
				b.Fatal("invalid right word-equation model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			equation := context.MkEq(
				context.MkSeqConcat(x, y),
				context.MkString("forge"),
			)
			formula := context.MkAnd(
				equation,
				context.MkEq(
					context.MkSeqLength(x),
					context.MkInt(3, context.MkIntSort()),
				),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid left word-equation model")
			}
			if _, found := model.Eval(y, true); !found {
				b.Fatal("invalid right word-equation model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid word-equation formula")
			}
		}
	})
}

func BenchmarkStringWordEquationLengthInequalityQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(21)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "forge"),
				),
				gosmt.Lt(gosmt.IntVal(context, 1), gosmt.LengthString(x)),
				gosmt.Le(gosmt.LengthString(x), gosmt.IntVal(context, 3)),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "fo" {
				b.Fatal("invalid left word-equation model")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "rge" {
				b.Fatal("invalid right word-equation model")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			length := context.MkSeqLength(x)
			formula := context.MkAnd(
				context.MkEq(
					context.MkSeqConcat(x, y),
					context.MkString("forge"),
				),
				context.MkLt(context.MkInt(1, context.MkIntSort()), length),
				context.MkLe(length, context.MkInt(3, context.MkIntSort())),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid left word-equation model")
			}
			if _, found := model.Eval(y, true); !found {
				b.Fatal("invalid right word-equation model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid word-equation formula")
			}
		}
	})
}

func BenchmarkStringMultipleWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(22)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			z := gosmt.StringConst(context, "z", 3)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "abc"),
				),
				gosmt.EqString(
					gosmt.ConcatString(x, gosmt.StringVal(context, "-"), z),
					gosmt.StringVal(context, "a-tail"),
				),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			for _, item := range []struct {
				expression gosmt.StringExpr
				expected   string
			}{
				{x, "a"},
				{y, "bc"},
				{z, "tail"},
			} {
				if value, found := gosmt.EvalString(result.Value, item.expression); !found || value != item.expected {
					b.Fatal("invalid shared word-equation model")
				}
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid shared word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			z := context.MkConst(context.MkStringSymbol("z"), context.MkStringSort())
			formula := context.MkAnd(
				context.MkEq(
					context.MkSeqConcat(x, y),
					context.MkString("abc"),
				),
				context.MkEq(
					context.MkSeqConcat(x, context.MkString("-"), z),
					context.MkString("a-tail"),
				),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, z, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid shared word-equation model")
				}
			}
		}
	})
}

func BenchmarkStringEightWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(27)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			z := gosmt.StringConst(context, "z", 3)
			w := gosmt.StringConst(context, "w", 4)
			stringValue := func(value string) gosmt.StringExpr {
				return gosmt.StringVal(context, value)
			}
			formula := gosmt.And(
				gosmt.EqString(gosmt.ConcatString(x, y), stringValue("abc")),
				gosmt.EqString(gosmt.ConcatString(x, stringValue("-"), z), stringValue("a-tail")),
				gosmt.EqString(gosmt.ConcatString(y, w), stringValue("bc!")),
				gosmt.EqString(gosmt.ConcatString(z, w), stringValue("tail!")),
				gosmt.EqString(gosmt.ConcatString(stringValue("<"), x, y), stringValue("<abc")),
				gosmt.EqString(gosmt.ConcatString(x, y, stringValue(">")), stringValue("abc>")),
				gosmt.EqString(gosmt.ConcatString(stringValue("["), z, w), stringValue("[tail!")),
				gosmt.EqString(gosmt.ConcatString(z, w, stringValue("]")), stringValue("tail!]")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			for _, item := range []struct {
				expression gosmt.StringExpr
				expected   string
			}{
				{x, "a"},
				{y, "bc"},
				{z, "tail"},
				{w, "!"},
			} {
				if value, found := gosmt.EvalString(result.Value, item.expression); !found || value != item.expected {
					b.Fatal("invalid eight-equation model")
				}
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid eight-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			stringSort := context.MkStringSort()
			x := context.MkConst(context.MkStringSymbol("x"), stringSort)
			y := context.MkConst(context.MkStringSymbol("y"), stringSort)
			z := context.MkConst(context.MkStringSymbol("z"), stringSort)
			w := context.MkConst(context.MkStringSymbol("w"), stringSort)
			stringValue := context.MkString
			formula := context.MkAnd(
				context.MkEq(context.MkSeqConcat(x, y), stringValue("abc")),
				context.MkEq(context.MkSeqConcat(x, stringValue("-"), z), stringValue("a-tail")),
				context.MkEq(context.MkSeqConcat(y, w), stringValue("bc!")),
				context.MkEq(context.MkSeqConcat(z, w), stringValue("tail!")),
				context.MkEq(context.MkSeqConcat(stringValue("<"), x, y), stringValue("<abc")),
				context.MkEq(context.MkSeqConcat(x, y, stringValue(">")), stringValue("abc>")),
				context.MkEq(context.MkSeqConcat(stringValue("["), z, w), stringValue("[tail!")),
				context.MkEq(context.MkSeqConcat(z, w, stringValue("]")), stringValue("tail!]")),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, z, w, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid eight-equation model")
				}
			}
		}
	})
}

func BenchmarkStringOverflowWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(28)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			z := gosmt.StringConst(context, "z", 3)
			w := gosmt.StringConst(context, "w", 4)
			stringValue := func(value string) gosmt.StringExpr {
				return gosmt.StringVal(context, value)
			}
			formula := gosmt.And(
				gosmt.EqString(gosmt.ConcatString(x, y), stringValue("abc")),
				gosmt.EqString(gosmt.ConcatString(x, stringValue("-"), z), stringValue("a-tail")),
				gosmt.EqString(gosmt.ConcatString(y, w), stringValue("bc!")),
				gosmt.EqString(gosmt.ConcatString(z, w), stringValue("tail!")),
				gosmt.EqString(gosmt.ConcatString(stringValue("<"), x, y), stringValue("<abc")),
				gosmt.EqString(gosmt.ConcatString(x, y, stringValue(">")), stringValue("abc>")),
				gosmt.EqString(gosmt.ConcatString(stringValue("["), z, w), stringValue("[tail!")),
				gosmt.EqString(gosmt.ConcatString(z, w, stringValue("]")), stringValue("tail!]")),
				gosmt.EqString(gosmt.ConcatString(stringValue("<"), x, stringValue("-"), z), stringValue("<a-tail")),
				gosmt.EqString(gosmt.ConcatString(x, stringValue("-"), z, stringValue(">")), stringValue("a-tail>")),
				gosmt.EqString(gosmt.ConcatString(stringValue("("), y, w), stringValue("(bc!")),
				gosmt.EqString(gosmt.ConcatString(z, w, stringValue(")")), stringValue("tail!)")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			for _, item := range []struct {
				expression gosmt.StringExpr
				expected   string
			}{
				{x, "a"},
				{y, "bc"},
				{z, "tail"},
				{w, "!"},
			} {
				if value, found := gosmt.EvalString(result.Value, item.expression); !found || value != item.expected {
					b.Fatal("invalid overflow-equation model")
				}
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid overflow-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			stringSort := context.MkStringSort()
			x := context.MkConst(context.MkStringSymbol("x"), stringSort)
			y := context.MkConst(context.MkStringSymbol("y"), stringSort)
			z := context.MkConst(context.MkStringSymbol("z"), stringSort)
			w := context.MkConst(context.MkStringSymbol("w"), stringSort)
			stringValue := context.MkString
			formula := context.MkAnd(
				context.MkEq(context.MkSeqConcat(x, y), stringValue("abc")),
				context.MkEq(context.MkSeqConcat(x, stringValue("-"), z), stringValue("a-tail")),
				context.MkEq(context.MkSeqConcat(y, w), stringValue("bc!")),
				context.MkEq(context.MkSeqConcat(z, w), stringValue("tail!")),
				context.MkEq(context.MkSeqConcat(stringValue("<"), x, y), stringValue("<abc")),
				context.MkEq(context.MkSeqConcat(x, y, stringValue(">")), stringValue("abc>")),
				context.MkEq(context.MkSeqConcat(stringValue("["), z, w), stringValue("[tail!")),
				context.MkEq(context.MkSeqConcat(z, w, stringValue("]")), stringValue("tail!]")),
				context.MkEq(context.MkSeqConcat(stringValue("<"), x, stringValue("-"), z), stringValue("<a-tail")),
				context.MkEq(context.MkSeqConcat(x, stringValue("-"), z, stringValue(">")), stringValue("a-tail>")),
				context.MkEq(context.MkSeqConcat(stringValue("("), y, w), stringValue("(bc!")),
				context.MkEq(context.MkSeqConcat(z, w, stringValue(")")), stringValue("tail!)")),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, z, w, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid overflow-equation model")
				}
			}
		}
	})
}

func BenchmarkStringWordEquationRegexQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(23)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			language := gosmt.UnionRegexExpr(
				gosmt.ToRegexString(gosmt.StringVal(context, "a")),
				gosmt.ToRegexString(gosmt.StringVal(context, "ab")),
			)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "abc"),
				),
				gosmt.InRegexString(x, language),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "a" {
				b.Fatal("invalid regex-constrained word-equation model")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "bc" {
				b.Fatal("invalid word-equation remainder")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid regex-constrained word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			language := context.MkReUnion(
				context.MkToRe(context.MkString("a")),
				context.MkToRe(context.MkString("ab")),
			)
			formula := context.MkAnd(
				context.MkEq(
					context.MkSeqConcat(x, y),
					context.MkString("abc"),
				),
				context.MkInRe(x, language),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid regex-constrained word-equation model")
				}
			}
		}
	})
}

func BenchmarkStringWordEquationBooleanRegexQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(24)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "abc"),
				),
				gosmt.Or(
					gosmt.InRegexString(x, gosmt.RangeRegexString(
						gosmt.StringVal(context, "z"), gosmt.StringVal(context, "z"),
					)),
					gosmt.InRegexString(x, gosmt.RangeRegexString(
						gosmt.StringVal(context, "a"), gosmt.StringVal(context, "a"),
					)),
				),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "a" {
				b.Fatal("invalid Boolean-regex word-equation model")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "bc" {
				b.Fatal("invalid word-equation remainder")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid Boolean-regex word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			formula := context.MkAnd(
				context.MkEq(
					context.MkSeqConcat(x, y),
					context.MkString("abc"),
				),
				context.MkOr(
					context.MkInRe(x, context.MkReRange(context.MkString("z"), context.MkString("z"))),
					context.MkInRe(x, context.MkReRange(context.MkString("a"), context.MkString("a"))),
				),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid Boolean-regex word-equation model")
				}
			}
		}
	})
}

func BenchmarkStringWordEquationDisequalityQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(25)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "ab"),
				),
				gosmt.Not(gosmt.EqString(x, gosmt.StringVal(context, ""))),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "a" {
				b.Fatal("invalid disequality-constrained word-equation model")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "b" {
				b.Fatal("invalid word-equation remainder")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid disequality-constrained word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			formula := context.MkAnd(
				context.MkEq(
					context.MkSeqConcat(x, y),
					context.MkString("ab"),
				),
				context.MkNot(context.MkEq(x, context.MkString(""))),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid disequality-constrained word-equation model")
				}
			}
		}
	})
}

func BenchmarkStringWordEquationPredicateQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(26)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.And(
				gosmt.EqString(
					gosmt.ConcatString(x, y),
					gosmt.StringVal(context, "abc"),
				),
				gosmt.ContainsString(x, gosmt.StringVal(context, "b")),
				gosmt.HasPrefixString(x, gosmt.StringVal(context, "a")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "ab" {
				b.Fatal("invalid predicate-constrained word-equation model")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "c" {
				b.Fatal("invalid word-equation remainder")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid predicate-constrained word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			formula := context.MkAnd(
				context.MkEq(
					context.MkSeqConcat(x, y),
					context.MkString("abc"),
				),
				context.MkSeqContains(x, context.MkString("b")),
				context.MkSeqPrefix(context.MkString("a"), x),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			for _, expression := range []*z3.Expr{x, y, formula} {
				if _, found := model.Eval(expression, true); !found {
					b.Fatal("invalid predicate-constrained word-equation model")
				}
			}
		}
	})
}

func BenchmarkStringDelimitedWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(16)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.EqString(
				gosmt.ConcatString(
					gosmt.StringVal(context, "["), x, gosmt.StringVal(context, "]"),
					y, gosmt.StringVal(context, "!"),
				),
				gosmt.StringVal(context, "[go]forge!"),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "go" {
				b.Fatal("invalid first word-equation value")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "forge" {
				b.Fatal("invalid second word-equation value")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid delimited word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			formula := context.MkEq(
				context.MkSeqConcat(
					context.MkString("["), x, context.MkString("]"),
					y, context.MkString("!"),
				),
				context.MkString("[go]forge!"),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid first word-equation model")
			}
			if _, found := model.Eval(y, true); !found {
				b.Fatal("invalid second word-equation model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid delimited word-equation formula")
			}
		}
	})
}

func BenchmarkStringCanonicalWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(17)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			formula := gosmt.EqString(
				gosmt.ConcatString(x, y),
				gosmt.StringVal(context, "forge"),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "" {
				b.Fatal("invalid canonical first value")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "forge" {
				b.Fatal("invalid canonical second value")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid canonical word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			formula := context.MkEq(
				context.MkSeqConcat(x, y),
				context.MkString("forge"),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid canonical first model")
			}
			if _, found := model.Eval(y, true); !found {
				b.Fatal("invalid canonical second model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid canonical word-equation formula")
			}
		}
	})
}

func BenchmarkStringRepeatedWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(18)
			x := gosmt.StringConst(context, "x", 1)
			formula := gosmt.EqString(
				gosmt.ConcatString(x, gosmt.StringVal(context, "-"), x),
				gosmt.StringVal(context, "go-go"),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "go" {
				b.Fatal("invalid repeated-symbol value")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid repeated-symbol formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			formula := context.MkEq(
				context.MkSeqConcat(x, context.MkString("-"), x),
				context.MkString("go-go"),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid repeated-symbol model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid repeated-symbol formula")
			}
		}
	})
}

func BenchmarkStringInteractingWordEquationQFSLIA(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := gosmt.NewContext(19)
			x := gosmt.StringConst(context, "x", 1)
			y := gosmt.StringConst(context, "y", 2)
			equation := gosmt.EqString(
				gosmt.ConcatString(
					gosmt.StringVal(context, "["), x,
					gosmt.StringVal(context, "]"), y,
					gosmt.StringVal(context, "!"),
				),
				gosmt.StringVal(context, "[a]b]c!"),
			)
			formula := gosmt.And(
				equation,
				gosmt.EqString(x, gosmt.StringVal(context, "a]b")),
			)
			result, ok := gosmt.Check(gosmt.Assert(index+1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalString(result.Value, x); !found || value != "a]b" {
				b.Fatal("invalid interacting first value")
			}
			if value, found := gosmt.EvalString(result.Value, y); !found || value != "c" {
				b.Fatal("invalid interacting second value")
			}
			if valid, found := gosmt.EvalBool(result.Value, formula); !found || !valid {
				b.Fatal("invalid interacting word-equation formula")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for index := 0; index < b.N; index++ {
			context := z3.NewContext()
			x := context.MkConst(context.MkStringSymbol("x"), context.MkStringSort())
			y := context.MkConst(context.MkStringSymbol("y"), context.MkStringSort())
			equation := context.MkEq(
				context.MkSeqConcat(
					context.MkString("["), x,
					context.MkString("]"), y,
					context.MkString("!"),
				),
				context.MkString("[a]b]c!"),
			)
			formula := context.MkAnd(
				equation,
				context.MkEq(x, context.MkString("a]b")),
			)
			solver := context.NewSolverForLogic("QF_SLIA")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if _, found := model.Eval(x, true); !found {
				b.Fatal("invalid interacting first model")
			}
			if _, found := model.Eval(y, true); !found {
				b.Fatal("invalid interacting second model")
			}
			if _, found := model.Eval(formula, true); !found {
				b.Fatal("invalid interacting word-equation formula")
			}
		}
	})
}

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

func BenchmarkFiniteEnumerationDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(28)
			red := gosmt.DatatypeConstructor(1, 3, 0, context, "red")
			x := gosmt.DatatypeConst(1, 3, context, "x", 1)
			formula := gosmt.And(gosmt.Not(gosmt.EqDatatype(x, red)), gosmt.IsDatatypeConstructor(1, 3, 1, x))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalDatatype(1, 3, result.Value, x); !found || value.ConstructorID != 1 {
				b.Fatal("invalid datatype model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			sort, constructors, testers := context.MkEnumSort("Color", []string{"red", "green", "blue"})
			x := context.MkConst(context.MkStringSymbol("x"), sort)
			red := context.MkApp(constructors[0])
			isGreen := context.MkApp(testers[1], x)
			solver := context.NewSolverForLogic("QF_DT")
			solver.Assert(context.MkAnd(context.MkNot(context.MkEq(x, red)), isGreen))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(x, true); !ok {
				b.Fatal("invalid datatype model")
			}
		}
	})
}

func BenchmarkRecursiveUnaryDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(40)
			zero := gosmt.DatatypeConstructor(2, 2, 0, context, "zero")
			succ := gosmt.DeclareRecursiveDatatypeConstructor(2, 2, 1, context, "succ", "pred")
			x := gosmt.DatatypeConst(2, 2, context, "x", 1)
			one := gosmt.ApplyRecursiveDatatypeConstructor(succ, zero)
			two := gosmt.ApplyRecursiveDatatypeConstructor(succ, one)
			formula := gosmt.And(gosmt.EqDatatype(x, two), gosmt.EqDatatype(gosmt.SelectRecursiveDatatypeConstructor(succ, x), one), gosmt.IsRecursiveDatatypeConstructor(succ, x))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalDatatype(2, 2, result.Value, x); !found || value.Child == nil || value.Child.Child == nil {
				b.Fatal("invalid datatype model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			zeroDeclaration := context.MkConstructor("zero", "is-zero", nil, nil, nil)
			succDeclaration := context.MkConstructor("succ", "is-succ", []string{"pred"}, []*z3.Sort{nil}, []uint{0})
			natSort := context.MkDatatypeSort("Nat", []*z3.Constructor{zeroDeclaration, succDeclaration})
			zero := context.MkApp(context.GetDatatypeSortConstructor(natSort, 0))
			succ := context.GetDatatypeSortConstructor(natSort, 1)
			pred := context.GetDatatypeSortConstructorAccessor(natSort, 1, 0)
			isSucc := context.GetDatatypeSortRecognizer(natSort, 1)
			x := context.MkConst(context.MkStringSymbol("x"), natSort)
			one := context.MkApp(succ, zero)
			two := context.MkApp(succ, one)
			formula := context.MkAnd(context.MkEq(x, two), context.MkEq(context.MkApp(pred, x), one), context.MkApp(isSucc, x))
			solver := context.NewSolverForLogic("QF_DT")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(x, true); !ok {
				b.Fatal("invalid datatype model")
			}
		}
	})
}

func BenchmarkBinaryRecursiveDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(41)
			leaf := gosmt.DatatypeConstructor(3, 2, 0, context, "leaf")
			node := gosmt.DeclareBinaryRecursiveDatatypeConstructor(3, 2, 1, context, "node", "left", "right")
			x := gosmt.DatatypeConst(3, 2, context, "x", 1)
			branch := gosmt.ApplyBinaryRecursiveDatatypeConstructor(node, leaf, leaf)
			tree := gosmt.ApplyBinaryRecursiveDatatypeConstructor(node, branch, leaf)
			formula := gosmt.And(
				gosmt.EqDatatype(x, tree),
				gosmt.EqDatatype(gosmt.SelectBinaryRecursiveDatatypeConstructor(gosmt.FirstDatatypeField(), node, x), branch),
				gosmt.EqDatatype(gosmt.SelectBinaryRecursiveDatatypeConstructor(gosmt.SecondDatatypeField(), node, x), leaf),
				gosmt.IsBinaryRecursiveDatatypeConstructor(node, x),
			)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalDatatype(3, 2, result.Value, x); !found || value.Child == nil || value.SecondChild == nil || value.Child.Child == nil || value.Child.SecondChild == nil {
				b.Fatal("invalid datatype model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			leafDeclaration := context.MkConstructor("leaf", "is-leaf", nil, nil, nil)
			nodeDeclaration := context.MkConstructor("node", "is-node", []string{"left", "right"}, []*z3.Sort{nil, nil}, []uint{0, 0})
			treeSort := context.MkDatatypeSort("Tree", []*z3.Constructor{leafDeclaration, nodeDeclaration})
			leaf := context.MkApp(context.GetDatatypeSortConstructor(treeSort, 0))
			node := context.GetDatatypeSortConstructor(treeSort, 1)
			left := context.GetDatatypeSortConstructorAccessor(treeSort, 1, 0)
			right := context.GetDatatypeSortConstructorAccessor(treeSort, 1, 1)
			isNode := context.GetDatatypeSortRecognizer(treeSort, 1)
			x := context.MkConst(context.MkStringSymbol("x"), treeSort)
			branch := context.MkApp(node, leaf, leaf)
			tree := context.MkApp(node, branch, leaf)
			formula := context.MkAnd(context.MkEq(x, tree), context.MkEq(context.MkApp(left, x), branch), context.MkEq(context.MkApp(right, x), leaf), context.MkApp(isNode, x))
			solver := context.NewSolverForLogic("QF_DT")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(x, true); !ok {
				b.Fatal("invalid datatype model")
			}
		}
	})
}

func BenchmarkNaryRecursiveDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(42)
			leaf := gosmt.DatatypeConstructor(4, 2, 0, context, "leaf")
			names := vec.Cons[string]{Head: "first", Tail: vec.Cons[string]{Head: "second", Tail: vec.Cons[string]{Head: "third", Tail: vec.Nil[string]{}}}}
			branch := gosmt.DeclareNaryRecursiveDatatypeConstructor(4, 2, 1, 3, context, "branch", names)
			values := func(first, second, third gosmt.DatatypeExpr) vec.Vec[gosmt.DatatypeExpr] {
				return vec.Cons[gosmt.DatatypeExpr]{Head: first, Tail: vec.Cons[gosmt.DatatypeExpr]{Head: second, Tail: vec.Cons[gosmt.DatatypeExpr]{Head: third, Tail: vec.Nil[gosmt.DatatypeExpr]{}}}}
			}
			x := gosmt.DatatypeConst(4, 2, context, "x", 1)
			nested := gosmt.ApplyNaryRecursiveDatatypeConstructor(branch, values(leaf, leaf, leaf))
			tree := gosmt.ApplyNaryRecursiveDatatypeConstructor(branch, values(leaf, nested, leaf))
			formula := gosmt.And(
				gosmt.EqDatatype(x, tree),
				gosmt.EqDatatype(gosmt.SelectNaryRecursiveDatatypeConstructor(vec.Succ{Prev: vec.Zero{}}, branch, x), nested),
				gosmt.IsNaryRecursiveDatatypeConstructor(branch, x),
			)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalDatatype(4, 2, result.Value, x); !found || value.Children.Len() != 3 {
				b.Fatal("invalid datatype model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			leafDeclaration := context.MkConstructor("leaf", "is-leaf", nil, nil, nil)
			branchDeclaration := context.MkConstructor("branch", "is-branch", []string{"first", "second", "third"}, []*z3.Sort{nil, nil, nil}, []uint{0, 0, 0})
			treeSort := context.MkDatatypeSort("Tree", []*z3.Constructor{leafDeclaration, branchDeclaration})
			leaf := context.MkApp(context.GetDatatypeSortConstructor(treeSort, 0))
			branch := context.GetDatatypeSortConstructor(treeSort, 1)
			second := context.GetDatatypeSortConstructorAccessor(treeSort, 1, 1)
			isBranch := context.GetDatatypeSortRecognizer(treeSort, 1)
			x := context.MkConst(context.MkStringSymbol("x"), treeSort)
			nested := context.MkApp(branch, leaf, leaf, leaf)
			tree := context.MkApp(branch, leaf, nested, leaf)
			formula := context.MkAnd(context.MkEq(x, tree), context.MkEq(context.MkApp(second, x), nested), context.MkApp(isBranch, x))
			solver := context.NewSolverForLogic("QF_DT")
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, ok := solver.Model().Eval(x, true); !ok {
				b.Fatal("invalid datatype model")
			}
		}
	})
}

func BenchmarkMixedRecursiveDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(83)
			signature := gosmt.IntDatatypeMixedField("payload", gosmt.SelfDatatypeMixedField("next", gosmt.EmptyDatatypeMixedSignature()))
			node := gosmt.DeclareMixedDatatypeConstructor(830, 2, 1, context, "node", signature)
			leaf := gosmt.DatatypeConstructor(830, 2, 0, context, "leaf")
			arguments := gosmt.IntDatatypeMixedArgument(gosmt.IntVal(context, 42), gosmt.SelfDatatypeMixedArgument(leaf, gosmt.EmptyDatatypeMixedArguments(context)))
			x := gosmt.DatatypeConst(830, 2, context, "x", 1)
			value := gosmt.ApplyMixedDatatypeConstructor(node, arguments)
			payload := gosmt.MixedDatatypeFields(node)
			formula := gosmt.And(gosmt.EqDatatype(x, value), gosmt.EqInt(gosmt.SelectMixedIntDatatypeField(payload, x), gosmt.IntVal(context, 42)), gosmt.IsMixedDatatypeConstructor(node, x))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := gosmt.EvalDatatype(830, 2, result.Value, x); !found {
				b.Fatal("missing model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			leafDecl := context.MkConstructor("leaf", "is-leaf", nil, nil, nil)
			nodeDecl := context.MkConstructor("node", "is-node", []string{"payload", "next"}, []*z3.Sort{context.MkIntSort(), nil}, []uint{0, 0})
			tree := context.MkDatatypeSort("Tree", []*z3.Constructor{leafDecl, nodeDecl})
			leaf := context.MkApp(context.GetDatatypeSortConstructor(tree, 0))
			node := context.MkApp(context.GetDatatypeSortConstructor(tree, 1), context.MkInt(42, context.MkIntSort()), leaf)
			x := context.MkConst(context.MkStringSymbol("x"), tree)
			payload := context.MkApp(context.GetDatatypeSortConstructorAccessor(tree, 1, 0), x)
			recognizer := context.MkApp(context.GetDatatypeSortRecognizer(tree, 1), x)
			solver := context.NewSolver()
			solver.Assert(context.MkAnd(context.MkEq(x, node), context.MkEq(payload, context.MkInt(42, context.MkIntSort())), recognizer))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if model == nil {
				b.Fatal("missing model")
			}
			if _, found := model.Eval(x, true); !found {
				b.Fatal("missing model value")
			}
		}
	})
}

func BenchmarkMutuallyRecursiveDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(84)
			leaf := gosmt.DatatypeConstructor(840, 2, 0, context, "leaf")
			nilValue := gosmt.DatatypeConstructor(841, 2, 0, context, "nil")
			node := gosmt.DeclareMixedDatatypeConstructor(840, 2, 1, context, "node", gosmt.DatatypeReferenceMixedField(841, 2, "children", gosmt.EmptyDatatypeMixedSignature()))
			cons := gosmt.DeclareMixedDatatypeConstructor(841, 2, 1, context, "cons", gosmt.DatatypeReferenceMixedField(840, 2, "head", gosmt.SelfDatatypeMixedField("tail", gosmt.EmptyDatatypeMixedSignature())))
			forest := gosmt.ApplyMixedDatatypeConstructor(cons, gosmt.DatatypeReferenceMixedArgument(840, 2, leaf, gosmt.SelfDatatypeMixedArgument(nilValue, gosmt.EmptyDatatypeMixedArguments(context))))
			tree := gosmt.ApplyMixedDatatypeConstructor(node, gosmt.DatatypeReferenceMixedArgument(841, 2, forest, gosmt.EmptyDatatypeMixedArguments(context)))
			x := gosmt.DatatypeConst(840, 2, context, "x", 1)
			children := gosmt.MixedDatatypeFields(node)
			head := gosmt.MixedDatatypeFields(cons)
			selected := gosmt.SelectMixedDatatypeReferenceField(841, 2, children, x)
			formula := gosmt.And(gosmt.EqDatatype(x, tree), gosmt.EqDatatype(gosmt.SelectMixedDatatypeReferenceField(840, 2, head, selected), leaf))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := gosmt.EvalDatatype(840, 2, result.Value, x); !found {
				b.Fatal("missing model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			leafDecl := context.MkConstructor("leaf", "is-leaf", nil, nil, nil)
			nodeDecl := context.MkConstructor("node", "is-node", []string{"children"}, []*z3.Sort{nil}, []uint{1})
			nilDecl := context.MkConstructor("nil", "is-nil", nil, nil, nil)
			consDecl := context.MkConstructor("cons", "is-cons", []string{"head", "tail"}, []*z3.Sort{nil, nil}, []uint{0, 1})
			sorts := context.MkDatatypeSorts([]string{"Tree", "Forest"}, [][]*z3.Constructor{{leafDecl, nodeDecl}, {nilDecl, consDecl}})
			leaf := context.MkApp(context.GetDatatypeSortConstructor(sorts[0], 0))
			nilValue := context.MkApp(context.GetDatatypeSortConstructor(sorts[1], 0))
			forest := context.MkApp(context.GetDatatypeSortConstructor(sorts[1], 1), leaf, nilValue)
			tree := context.MkApp(context.GetDatatypeSortConstructor(sorts[0], 1), forest)
			x := context.MkConst(context.MkStringSymbol("x"), sorts[0])
			children := context.MkApp(context.GetDatatypeSortConstructorAccessor(sorts[0], 1, 0), x)
			head := context.MkApp(context.GetDatatypeSortConstructorAccessor(sorts[1], 1, 0), children)
			solver := context.NewSolver()
			solver.Assert(context.MkAnd(context.MkEq(x, tree), context.MkEq(head, leaf)))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			if model == nil {
				b.Fatal("missing model")
			}
			if _, found := model.Eval(x, true); !found {
				b.Fatal("missing model value")
			}
		}
	})
}

func BenchmarkMutuallyParametricDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(845)
			leaf := gosmt.DeclareMixedDatatypeConstructor(8450, 2, 0, context, "leaf", gosmt.IntDatatypeMixedField("value", gosmt.EmptyDatatypeMixedSignature()))
			node := gosmt.DeclareMixedDatatypeConstructor(8450, 2, 1, context, "node", gosmt.DatatypeReferenceMixedField(8451, 2, "children", gosmt.EmptyDatatypeMixedSignature()))
			empty := gosmt.DatatypeConstructor(8451, 2, 0, context, "empty")
			more := gosmt.DeclareMixedDatatypeConstructor(8451, 2, 1, context, "more", gosmt.DatatypeReferenceMixedField(8450, 2, "first", gosmt.SelfDatatypeMixedField("rest", gosmt.EmptyDatatypeMixedSignature())))
			leafValue := gosmt.ApplyMixedDatatypeConstructor(leaf, gosmt.IntDatatypeMixedArgument(gosmt.IntVal(context, 42), gosmt.EmptyDatatypeMixedArguments(context)))
			forest := gosmt.ApplyMixedDatatypeConstructor(more, gosmt.DatatypeReferenceMixedArgument(8450, 2, leafValue, gosmt.SelfDatatypeMixedArgument(empty, gosmt.EmptyDatatypeMixedArguments(context))))
			tree := gosmt.ApplyMixedDatatypeConstructor(node, gosmt.DatatypeReferenceMixedArgument(8451, 2, forest, gosmt.EmptyDatatypeMixedArguments(context)))
			x := gosmt.DatatypeConst(8450, 2, context, "tree", 1)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), gosmt.EqDatatype(x, tree))).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := gosmt.EvalDatatype(8450, 2, result.Value, x); !found {
				b.Fatal("missing model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			leafDecl := context.MkConstructor("leaf", "is-leaf", []string{"value"}, []*z3.Sort{context.MkIntSort()}, []uint{0})
			nodeDecl := context.MkConstructor("node", "is-node", []string{"children"}, []*z3.Sort{nil}, []uint{1})
			emptyDecl := context.MkConstructor("empty", "is-empty", nil, nil, nil)
			moreDecl := context.MkConstructor("more", "is-more", []string{"first", "rest"}, []*z3.Sort{nil, nil}, []uint{0, 1})
			sorts := context.MkDatatypeSorts([]string{"TreeInt", "ForestInt"}, [][]*z3.Constructor{{leafDecl, nodeDecl}, {emptyDecl, moreDecl}})
			leaf := context.MkApp(context.GetDatatypeSortConstructor(sorts[0], 0), context.MkInt(42, context.MkIntSort()))
			empty := context.MkApp(context.GetDatatypeSortConstructor(sorts[1], 0))
			forest := context.MkApp(context.GetDatatypeSortConstructor(sorts[1], 1), leaf, empty)
			tree := context.MkApp(context.GetDatatypeSortConstructor(sorts[0], 1), forest)
			x := context.MkConst(context.MkStringSymbol("tree"), sorts[0])
			solver := context.NewSolver()
			solver.Assert(context.MkEq(x, tree))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, found := solver.Model().Eval(x, true); !found {
				b.Fatal("missing model")
			}
		}
	})
}

func BenchmarkParametricDatatypeInstantiationCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(85)
			signature := gosmt.IntDatatypeMixedField("head", gosmt.SelfDatatypeMixedField("tail", gosmt.EmptyDatatypeMixedSignature()))
			cons := gosmt.DeclareMixedDatatypeConstructor(850, 2, 1, context, "cons", signature)
			nilValue := gosmt.DatatypeConstructor(850, 2, 0, context, "nil")
			arguments := gosmt.IntDatatypeMixedArgument(gosmt.IntVal(context, 42), gosmt.SelfDatatypeMixedArgument(nilValue, gosmt.EmptyDatatypeMixedArguments(context)))
			x := gosmt.DatatypeConst(850, 2, context, "xs", 1)
			value := gosmt.ApplyMixedDatatypeConstructor(cons, arguments)
			head := gosmt.MixedDatatypeFields(cons)
			formula := gosmt.And(gosmt.EqDatatype(x, value), gosmt.EqInt(gosmt.SelectMixedIntDatatypeField(head, x), gosmt.IntVal(context, 42)), gosmt.IsMixedDatatypeConstructor(cons, x))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := gosmt.EvalDatatype(850, 2, result.Value, x); !found {
				b.Fatal("missing model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			nilDecl := context.MkConstructor("nil", "is-nil", nil, nil, nil)
			consDecl := context.MkConstructor("cons", "is-cons", []string{"head", "tail"}, []*z3.Sort{context.MkIntSort(), nil}, []uint{0, 0})
			listInt := context.MkDatatypeSort("PListInt", []*z3.Constructor{nilDecl, consDecl})
			nilValue := context.MkApp(context.GetDatatypeSortConstructor(listInt, 0))
			cons := context.MkApp(context.GetDatatypeSortConstructor(listInt, 1), context.MkInt(42, context.MkIntSort()), nilValue)
			x := context.MkConst(context.MkStringSymbol("xs"), listInt)
			head := context.MkApp(context.GetDatatypeSortConstructorAccessor(listInt, 1, 0), x)
			recognizer := context.MkApp(context.GetDatatypeSortRecognizer(listInt, 1), x)
			solver := context.NewSolver()
			solver.Assert(context.MkAnd(context.MkEq(x, cons), context.MkEq(head, context.MkInt(42, context.MkIntSort())), recognizer))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, found := solver.Model().Eval(x, true); !found {
				b.Fatal("missing model value")
			}
		}
	})
}

func BenchmarkMultiParameterDatatypeCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := gosmt.NewContext(855)
			signature := gosmt.IntDatatypeMixedField("first", gosmt.BoolDatatypeMixedField("second", gosmt.EmptyDatatypeMixedSignature()))
			pair := gosmt.DeclareMixedDatatypeConstructor(8550, 1, 0, context, "pair", signature)
			arguments := gosmt.IntDatatypeMixedArgument(
				gosmt.IntVal(context, 42),
				gosmt.BoolDatatypeMixedArgument(gosmt.BoolValue(context, true), gosmt.EmptyDatatypeMixedArguments(context)),
			)
			value := gosmt.DatatypeConst(8550, 1, context, "value", 1)
			formula := gosmt.EqDatatype(value, gosmt.ApplyMixedDatatypeConstructor(pair, arguments))
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			exact, found := gosmt.EvalDatatype(8550, 1, result.Value, value)
			if !found || exact.Fields.Len() != 2 {
				b.Fatal("missing model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			pairDecl := context.MkConstructor(
				"pair", "is-pair",
				[]string{"first", "second"},
				[]*z3.Sort{context.MkIntSort(), context.MkBoolSort()},
				[]uint{0, 0},
			)
			pairSort := context.MkDatatypeSort("PairIntBool", []*z3.Constructor{pairDecl})
			value := context.MkConst(context.MkStringSymbol("value"), pairSort)
			pair := context.MkApp(
				context.GetDatatypeSortConstructor(pairSort, 0),
				context.MkInt(42, context.MkIntSort()),
				context.MkTrue(),
			)
			first := context.MkApp(context.GetDatatypeSortConstructorAccessor(pairSort, 0, 0), value)
			second := context.MkApp(context.GetDatatypeSortConstructorAccessor(pairSort, 0, 1), value)
			solver := context.NewSolver()
			solver.Assert(context.MkEq(value, pair))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			_, valueFound := model.Eval(value, true)
			_, firstFound := model.Eval(first, true)
			_, secondFound := model.Eval(second, true)
			if !valueFound || !firstFound || !secondFound {
				b.Fatal("missing model")
			}
		}
	})
}

func BenchmarkDatatypeUpdateFieldCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			signature := smt.IntDatatypeField("head", smt.SelfDatatypeField("tail", smt.EmptyMixedDatatypeSignature{}))
			cons := smt.DeclareMixedRecursiveDatatypeConstructor(860, 2, 1, "cons", signature)
			nilValue := smt.DatatypeConstructor(860, 2, 0, "nil")
			arguments := smt.IntDatatypeArgument(smt.Integer{Value: 42}, smt.SelfDatatypeArgument(nilValue, smt.EmptyMixedDatatypeArguments{}))
			x := smt.DatatypeConst(860, 2, 1, "xs")
			updated := smt.UpdateMixedIntDatatypeField(smt.MixedDatatypeFields(cons), x, smt.Integer{Value: 7})
			formula := smt.Equal{Left: x, Right: smt.ApplyMixedRecursiveDatatypeConstructor(cons, arguments)}
			result, ok := smt.Check(smt.Assert(1, smt.New(), formula)).(smt.Satisfiable)
			if !ok {
				b.Fatal("unexpected result")
			}
			if _, found := smt.DatatypeModelValue(860, 2, result.Value, updated); !found {
				b.Fatal("missing updated model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			nilDecl := context.MkConstructor("nil", "is-nil", nil, nil, nil)
			consDecl := context.MkConstructor("cons", "is-cons", []string{"head", "tail"}, []*z3.Sort{context.MkIntSort(), nil}, []uint{0, 0})
			listInt := context.MkDatatypeSort("PListInt", []*z3.Constructor{nilDecl, consDecl})
			nilValue := context.MkApp(context.GetDatatypeSortConstructor(listInt, 0))
			original := context.MkApp(context.GetDatatypeSortConstructor(listInt, 1), context.MkInt(42, context.MkIntSort()), nilValue)
			updated := context.MkApp(context.GetDatatypeSortConstructor(listInt, 1), context.MkInt(7, context.MkIntSort()), nilValue)
			x := context.MkConst(context.MkStringSymbol("xs"), listInt)
			solver := context.NewSolver()
			solver.Assert(context.MkEq(x, original))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, found := solver.Model().Eval(updated, true); !found {
				b.Fatal("missing updated model")
			}
		}
	})
}

func BenchmarkDatatypeValuedMatchCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			x := smt.DatatypeConst(870, 2, 1, "xs")
			red := smt.DatatypeConstructor(871, 2, 0, "red")
			blue := smt.DatatypeConstructor(871, 2, 1, "blue")
			matched := smt.If[smt.DatatypeSort]{
				Condition: smt.IsDatatypeConstructor(870, 2, 0, x),
				Then:      red,
				Else:      blue,
			}
			result, ok := smt.Check(smt.Assert(1, smt.New(), smt.Equal{Left: matched, Right: blue})).(smt.Satisfiable)
			if !ok {
				b.Fatal("unexpected result")
			}
			value, found := smt.DatatypeModelValue(870, 2, result.Value, x)
			if !found || value.ConstructorID != 1 {
				b.Fatal("missing selected constructor")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			nilDecl := context.MkConstructor("nil", "is-nil", nil, nil, nil)
			consDecl := context.MkConstructor("cons", "is-cons", []string{"head"}, []*z3.Sort{context.MkIntSort()}, []uint{0})
			listInt := context.MkDatatypeSort("PListInt", []*z3.Constructor{nilDecl, consDecl})
			redDecl := context.MkConstructor("red", "is-red", nil, nil, nil)
			blueDecl := context.MkConstructor("blue", "is-blue", nil, nil, nil)
			color := context.MkDatatypeSort("Color", []*z3.Constructor{redDecl, blueDecl})
			x := context.MkConst(context.MkStringSymbol("xs"), listInt)
			isNil := context.MkApp(context.GetDatatypeSortRecognizer(listInt, 0), x)
			red := context.MkApp(context.GetDatatypeSortConstructor(color, 0))
			blue := context.MkApp(context.GetDatatypeSortConstructor(color, 1))
			solver := context.NewSolver()
			// The pinned Go binding omits Z3_mk_ite. This disjunction is the
			// equivalent datatype-valued two-branch match constraint.
			solver.Assert(context.MkOr(
				context.MkAnd(isNil, context.MkEq(red, blue)),
				context.MkAnd(context.MkNot(isNil), context.MkEq(blue, blue)),
			))
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			if _, found := solver.Model().Eval(x, true); !found {
				b.Fatal("missing selected constructor")
			}
		}
	})
}

func BenchmarkBooleanDatatypeBranchingCold(b *testing.B) {
	b.Run("gosmt", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			red := smt.DatatypeConstructor(872, 2, 0, "red")
			blue := smt.DatatypeConstructor(872, 2, 1, "blue")
			x := smt.DatatypeConst(872, 2, 1, "x")
			isRed := smt.Equal{Left: x, Right: red}
			isBlue := smt.Equal{Left: x, Right: blue}
			formula := smt.And{Values: []smt.Term[smt.BoolSort]{
				smt.Or{Values: []smt.Term[smt.BoolSort]{isRed, isBlue}},
				smt.Not{Value: isRed},
			}}
			result, ok := smt.Check(smt.Assert(1, smt.New(), formula)).(smt.Satisfiable)
			if !ok {
				b.Fatal("unexpected result")
			}
			value, found := smt.DatatypeModelValue(872, 2, result.Value, x)
			if !found || value.ConstructorID != 1 {
				b.Fatal("missing selected model")
			}
			redValue, redFound := smt.BoolValue(result.Value, smt.IsDatatypeConstructor(872, 2, 0, x))
			blueValue, blueFound := smt.BoolValue(result.Value, smt.IsDatatypeConstructor(872, 2, 1, x))
			redConstructor, redConstructorFound := smt.DatatypeModelValue(872, 2, result.Value, red)
			blueConstructor, blueConstructorFound := smt.DatatypeModelValue(872, 2, result.Value, blue)
			if !redFound || redValue || !blueFound || !blueValue || !redConstructorFound || redConstructor.ConstructorID != 0 || !blueConstructorFound || blueConstructor.ConstructorID != 1 {
				b.Fatal("invalid Boolean branch model")
			}
		}
	})
	b.Run("z3", func(b *testing.B) {
		b.ReportAllocs()
		for i := 0; i < b.N; i++ {
			context := z3.NewContext()
			redDecl := context.MkConstructor("red", "is-red", nil, nil, nil)
			blueDecl := context.MkConstructor("blue", "is-blue", nil, nil, nil)
			color := context.MkDatatypeSort("Color", []*z3.Constructor{redDecl, blueDecl})
			red := context.MkApp(context.GetDatatypeSortConstructor(color, 0))
			blue := context.MkApp(context.GetDatatypeSortConstructor(color, 1))
			x := context.MkConst(context.MkStringSymbol("x"), color)
			isRed := context.MkEq(x, red)
			isBlue := context.MkEq(x, blue)
			recognizesRed := context.MkApp(context.GetDatatypeSortRecognizer(color, 0), x)
			recognizesBlue := context.MkApp(context.GetDatatypeSortRecognizer(color, 1), x)
			formula := context.MkAnd(
				context.MkOr(isRed, isBlue),
				context.MkNot(isRed),
			)
			solver := context.NewSolver()
			solver.Assert(formula)
			if solver.Check() != z3.Satisfiable {
				b.Fatal("unexpected result")
			}
			model := solver.Model()
			_, xFound := model.Eval(x, true)
			_, redFound := model.Eval(isRed, true)
			_, blueFound := model.Eval(isBlue, true)
			_, redConstructorFound := model.Eval(red, true)
			_, blueConstructorFound := model.Eval(blue, true)
			_, recognizesRedFound := model.Eval(recognizesRed, true)
			_, recognizesBlueFound := model.Eval(recognizesBlue, true)
			_, formulaFound := model.Eval(formula, true)
			if !xFound || !redFound || !blueFound || !redConstructorFound || !blueConstructorFound || !recognizesRedFound || !recognizesBlueFound || !formulaFound {
				b.Fatal("missing selected model")
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
			quotient, remainder := gosmt.DivInt64(x, -3), gosmt.ModInt64(x, -3)
			formula := gosmt.And(
				gosmt.EqInt(x, gosmt.IntVal(context, -7)),
				gosmt.EqInt(quotient, gosmt.IntVal(context, 3)),
				gosmt.EqInt(remainder, gosmt.IntVal(context, 2)),
			)
			result, ok := gosmt.Check(gosmt.Assert(1, gosmt.NewSolver(context), formula)).(gosmt.Sat)
			if !ok {
				b.Fatal("unexpected result")
			}
			if value, found := gosmt.EvalInt(result.Value, quotient); !found || value != 3 {
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
			negativeThree := context.MkInt(-3, intSort)
			quotient, remainder := context.MkDiv(x, negativeThree), context.MkMod(x, negativeThree)
			formula := context.MkAnd(
				context.MkEq(x, context.MkInt(-7, intSort)),
				context.MkEq(quotient, context.MkInt(3, intSort)),
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
