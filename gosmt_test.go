package gosmt

import (
	"testing"

	"goforge.dev/goplus/std/smt"
	"goforge.dev/goplus/std/smtlib"
	"goforge.dev/goplus/std/vec"
)

func narySelectorNames() vec.Vec[string] {
	return vec.Cons[string]{Head: "first", Tail: vec.Cons[string]{Head: "second", Tail: vec.Cons[string]{Head: "third", Tail: vec.Nil[string]{}}}}
}

func naryDatatypeExpressions(first, second, third DatatypeExpr) vec.Vec[DatatypeExpr] {
	return vec.Cons[DatatypeExpr]{Head: first, Tail: vec.Cons[DatatypeExpr]{Head: second, Tail: vec.Cons[DatatypeExpr]{Head: third, Tail: vec.Nil[DatatypeExpr]{}}}}
}

func TestContextIndexedBooleanSolve(t *testing.T) {
	context := NewContext(7)
	a := BoolConst(context, "a", 1)
	b := BoolConst(context, "b", 2)
	formula := And(Or(a, b), Not(a))
	result := Check(Assert(11, NewSolver(context), formula))
	sat, ok := result.(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if value, found := EvalBool(sat.Value, a); !found || value {
		t.Fatalf("a=(%v,%v)", value, found)
	}
	if value, found := EvalBool(sat.Value, b); !found || !value {
		t.Fatalf("b=(%v,%v)", value, found)
	}
}

func TestContextIndexedStringSolve(t *testing.T) {
	context := NewContext(8)
	x := StringConst(context, "x", 1)
	value := ConcatString(StringVal(context, "go"), StringVal(context, "forge"))
	formula := And(
		EqString(x, value),
		ContainsString(x, StringVal(context, "of")),
		HasPrefixString(x, StringVal(context, "go")),
		HasSuffixString(x, StringVal(context, "forge")),
		EqInt(LengthString(x), IntVal(context, 7)),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "goforge" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if length, found := EvalInt(result.Value, LengthString(x)); !found || length != 7 {
		t.Fatalf("length=(%d,%v)", length, found)
	}
}

func TestContextIndexedStringDisequality(t *testing.T) {
	context := NewContext(9)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	result, ok := Check(Assert(1, NewSolver(context), Not(EqString(x, y)))).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), Not(EqString(x, y)))))
	}
	left, leftOK := EvalString(result.Value, x)
	right, rightOK := EvalString(result.Value, y)
	if !leftOK || !rightOK || left == right {
		t.Fatalf("x=(%q,%v), y=(%q,%v)", left, leftOK, right, rightOK)
	}
}

func TestContextIndexedStringOperations(t *testing.T) {
	context := NewContext(10)
	value := StringVal(context, "a🙂bc🙂")
	at := AtString(value, IntVal(context, 1))
	substring := Substring(value, IntVal(context, 1), IntVal(context, 3))
	index := IndexOfString(value, StringVal(context, "🙂"), IntVal(context, 2))
	replaced := ReplaceString(value, StringVal(context, "🙂"), StringVal(context, "!"))
	formula := And(
		EqString(at, StringVal(context, "🙂")),
		EqString(substring, StringVal(context, "🙂bc")),
		EqInt(index, IntVal(context, 4)),
		EqString(replaced, StringVal(context, "a!bc🙂")),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	if actual, found := EvalString(result.Value, at); !found || actual != "🙂" {
		t.Fatalf("at=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, substring); !found || actual != "🙂bc" {
		t.Fatalf("substring=(%q,%v)", actual, found)
	}
	if actual, found := EvalInt(result.Value, index); !found || actual != 4 {
		t.Fatalf("index=(%d,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, replaced); !found || actual != "a!bc🙂" {
		t.Fatalf("replace=(%q,%v)", actual, found)
	}
}

func TestContextIndexedStringConversions(t *testing.T) {
	context := NewContext(11)
	huge, err := smt.ParseIntegerValue("123456789012345678901234567890")
	if err != nil {
		t.Fatal(err)
	}
	replaced := ReplaceAllString(StringVal(context, "aaaa"), StringVal(context, "aa"), StringVal(context, "b"))
	parsed := ToIntString(StringVal(context, huge.String()))
	rendered := FromIntString(IntValExact(context, huge))
	surrogate := FromCodeString(IntVal(context, 0xd800))
	formula := And(
		EqString(replaced, StringVal(context, "bb")),
		EqInt(parsed, IntValExact(context, huge)),
		EqString(rendered, StringVal(context, huge.String())),
		EqInt(ToCodeString(surrogate), IntVal(context, 0xd800)),
		IsDigitString(StringVal(context, "7")),
		Not(IsDigitString(StringVal(context, "٧"))),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	if actual, found := EvalIntExact(result.Value, parsed); !found || smt.CompareIntegerValue(actual, huge) != 0 {
		t.Fatalf("parsed=(%v,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, rendered); !found || actual != huge.String() {
		t.Fatalf("rendered=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, surrogate); !found || actual != string([]byte{0xed, 0xa0, 0x80}) {
		t.Fatalf("surrogate=(%q,%v)", actual, found)
	}
}

func TestContextIndexedStringRegularExpressions(t *testing.T) {
	context := NewContext(12)
	letter := RangeRegexString(StringVal(context, "a"), StringVal(context, "z"))
	suffix := StarRegexExpr(UnionRegexExpr(
		ToRegexString(StringVal(context, "-")),
		letter,
	))
	language := ConcatRegexExpr(ToRegexString(StringVal(context, "go")), suffix)
	formula := And(
		InRegexString(StringVal(context, "go-forge"), language),
		InRegexString(StringVal(context, ""), OptionalRegexExpr(ToRegexString(StringVal(context, "x")))),
		InRegexString(StringVal(context, "aaa"), LoopRegexExpr(2, 4, ToRegexString(StringVal(context, "a")))),
		Not(InRegexString(StringVal(context, "1"), IntersectRegexExpr(letter, AllCharStringRegex(context)))),
		InRegexString(StringVal(context, "🙂"), DifferenceRegexExpr(FullStringRegex(context), EmptyStringRegex(context))),
	)
	result := Check(Assert(1, NewSolver(context), formula))
	if _, ok := result.(Sat); !ok {
		t.Fatalf("result=%T", result)
	}
}

func TestContextIndexedSymbolicStringRegularExpressions(t *testing.T) {
	context := NewContext(13)
	x := StringConst(context, "x", 1)
	language := ConcatRegexExpr(
		ToRegexString(StringVal(context, "go-")),
		LoopRegexExpr(2, 4, RangeRegexString(StringVal(context, "a"), StringVal(context, "z"))),
	)
	result := Check(Assert(1, NewSolver(context), InRegexString(x, language)))
	sat, ok := result.(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if actual, found := EvalString(sat.Value, x); !found || actual != "go-aa" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}

	contradiction := And(
		EqString(x, StringVal(context, "a")),
		InRegexString(x, ToRegexString(StringVal(context, "b"))),
	)
	checked := Check(Assert(2, NewSolver(context), contradiction))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("contradiction=%T", checked)
	}
}

func TestContextIndexedInteractingStringRegularExpressions(t *testing.T) {
	context := NewContext(14)
	x := StringConst(context, "x", 1)
	a := ToRegexString(StringVal(context, "a"))
	b := ToRegexString(StringVal(context, "b"))
	c := ToRegexString(StringVal(context, "c"))
	formula := And(
		InRegexString(x, UnionRegexExpr(a, b)),
		InRegexString(x, UnionRegexExpr(b, c)),
		Not(InRegexString(x, a)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T (%#v)", checked, checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "b" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

}

func TestContextIndexedBooleanStringRegularExpressions(t *testing.T) {
	context := NewContext(15)
	x := StringConst(context, "x", 1)
	a := InRegexString(x, ToRegexString(StringVal(context, "a")))
	b := InRegexString(x, ToRegexString(StringVal(context, "b")))
	c := InRegexString(x, ToRegexString(StringVal(context, "c")))
	formula := And(
		Or(a, b),
		Not(a),
		ImpliesBool(b, Not(c)),
		IfBool(a, c, b),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "b" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

}

func TestContextIndexedSingleUnknownWordEquation(t *testing.T) {
	context := NewContext(16)
	x := StringConst(context, "x", 1)
	equation := EqString(
		ConcatString(StringVal(context, "go-"), x, StringVal(context, "!")),
		StringVal(context, "go-forge!"),
	)
	checked := Check(Assert(1, NewSolver(context), equation))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "forge" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, equation); !found || !valid {
		t.Fatalf("equation=(%v,%v)", valid, found)
	}
}

func TestContextIndexedUniquelyDelimitedWordEquation(t *testing.T) {
	context := NewContext(16)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	formula := EqString(
		ConcatString(
			StringVal(context, "["), x, StringVal(context, "]"),
			y, StringVal(context, "!"),
		),
		StringVal(context, "[go]forge!"),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "go" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "forge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	interacting := And(formula, EqString(x, StringVal(context, "go")))
	checked = Check(Assert(2, NewSolver(context), interacting))
	if _, ok := checked.(Sat); !ok {
		t.Fatalf("interacting result=%T", checked)
	}

	conflict := And(formula, EqString(x, StringVal(context, "not-go")))
	checked = Check(Assert(3, NewSolver(context), conflict))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("conflict result=%T", checked)
	}
}

func TestContextIndexedCanonicalBoundedWordEquation(t *testing.T) {
	context := NewContext(17)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	formula := EqString(ConcatString(x, y), StringVal(context, "forge"))
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "forge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	interacting := And(formula, EqString(x, StringVal(context, "for")))
	checked = Check(Assert(2, NewSolver(context), interacting))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("interacting result=%T", checked)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "ge" {
		t.Fatalf("interacting y=(%q,%v)", actual, found)
	}

	ambiguous := EqString(
		ConcatString(StringVal(context, "["), x, StringVal(context, "]"), y, StringVal(context, "!")),
		StringVal(context, "[a]b]c!"),
	)
	checked = Check(Assert(3, NewSolver(context), ambiguous))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("ambiguous result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("ambiguous x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "b]c" {
		t.Fatalf("ambiguous y=(%q,%v)", actual, found)
	}

	secondSplit := And(ambiguous, EqString(x, StringVal(context, "a]b")))
	checked = Check(Assert(4, NewSolver(context), secondSplit))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("second split result=%T", checked)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "c" {
		t.Fatalf("second split y=(%q,%v)", actual, found)
	}

	impossibleSplit := And(ambiguous, EqString(x, StringVal(context, "wrong")))
	checked = Check(Assert(5, NewSolver(context), impossibleSplit))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible split result=%T", checked)
	}
}

func TestContextIndexedRepeatedSymbolWordEquation(t *testing.T) {
	context := NewContext(18)
	x := StringConst(context, "x", 1)
	formula := EqString(
		ConcatString(x, StringVal(context, "-"), x),
		StringVal(context, "go-go"),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "go" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := EqString(
		ConcatString(x, StringVal(context, "-"), x),
		StringVal(context, "go-rust"),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}

	reversedBounds := And(
		Le(LengthString(x), IntVal(context, 3)),
		Lt(IntVal(context, 1), LengthString(x)),
	)
	checked = Check(Assert(3, NewSolver(context), reversedBounds))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("reversed bounds result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "aa" {
		t.Fatalf("reversed bounds x=(%q,%v)", actual, found)
	}
}

func TestContextIndexedWordEquationLengthInteraction(t *testing.T) {
	context := NewContext(19)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equation := EqString(ConcatString(x, y), StringVal(context, "forge"))
	formula := And(
		equation,
		EqInt(LengthString(x), IntVal(context, 3)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "for" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "ge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := And(
		equation,
		EqInt(LengthString(x), IntVal(context, 10)),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationLengthInequalityInteraction(t *testing.T) {
	context := NewContext(20)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equation := EqString(ConcatString(x, y), StringVal(context, "forge"))
	formula := And(
		equation,
		Lt(IntVal(context, 1), LengthString(x)),
		Le(LengthString(x), IntVal(context, 3)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "fo" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "rge" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := And(
		equation,
		Lt(IntVal(context, 5), LengthString(x)),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationRelationalLengthInteraction(t *testing.T) {
	context := NewContext(30)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equalLength := EqInt(LengthString(x), LengthString(y))
	equalFormula := And(
		EqString(ConcatString(x, y), StringVal(context, "abcd")),
		equalLength,
	)
	checked := Check(Assert(1, NewSolver(context), equalFormula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("equal result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "ab" {
		t.Fatalf("equal x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "cd" {
		t.Fatalf("equal y=(%q,%v)", actual, found)
	}

	ordered := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		Or(
			equalLength,
			Lt(LengthString(y), LengthString(x)),
		),
	)
	checked = Check(Assert(2, NewSolver(context), ordered))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("ordered result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "ab" {
		t.Fatalf("ordered x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "c" {
		t.Fatalf("ordered y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, ordered); !found || !valid {
		t.Fatalf("ordered formula=(%v,%v)", valid, found)
	}

	impossible := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		equalLength,
	)
	checked = Check(Assert(3, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationAffineLengthInteraction(t *testing.T) {
	context := NewContext(31)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	weighted := Add(
		ScaleInt64(2, LengthString(x)),
		LengthString(y),
	)
	formula := And(
		EqString(ConcatString(x, y), StringVal(context, "abcd")),
		EqInt(weighted, IntVal(context, 6)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "ab" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "cd" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	ordered := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		Lt(
			IntVal(context, 0),
			Sub(LengthString(x), LengthString(y)),
		),
	)
	checked = Check(Assert(2, NewSolver(context), ordered))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("ordered result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "ab" {
		t.Fatalf("ordered x=(%q,%v)", actual, found)
	}

	impossible := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		EqInt(Add(LengthString(x), LengthString(y)), IntVal(context, 4)),
	)
	checked = Check(Assert(3, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationIntegerStringOperationInteraction(t *testing.T) {
	context := NewContext(32)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	indexFormula := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		EqInt(
			IndexOfString(x, StringVal(context, "b"), IntVal(context, 0)),
			IntVal(context, 1),
		),
	)
	checked := Check(Assert(1, NewSolver(context), indexFormula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("index result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "ab" {
		t.Fatalf("index x=(%q,%v)", actual, found)
	}

	toIntegerFormula := And(
		EqString(ConcatString(x, y), StringVal(context, "12z")),
		EqInt(ToIntString(x), IntVal(context, 12)),
	)
	checked = Check(Assert(2, NewSolver(context), toIntegerFormula))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("to-int result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "12" {
		t.Fatalf("to-int x=(%q,%v)", actual, found)
	}

	toCodeFormula := And(
		EqString(ConcatString(x, y), StringVal(context, "a🙂")),
		EqInt(ToCodeString(x), IntVal(context, 97)),
	)
	checked = Check(Assert(3, NewSolver(context), toCodeFormula))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("to-code result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("to-code x=(%q,%v)", actual, found)
	}

	const digits = "1234567890123456789012345678901234567890"
	exact, err := smt.ParseIntegerValue(digits)
	if err != nil {
		t.Fatal(err)
	}
	wide := And(
		EqString(ConcatString(x, y), StringVal(context, digits+"!")),
		EqInt(ToIntString(x), IntValExact(context, exact)),
	)
	checked = Check(Assert(4, NewSolver(context), wide))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("wide result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != digits {
		t.Fatalf("wide x=(%q,%v)", actual, found)
	}

	impossible := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		EqInt(ToCodeString(x), IntVal(context, 122)),
	)
	checked = Check(Assert(5, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationDerivedStringOperationInteraction(t *testing.T) {
	context := NewContext(33)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	cases := []struct {
		name      string
		target    string
		predicate BoolExpr
		want      string
	}{
		{
			name:      "at",
			target:    "a🙂c",
			predicate: EqString(AtString(x, IntVal(context, 1)), StringVal(context, "🙂")),
			want:      "a🙂",
		},
		{
			name:   "substring",
			target: "abcd",
			predicate: EqString(
				Substring(x, IntVal(context, 1), IntVal(context, 2)),
				StringVal(context, "bc"),
			),
			want: "abc",
		},
		{
			name:   "replace",
			target: "abc",
			predicate: EqString(
				ReplaceString(x, StringVal(context, "a"), StringVal(context, "z")),
				StringVal(context, "z"),
			),
			want: "a",
		},
		{
			name:   "replace-all",
			target: "aab",
			predicate: EqString(
				ReplaceAllString(x, StringVal(context, "a"), StringVal(context, "z")),
				StringVal(context, "zz"),
			),
			want: "aa",
		},
		{
			name:   "from-int",
			target: "12x",
			predicate: EqString(
				AtString(x, IntVal(context, 0)),
				AtString(FromIntString(IntVal(context, 12)), IntVal(context, 0)),
			),
			want: "1",
		},
		{
			name:   "from-code",
			target: "a🙂",
			predicate: EqString(
				AtString(x, IntVal(context, 0)),
				FromCodeString(IntVal(context, 97)),
			),
			want: "a",
		},
	}
	for index, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			formula := And(
				EqString(ConcatString(x, y), StringVal(context, test.target)),
				test.predicate,
			)
			checked := Check(Assert(index+1, NewSolver(context), formula))
			result, ok := checked.(Sat)
			if !ok {
				t.Fatalf("result=%T", checked)
			}
			if actual, found := EvalString(result.Value, x); !found || actual != test.want {
				t.Fatalf("x=(%q,%v), want %q", actual, found, test.want)
			}
			if valid, found := EvalBool(result.Value, formula); !found || !valid {
				t.Fatalf("formula=(%v,%v)", valid, found)
			}
		})
	}

	impossible := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		EqString(AtString(x, IntVal(context, 4)), StringVal(context, "z")),
	)
	checked := Check(Assert(7, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedGroundIntegerSequenceEvaluation(t *testing.T) {
	context := NewContext(34)
	empty := EmptyIntSequence(context)
	first := UnitIntSequence(IntVal(context, 7))
	second := UnitIntSequence(IntVal(context, 11))
	sequence := ConcatIntSequence(first, empty, second)
	same := ConcatIntSequence(
		UnitIntSequence(IntVal(context, 7)),
		UnitIntSequence(IntVal(context, 11)),
	)
	different := UnitIntSequence(IntVal(context, 7))
	formula := And(
		EqIntSequence(sequence, same),
		Not(EqIntSequence(sequence, different)),
		EqInt(LengthIntSequence(sequence), IntVal(context, 2)),
		Lt(LengthIntSequence(empty), LengthIntSequence(sequence)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if length, found := EvalInt(result.Value, LengthIntSequence(sequence)); !found || length != 2 {
		t.Fatalf("length=(%d,%v)", length, found)
	}
	value, found := EvalIntSequence(result.Value, sequence)
	if !found || value.Len() != 2 {
		t.Fatalf("sequence len=(%d,%v)", value.Len(), found)
	}
	if element, ok := value.At(0); !ok || smt.CompareIntegerValue(element, smt.NewIntegerValue(7)) != 0 {
		t.Fatalf("first=(%v,%v)", element, ok)
	}
	if element, ok := value.At(1); !ok || smt.CompareIntegerValue(element, smt.NewIntegerValue(11)) != 0 {
		t.Fatalf("second=(%v,%v)", element, ok)
	}

	impossible := And(
		EqIntSequence(sequence, different),
		EqInt(LengthIntSequence(sequence), IntVal(context, 2)),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedGroundIntegerSequenceOperations(t *testing.T) {
	context := NewContext(35)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	sequence := ConcatIntSequence(unit(1), unit(2), unit(3), unit(2))
	pair := ConcatIntSequence(unit(2), unit(3))
	replaced := ConcatIntSequence(unit(1), unit(9), unit(2))
	formula := And(
		EqIntSequence(AtIntSequence(sequence, IntVal(context, 1)), unit(2)),
		EqIntSequence(
			ExtractIntSequence(sequence, IntVal(context, 1), IntVal(context, 2)),
			pair,
		),
		ContainsIntSequence(sequence, pair),
		HasPrefixIntSequence(sequence, ConcatIntSequence(unit(1), unit(2))),
		HasSuffixIntSequence(sequence, ConcatIntSequence(unit(3), unit(2))),
		EqInt(
			IndexOfIntSequence(sequence, unit(2), IntVal(context, 2)),
			IntVal(context, 3),
		),
		EqIntSequence(ReplaceIntSequence(sequence, pair, unit(9)), replaced),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	extracted := ExtractIntSequence(sequence, IntVal(context, 1), IntVal(context, 2))
	if value, found := EvalIntSequence(result.Value, extracted); !found || value.Len() != 2 {
		t.Fatalf("extract len=(%d,%v)", value.Len(), found)
	}
	if index, found := EvalInt(
		result.Value,
		IndexOfIntSequence(sequence, unit(2), IntVal(context, 2)),
	); !found || index != 3 {
		t.Fatalf("index=(%d,%v)", index, found)
	}

	impossible := And(
		ContainsIntSequence(sequence, pair),
		Not(HasSuffixIntSequence(sequence, unit(2))),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedGroundAssignedIntegerSequence(t *testing.T) {
	context := NewContext(36)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	ground := ConcatIntSequence(unit(1), unit(2), unit(3))
	formula := And(
		EqIntSequence(x, ground),
		ContainsIntSequence(x, ConcatIntSequence(unit(2), unit(3))),
		EqInt(LengthIntSequence(x), IntVal(context, 3)),
		EqIntSequence(AtIntSequence(x, IntVal(context, 1)), unit(2)),
		EqIntSequence(
			ReplaceIntSequence(x, unit(2), unit(9)),
			ConcatIntSequence(unit(1), unit(9), unit(3)),
		),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	value, found := EvalIntSequence(result.Value, x)
	if !found || value.Len() != 3 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if length, found := EvalInt(result.Value, LengthIntSequence(x)); !found || length != 3 {
		t.Fatalf("length=(%d,%v)", length, found)
	}

	conflicting := And(
		EqIntSequence(x, ground),
		EqIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
	)
	checked = Check(Assert(2, NewSolver(context), conflicting))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("conflicting result=%T", checked)
	}

	checked = Check(Assert(3, NewSolver(context), ContainsIntSequence(x, unit(2))))
	if result, ok := checked.(Sat); !ok {
		t.Fatalf("unbound result=%T", checked)
	} else if value, found := EvalIntSequence(result.Value, x); !found || value.Len() != 1 {
		t.Fatalf("unbound x len=(%d,%v)", value.Len(), found)
	}
}

func TestContextIndexedPositiveSymbolicIntegerSequence(t *testing.T) {
	context := NewContext(37)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	y := IntSequenceConst(context, "y", 2)
	formula := And(
		HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
		HasPrefixIntSequence(x, unit(1)),
		ContainsIntSequence(x, ConcatIntSequence(unit(3), unit(4))),
		HasSuffixIntSequence(x, ConcatIntSequence(unit(5), unit(6))),
		HasSuffixIntSequence(x, unit(6)),
		ContainsIntSequence(y, ConcatIntSequence(unit(9), unit(8))),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if value, found := EvalIntSequence(result.Value, x); !found || value.Len() != 6 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}
	if value, found := EvalIntSequence(result.Value, y); !found || value.Len() != 2 {
		t.Fatalf("y len=(%d,%v)", value.Len(), found)
	}

	incompatible := And(
		HasPrefixIntSequence(x, unit(1)),
		HasPrefixIntSequence(x, unit(2)),
	)
	if checked := Check(Assert(2, NewSolver(context), incompatible)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("incompatible result=%T", checked)
	}

	unsupported := Not(ContainsIntSequence(x, unit(1)))
	if checked := Check(Assert(3, NewSolver(context), unsupported)); func() bool {
		_, ok := checked.(Unknown)
		return ok
	}() == false {
		t.Fatalf("unsupported result=%T", checked)
	}
}

func TestContextIndexedExactLengthIntegerSequence(t *testing.T) {
	context := NewContext(38)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	formula := And(
		HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
		ContainsIntSequence(x, unit(3)),
		HasSuffixIntSequence(x, ConcatIntSequence(unit(5), unit(6))),
		EqInt(LengthIntSequence(x), IntVal(context, 6)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
	if value, found := EvalIntSequence(result.Value, x); !found || value.Len() != 6 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}

	overlap := And(
		HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
		HasSuffixIntSequence(x, ConcatIntSequence(unit(2), unit(3))),
		EqInt(LengthIntSequence(x), IntVal(context, 3)),
	)
	if checked := Check(Assert(2, NewSolver(context), overlap)); func() bool {
		_, ok := checked.(Sat)
		return ok
	}() == false {
		t.Fatalf("overlap result=%T", checked)
	}

	conflicting := And(
		EqInt(LengthIntSequence(x), IntVal(context, 2)),
		EqInt(LengthIntSequence(x), IntVal(context, 3)),
	)
	if checked := Check(Assert(3, NewSolver(context), conflicting)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}

	tooShort := And(
		ContainsIntSequence(x, ConcatIntSequence(unit(1), unit(2), unit(3))),
		EqInt(LengthIntSequence(x), IntVal(context, 2)),
	)
	if checked := Check(Assert(4, NewSolver(context), tooShort)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("too-short result=%T", checked)
	}
}

func TestContextIndexedRelationalLengthIntegerSequence(t *testing.T) {
	context := NewContext(39)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	formula := And(
		HasPrefixIntSequence(x, unit(1)),
		ContainsIntSequence(x, unit(2)),
		HasSuffixIntSequence(x, unit(3)),
		Le(IntVal(context, 3), LengthIntSequence(x)),
		Le(LengthIntSequence(x), IntVal(context, 5)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if value, found := EvalIntSequence(result.Value, x); !found || value.Len() < 3 || value.Len() > 5 {
		t.Fatalf("x len=(%d,%v)", value.Len(), found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	strict := Lt(IntVal(context, 5), LengthIntSequence(x))
	strictResult, ok := Check(Assert(2, NewSolver(context), strict)).(Sat)
	if !ok {
		t.Fatal("strict lower bound must be satisfiable")
	}
	if value, found := EvalIntSequence(strictResult.Value, x); !found || value.Len() != 6 {
		t.Fatalf("strict len=(%d,%v)", value.Len(), found)
	}

	conflicting := And(
		Le(IntVal(context, 4), LengthIntSequence(x)),
		Le(LengthIntSequence(x), IntVal(context, 3)),
	)
	if checked := Check(Assert(3, NewSolver(context), conflicting)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}
}

func TestContextIndexedAffineLengthIntegerSequence(t *testing.T) {
	context := NewContext(40)
	x := IntSequenceConst(context, "x", 1)
	length := LengthIntSequence(x)
	twicePlusOne := Add(ScaleInt64(2, length), IntVal(context, 1))
	exact := EqInt(twicePlusOne, IntVal(context, 7))
	result, ok := Check(Assert(1, NewSolver(context), exact)).(Sat)
	if !ok {
		t.Fatal("affine equality must be satisfiable")
	}
	if value, found := EvalIntSequence(result.Value, x); !found || value.Len() != 3 {
		t.Fatalf("exact len=(%d,%v)", value.Len(), found)
	}

	nondivisible := EqInt(ScaleInt64(2, length), IntVal(context, 3))
	if checked := Check(Assert(2, NewSolver(context), nondivisible)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("nondivisible result=%T", checked)
	}

	bounded := And(
		Le(twicePlusOne, IntVal(context, 9)),
		Lt(
			Add(ScaleInt64(-2, length), IntVal(context, 1)),
			IntVal(context, -4),
		),
	)
	boundedResult, ok := Check(Assert(3, NewSolver(context), bounded)).(Sat)
	if !ok {
		t.Fatal("affine bounds must be satisfiable")
	}
	if value, found := EvalIntSequence(boundedResult.Value, x); !found ||
		value.Len() < 3 || value.Len() > 4 {
		t.Fatalf("bounded len=(%d,%v)", value.Len(), found)
	}
}

func TestContextIndexedIntegerSequenceEqualityClasses(t *testing.T) {
	context := NewContext(41)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	y := IntSequenceConst(context, "y", 2)
	z := IntSequenceConst(context, "z", 3)
	formula := And(
		EqIntSequence(x, y),
		EqIntSequence(y, z),
		HasPrefixIntSequence(x, unit(1)),
		ContainsIntSequence(y, unit(2)),
		HasSuffixIntSequence(z, unit(3)),
		EqInt(LengthIntSequence(y), IntVal(context, 3)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for name, expression := range map[string]IntSequenceExpr{
		"x": x,
		"y": y,
		"z": z,
	} {
		value, found := EvalIntSequence(result.Value, expression)
		if !found || value.Len() != 3 {
			t.Fatalf("%s len=(%d,%v)", name, value.Len(), found)
		}
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	ground := ConcatIntSequence(unit(4), unit(5))
	assigned := And(EqIntSequence(x, y), EqIntSequence(y, ground))
	assignedResult, ok := Check(Assert(2, NewSolver(context), assigned)).(Sat)
	if !ok {
		t.Fatalf("assigned result=%T", Check(Assert(2, NewSolver(context), assigned)))
	}
	if value, found := EvalIntSequence(assignedResult.Value, x); !found || value.Len() != 2 {
		t.Fatalf("assigned x len=(%d,%v)", value.Len(), found)
	}

	conflicting := And(
		EqIntSequence(x, y),
		EqIntSequence(x, unit(1)),
		EqIntSequence(y, unit(2)),
	)
	if checked := Check(Assert(3, NewSolver(context), conflicting)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}
}

func TestContextIndexedTwoSymbolAffineIntegerSequenceLengths(t *testing.T) {
	context := NewContext(42)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	y := IntSequenceConst(context, "y", 2)
	relation := EqInt(
		Add(ScaleInt64(2, LengthIntSequence(x)), LengthIntSequence(y)),
		IntVal(context, 7),
	)
	formula := And(
		relation,
		HasPrefixIntSequence(x, unit(1)),
		HasSuffixIntSequence(y, unit(3)),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	xValue, xFound := EvalIntSequence(result.Value, x)
	yValue, yFound := EvalIntSequence(result.Value, y)
	if !xFound || !yFound || 2*xValue.Len()+yValue.Len() != 7 {
		t.Fatalf("lengths=(%d,%v)/(%d,%v)", xValue.Len(), xFound, yValue.Len(), yFound)
	}

	conflicting := And(
		relation,
		EqInt(LengthIntSequence(x), IntVal(context, 2)),
		EqInt(LengthIntSequence(y), IntVal(context, 2)),
	)
	if checked := Check(Assert(2, NewSolver(context), conflicting)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}
}

func TestContextIndexedThreeSymbolAffineIntegerSequenceLengths(t *testing.T) {
	context := NewContext(43)
	unit := func(value int64) IntSequenceExpr {
		return UnitIntSequence(IntVal(context, value))
	}
	x := IntSequenceConst(context, "x", 1)
	y := IntSequenceConst(context, "y", 2)
	z := IntSequenceConst(context, "z", 3)
	relation := EqInt(
		Add(
			ScaleInt64(2, LengthIntSequence(x)),
			LengthIntSequence(y),
			LengthIntSequence(z),
		),
		IntVal(context, 7),
	)
	formula := And(
		relation,
		HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
		ContainsIntSequence(y, unit(3)),
		HasSuffixIntSequence(z, ConcatIntSequence(unit(4), unit(5))),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	xValue, xFound := EvalIntSequence(result.Value, x)
	yValue, yFound := EvalIntSequence(result.Value, y)
	zValue, zFound := EvalIntSequence(result.Value, z)
	if !xFound || !yFound || !zFound ||
		2*xValue.Len()+yValue.Len()+zValue.Len() != 7 {
		t.Fatalf(
			"lengths=(%d,%v)/(%d,%v)/(%d,%v)",
			xValue.Len(), xFound, yValue.Len(), yFound, zValue.Len(), zFound,
		)
	}

	conflicting := And(
		relation,
		EqInt(LengthIntSequence(x), IntVal(context, 2)),
		EqInt(LengthIntSequence(y), IntVal(context, 1)),
		EqInt(LengthIntSequence(z), IntVal(context, 1)),
	)
	if checked := Check(Assert(2, NewSolver(context), conflicting)); func() bool {
		_, ok := checked.(Unsat)
		return ok
	}() == false {
		t.Fatalf("conflicting result=%T", checked)
	}
}

func TestContextIndexedMultipleWordEquationInteraction(t *testing.T) {
	context := NewContext(21)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	z := StringConst(context, "z", 3)
	first := EqString(ConcatString(x, y), StringVal(context, "abc"))
	second := EqString(
		ConcatString(x, StringVal(context, "-"), z),
		StringVal(context, "a-tail"),
	)
	formula := And(first, second)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for _, item := range []struct {
		expression StringExpr
		expected   string
	}{
		{x, "a"},
		{y, "bc"},
		{z, "tail"},
	} {
		if actual, found := EvalString(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := And(
		first,
		EqString(ConcatString(x, x), StringVal(context, "zz")),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedEightWordEquationInteraction(t *testing.T) {
	context := NewContext(27)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	z := StringConst(context, "z", 3)
	w := StringConst(context, "w", 4)
	formula := And(
		EqString(ConcatString(x, y), StringVal(context, "abc")),
		EqString(ConcatString(x, StringVal(context, "-"), z), StringVal(context, "a-tail")),
		EqString(ConcatString(y, w), StringVal(context, "bc!")),
		EqString(ConcatString(z, w), StringVal(context, "tail!")),
		EqString(ConcatString(StringVal(context, "<"), x, y), StringVal(context, "<abc")),
		EqString(ConcatString(x, y, StringVal(context, ">")), StringVal(context, "abc>")),
		EqString(ConcatString(StringVal(context, "["), z, w), StringVal(context, "[tail!")),
		EqString(ConcatString(z, w, StringVal(context, "]")), StringVal(context, "tail!]")),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for _, item := range []struct {
		expression StringExpr
		expected   string
	}{
		{x, "a"},
		{y, "bc"},
		{z, "tail"},
		{w, "!"},
	} {
		if actual, found := EvalString(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}

func TestContextIndexedOverflowWordEquationInteraction(t *testing.T) {
	context := NewContext(28)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	z := StringConst(context, "z", 3)
	w := StringConst(context, "w", 4)
	stringValue := func(value string) StringExpr {
		return StringVal(context, value)
	}
	formula := And(
		EqString(ConcatString(x, y), stringValue("abc")),
		EqString(ConcatString(x, stringValue("-"), z), stringValue("a-tail")),
		EqString(ConcatString(y, w), stringValue("bc!")),
		EqString(ConcatString(z, w), stringValue("tail!")),
		EqString(ConcatString(stringValue("<"), x, y), stringValue("<abc")),
		EqString(ConcatString(x, y, stringValue(">")), stringValue("abc>")),
		EqString(ConcatString(stringValue("["), z, w), stringValue("[tail!")),
		EqString(ConcatString(z, w, stringValue("]")), stringValue("tail!]")),
		EqString(ConcatString(stringValue("<"), x, stringValue("-"), z), stringValue("<a-tail")),
		EqString(ConcatString(x, stringValue("-"), z, stringValue(">")), stringValue("a-tail>")),
		EqString(ConcatString(stringValue("("), y, w), stringValue("(bc!")),
		EqString(ConcatString(z, w, stringValue(")")), stringValue("tail!)")),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	for _, item := range []struct {
		expression StringExpr
		expected   string
	}{
		{x, "a"},
		{y, "bc"},
		{z, "tail"},
		{w, "!"},
	} {
		if actual, found := EvalString(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}

func TestContextIndexedOverflowWordEquationConstraintInteraction(t *testing.T) {
	context := NewContext(29)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	z := StringConst(context, "z", 3)
	w := StringConst(context, "w", 4)
	v := StringConst(context, "v", 5)
	stringValue := func(value string) StringExpr {
		return StringVal(context, value)
	}
	a := ToRegexString(stringValue("a"))
	notA := ToRegexString(stringValue("z"))
	formula := And(
		EqString(
			ConcatString(x, stringValue("-"), y, stringValue("-"), z, stringValue("-"), w),
			stringValue("a-b-c-d"),
		),
		EqString(ConcatString(v, stringValue("!")), stringValue("e!")),
		EqInt(LengthString(x), IntVal(context, 1)),
		EqInt(LengthString(y), IntVal(context, 1)),
		EqInt(LengthString(z), IntVal(context, 1)),
		EqInt(LengthString(w), IntVal(context, 1)),
		EqInt(LengthString(v), IntVal(context, 1)),
		InRegexString(x, a),
		InRegexString(x, UnionRegexExpr(a, notA)),
		InRegexString(x, IntersectRegexExpr(FullStringRegex(context), a)),
		InRegexString(x, DifferenceRegexExpr(a, notA)),
		InRegexString(x, ComplementRegexExpr(notA)),
		ContainsString(x, stringValue("a")),
		HasPrefixString(x, stringValue("a")),
		HasSuffixString(x, stringValue("a")),
		Not(EqString(x, stringValue("z"))),
		Not(EqString(x, stringValue(""))),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("overflow constraints result=%T (%#v)", checked, checked)
	}
	for _, item := range []struct {
		expression StringExpr
		expected   string
	}{
		{x, "a"},
		{y, "b"},
		{z, "c"},
		{w, "d"},
		{v, "e"},
	} {
		if actual, found := EvalString(result.Value, item.expression); !found || actual != item.expected {
			t.Fatalf("value=(%q,%v), want=%q", actual, found, item.expected)
		}
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}
}

func TestContextIndexedWordEquationRegexInteraction(t *testing.T) {
	context := NewContext(22)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equation := EqString(ConcatString(x, y), StringVal(context, "abc"))
	language := UnionRegexExpr(
		ToRegexString(StringVal(context, "a")),
		ToRegexString(StringVal(context, "ab")),
	)
	formula := And(equation, InRegexString(x, language))
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "bc" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	negativeLiteral := And(
		equation,
		Not(InRegexString(x, ToRegexString(StringVal(context, "")))),
	)
	checked = Check(Assert(2, NewSolver(context), negativeLiteral))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("negative result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("negative x=(%q,%v)", actual, found)
	}

	impossible := And(
		equation,
		InRegexString(x, ToRegexString(StringVal(context, "z"))),
	)
	checked = Check(Assert(3, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationBooleanRegexInteraction(t *testing.T) {
	context := NewContext(23)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equation := EqString(ConcatString(x, y), StringVal(context, "abc"))
	choice := Or(
		InRegexString(x, RangeRegexString(StringVal(context, "z"), StringVal(context, "z"))),
		InRegexString(x, RangeRegexString(StringVal(context, "a"), StringVal(context, "a"))),
	)
	formula := And(equation, choice)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "bc" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := And(
		equation,
		Or(
			InRegexString(x, RangeRegexString(StringVal(context, "z"), StringVal(context, "z"))),
			InRegexString(x, RangeRegexString(StringVal(context, "q"), StringVal(context, "q"))),
		),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationStringDisequalityInteraction(t *testing.T) {
	context := NewContext(24)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equation := EqString(ConcatString(x, y), StringVal(context, "ab"))
	formula := And(
		equation,
		Not(EqString(x, StringVal(context, ""))),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "b" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	choice := And(
		equation,
		Or(
			EqString(x, StringVal(context, "z")),
			EqString(x, StringVal(context, "a")),
		),
	)
	checked = Check(Assert(2, NewSolver(context), choice))
	result, ok = checked.(Sat)
	if !ok {
		t.Fatalf("choice result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "a" {
		t.Fatalf("choice x=(%q,%v)", actual, found)
	}

	impossible := And(
		EqString(ConcatString(x, y), StringVal(context, "")),
		Not(EqString(x, StringVal(context, ""))),
	)
	checked = Check(Assert(3, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func TestContextIndexedWordEquationStringPredicateInteraction(t *testing.T) {
	context := NewContext(25)
	x := StringConst(context, "x", 1)
	y := StringConst(context, "y", 2)
	equation := EqString(ConcatString(x, y), StringVal(context, "abc"))
	formula := And(
		equation,
		ContainsString(x, StringVal(context, "b")),
		HasPrefixString(x, StringVal(context, "a")),
	)
	checked := Check(Assert(1, NewSolver(context), formula))
	result, ok := checked.(Sat)
	if !ok {
		t.Fatalf("result=%T", checked)
	}
	if actual, found := EvalString(result.Value, x); !found || actual != "ab" {
		t.Fatalf("x=(%q,%v)", actual, found)
	}
	if actual, found := EvalString(result.Value, y); !found || actual != "c" {
		t.Fatalf("y=(%q,%v)", actual, found)
	}
	if valid, found := EvalBool(result.Value, formula); !found || !valid {
		t.Fatalf("formula=(%v,%v)", valid, found)
	}

	impossible := And(
		equation,
		ContainsString(x, StringVal(context, "z")),
	)
	checked = Check(Assert(2, NewSolver(context), impossible))
	if _, ok := checked.(Unsat); !ok {
		t.Fatalf("impossible result=%T", checked)
	}
}

func BenchmarkContextIndexedStringSolve(b *testing.B) {
	context := NewContext(8)
	x := StringConst(context, "x", 1)
	formula := And(
		EqString(x, ConcatString(StringVal(context, "go-"), StringVal(context, "forge"))),
		EqInt(LengthString(x), IntVal(context, 8)),
		ContainsString(x, StringVal(context, "-")),
		HasPrefixString(x, StringVal(context, "go")),
		HasSuffixString(x, StringVal(context, "forge")),
	)
	b.ReportAllocs()
	for index := 0; index < b.N; index++ {
		if _, ok := Check(Assert(index+1, NewSolver(context), formula)).(Sat); !ok {
			b.Fatal("expected satisfiable string workload")
		}
	}
}

func TestBooleanInlineCNFFallsBackForWideSymbolIDs(t *testing.T) {
	context := NewContext(101)
	a := BoolConst(context, "a", 100)
	b := BoolConst(context, "b", 101)
	formula := And(Or(a, b), Not(a))
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	if value, found := EvalBool(result.Value, a); !found || value {
		t.Fatalf("a=(%v,%v)", value, found)
	}
	if value, found := EvalBool(result.Value, b); !found || !value {
		t.Fatalf("b=(%v,%v)", value, found)
	}
}

func TestUnsatIsExhaustive(t *testing.T) {
	context := NewContext(9)
	a := BoolConst(context, "a", 1)
	result := Check(Assert(1, NewSolver(context), And(a, Not(a))))
	if _, ok := result.(Unsat); !ok {
		t.Fatalf("result=%T", result)
	}
}

func TestBooleanEquality(t *testing.T) {
	context := NewContext(91)
	value := BoolConst(context, "value", 1)
	result, ok := Check(Assert(1, NewSolver(context), EqBool(value, BoolValue(context, true)))).(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if evaluated, found := EvalBool(result.Value, value); !found || !evaluated {
		t.Fatalf("value=(%v,%v)", evaluated, found)
	}
}

func TestAssumptionUnsatCore(t *testing.T) {
	context := NewContext(3)
	a := BoolConst(context, "a", 1)
	b := BoolConst(context, "b", 2)
	solver := Assert(1, NewSolver(context), Or(a, b))
	result, ok := CheckAssuming(solver, Not(a), Not(b), BoolValue(context, true)).(AssumptionUnsat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if len(result.Indices) != 2 || result.Indices[0] != 0 || result.Indices[1] != 1 {
		t.Fatalf("core=%v", result.Indices)
	}
}

func TestIntegerDifferenceLogicModel(t *testing.T) {
	context := NewContext(4)
	x := IntConst(context, "x", 1)
	y := IntConst(context, "y", 2)
	formula := And(
		Le(Sub(x, y), IntVal(context, 3)),
		Le(y, IntVal(context, 2)),
		Le(IntVal(context, 4), x),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	xValue, xFound := EvalInt(result.Value, x)
	yValue, yFound := EvalInt(result.Value, y)
	if !xFound || !yFound || xValue-yValue > 3 || yValue > 2 || xValue < 4 {
		t.Fatalf("model x=%d/%v y=%d/%v", xValue, xFound, yValue, yFound)
	}
}

func TestLinearIntegerArithmeticModelAndIntegrality(t *testing.T) {
	context := NewContext(104)
	x := IntConst(context, "x", 1)
	y := IntConst(context, "y", 2)
	formula := And(
		Le(Add(x, y), IntVal(context, 10)),
		Le(IntVal(context, 11), Add(ScaleInt64(2, x), y)),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	xValue, xOK := EvalIntExact(result.Value, x)
	yValue, yOK := EvalIntExact(result.Value, y)
	if !xOK || !yOK || smt.CompareIntegerValue(smt.AddIntegerValue(xValue, yValue), smt.NewIntegerValue(10)) > 0 || smt.CompareIntegerValue(smt.AddIntegerValue(smt.MultiplyIntegerValue(smt.NewIntegerValue(2), xValue), yValue), smt.NewIntegerValue(11)) < 0 {
		t.Fatalf("invalid model x=%v/%v y=%v/%v", xValue, xOK, yValue, yOK)
	}

	twoX := ScaleInt64(2, x)
	integralityResult := Check(Assert(2, NewSolver(context), EqInt(twoX, IntVal(context, 1))))
	if _, ok := integralityResult.(Unsat); !ok {
		t.Fatalf("integrality result=%T", integralityResult)
	}
}

func TestBooleanLinearIntegerArithmetic(t *testing.T) {
	context := NewContext(106)
	x := IntConst(context, "x", 1)
	one, two := IntVal(context, 1), IntVal(context, 2)
	formula := And(
		Or(EqInt(x, one), EqInt(x, two)),
		NeInt(x, one),
		ImpliesBool(EqInt(x, two), Lt(IntVal(context, 0), x)),
		IffBool(EqInt(x, two), Le(two, x)),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	value, found := EvalInt(result.Value, x)
	if !found || value != 2 {
		t.Fatalf("x=(%d,%v)", value, found)
	}
}

func TestIntegerEuclideanDivisionAndModulo(t *testing.T) {
	context := NewContext(108)
	x := IntConst(context, "x", 1)
	quotient, remainder := DivInt64(x, 3), ModInt64(x, 3)
	formula := And(
		EqInt(x, IntVal(context, -7)),
		EqInt(quotient, IntVal(context, -3)),
		EqInt(remainder, IntVal(context, 2)),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if value, found := EvalInt(result.Value, quotient); !found || value != -3 {
		t.Fatalf("quotient=(%d,%v)", value, found)
	}
	if value, found := EvalInt(result.Value, remainder); !found || value != 2 {
		t.Fatalf("remainder=(%d,%v)", value, found)
	}
}

func TestIntegerEuclideanDivisionNegativeConstantDivisor(t *testing.T) {
	context := NewContext(110)
	x := IntConst(context, "x", 1)
	quotient, remainder := DivInt64(x, -3), ModInt64(x, -3)
	formula := And(
		EqInt(x, IntVal(context, -7)),
		EqInt(quotient, IntVal(context, 3)),
		EqInt(remainder, IntVal(context, 2)),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	if value, found := EvalInt(result.Value, quotient); !found || value != 3 {
		t.Fatalf("quotient=(%d,%v)", value, found)
	}
	if value, found := EvalInt(result.Value, remainder); !found || value != 2 {
		t.Fatalf("remainder=(%d,%v)", value, found)
	}
}

func TestArbitraryPrecisionIntegerDifferenceLogic(t *testing.T) {
	context := NewContext(5)
	lower, err := ParseInteger("1267650600228229401496703205376")
	if err != nil {
		t.Fatal(err)
	}
	upper, err := ParseInteger("1267650600228229401496703205377")
	if err != nil {
		t.Fatal(err)
	}
	x := IntConst(context, "wide", 1)
	formula := And(Le(IntValExact(context, lower), x), Le(x, IntValExact(context, upper)))
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	value, found := EvalIntExact(result.Value, x)
	if !found || value.String() < lower.String() || value.String() > upper.String() {
		t.Fatalf("value=%s/%v", value.String(), found)
	}
}

func TestSMTLibArbitraryPrecisionIntegerModel(t *testing.T) {
	script := `(declare-const x Int)
(assert (= x 1267650600228229401496703205376))
(check-sat)
(get-value (x))`
	executed, ok := ExecuteSMTLib(script).(smtlib.Executed)
	if !ok || len(executed.Responses) != 4 {
		t.Fatalf("result=%#v", executed)
	}
	values, ok := executed.Responses[3].(smtlib.ValuesAvailable)
	if !ok || len(values.Values) != 1 {
		t.Fatalf("values=%#v", executed.Responses[3])
	}
	value, ok := values.Values[0].(smtlib.ArbitraryIntegerValue)
	if !ok || value.Value.String() != "1267650600228229401496703205376" {
		t.Fatalf("value=%#v", values.Values[0])
	}
}

func TestSMTLibSyntaxBoundary(t *testing.T) {
	result, ok := ParseSMTLib(`(set-logic QF_IDL) (declare-const x Int) (assert (<= x 3)) (check-sat)`).(smtlib.Parsed)
	if !ok || len(result.Commands) != 4 {
		t.Fatalf("result=%#v", result)
	}
}

func TestSMTLibExecutionBoundary(t *testing.T) {
	result, ok := ExecuteSMTLib(`(declare-const a Bool) (assert a) (check-sat) (get-value (a))`).(smtlib.Executed)
	if !ok {
		t.Fatalf("result=%#v", ExecuteSMTLib(`(check-sat)`))
	}
	if _, ok := result.Responses[2].(smtlib.Satisfiable); !ok {
		t.Fatalf("check=%T", result.Responses[2])
	}
}

func TestGroundUninterpretedFunctionCongruence(t *testing.T) {
	context := NewContext(12)
	a := UninterpretedConst(1, context, "a", 1)
	b := UninterpretedConst(1, context, "b", 2)
	f := DeclareUnary(1, 2, context, "f", 1)
	formula := And(
		EqUninterpreted(a, b),
		Not(EqUninterpreted(ApplyUninterpreted(f, a), ApplyUninterpreted(f, b))),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestFiniteEnumerationDatatypeModel(t *testing.T) {
	context := NewContext(111)
	red := DatatypeConstructor(1, 3, 0, context, "red")
	green := DatatypeConstructor(1, 3, 1, context, "green")
	x := DatatypeConst(1, 3, context, "x", 1)
	formula := And(Not(EqDatatype(x, red)), IsDatatypeConstructor(1, 3, 1, x))
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	value, found := EvalDatatype(1, 3, result.Value, x)
	if !found || value.ConstructorID != 1 {
		t.Fatalf("x=(%#v,%v)", value, found)
	}
	if direct, found := EvalDatatype(1, 3, result.Value, green); !found || direct.ConstructorID != 1 || direct.ConstructorName != "green" {
		t.Fatalf("green=(%#v,%v)", direct, found)
	}
}

func TestRecursiveUnaryDatatypeConstructorSelectorAndModel(t *testing.T) {
	context := NewContext(151)
	zero := DatatypeConstructor(81, 2, 0, context, "zero")
	succ := DeclareRecursiveDatatypeConstructor(81, 2, 1, context, "succ", "pred")
	x := DatatypeConst(81, 2, context, "x", 1)
	one := ApplyRecursiveDatatypeConstructor(succ, zero)
	two := ApplyRecursiveDatatypeConstructor(succ, one)
	formula := And(EqDatatype(x, two), EqDatatype(SelectRecursiveDatatypeConstructor(succ, x), one), IsRecursiveDatatypeConstructor(succ, x))
	solver := Assert(1, NewSolver(context), formula)
	result, ok := Check(solver).(Sat)
	if !ok {
		t.Fatalf("result=%#v", Check(solver))
	}
	value, found := EvalDatatype(81, 2, result.Value, x)
	if !found || value.ConstructorName != "succ" || value.Child == nil || value.Child.ConstructorName != "succ" || value.Child.Child == nil || value.Child.Child.ConstructorName != "zero" {
		t.Fatalf("value=%#v found=%v", value, found)
	}
	predecessor, found := EvalDatatype(81, 2, result.Value, SelectRecursiveDatatypeConstructor(succ, x))
	if !found || predecessor.ConstructorName != "succ" || predecessor.Child == nil || predecessor.Child.ConstructorName != "zero" {
		t.Fatalf("predecessor=%#v found=%v", predecessor, found)
	}
}

func TestRecursiveUnaryDatatypeInjectivityAndAcyclicity(t *testing.T) {
	context := NewContext(152)
	succ := DeclareRecursiveDatatypeConstructor(82, 2, 1, context, "succ", "pred")
	x := DatatypeConst(82, 2, context, "x", 1)
	y := DatatypeConst(82, 2, context, "y", 2)
	injective := And(EqDatatype(ApplyRecursiveDatatypeConstructor(succ, x), ApplyRecursiveDatatypeConstructor(succ, y)), Not(EqDatatype(x, y)))
	if result := Check(Assert(1, NewSolver(context), injective)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("injectivity result=%#v", result)
	}
	cyclic := EqDatatype(x, ApplyRecursiveDatatypeConstructor(succ, x))
	if result := Check(Assert(2, NewSolver(context), cyclic)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("acyclicity result=%#v", result)
	}
}

func TestBinaryRecursiveDatatypeConstructorSelectorsAndModel(t *testing.T) {
	context := NewContext(154)
	leaf := DatatypeConstructor(83, 2, 0, context, "leaf")
	node := DeclareBinaryRecursiveDatatypeConstructor(83, 2, 1, context, "node", "left", "right")
	branch := ApplyBinaryRecursiveDatatypeConstructor(node, leaf, leaf)
	tree := ApplyBinaryRecursiveDatatypeConstructor(node, branch, leaf)
	x := DatatypeConst(83, 2, context, "x", 1)
	formula := And(
		EqDatatype(x, tree),
		EqDatatype(SelectBinaryRecursiveDatatypeConstructor(FirstDatatypeField(), node, x), branch),
		EqDatatype(SelectBinaryRecursiveDatatypeConstructor(SecondDatatypeField(), node, x), leaf),
		IsBinaryRecursiveDatatypeConstructor(node, x),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%#v", Check(Assert(1, NewSolver(context), formula)))
	}
	value, found := EvalDatatype(83, 2, result.Value, x)
	if !found || value.ConstructorID != 1 || value.Child == nil || value.SecondChild == nil || value.Child.ConstructorID != 1 || value.Child.Child == nil || value.Child.SecondChild == nil || value.SecondChild.ConstructorID != 0 {
		t.Fatalf("value=%#v found=%v", value, found)
	}
}

func TestBinaryRecursiveDatatypeInjectivityAndAcyclicity(t *testing.T) {
	context := NewContext(155)
	leaf := DatatypeConstructor(84, 2, 0, context, "leaf")
	node := DeclareBinaryRecursiveDatatypeConstructor(84, 2, 1, context, "node", "left", "right")
	x := DatatypeConst(84, 2, context, "x", 1)
	y := DatatypeConst(84, 2, context, "y", 2)
	firstConflict := And(EqDatatype(ApplyBinaryRecursiveDatatypeConstructor(node, x, leaf), ApplyBinaryRecursiveDatatypeConstructor(node, y, leaf)), Not(EqDatatype(x, y)))
	if result := Check(Assert(1, NewSolver(context), firstConflict)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("first-field injectivity result=%#v", result)
	}
	secondConflict := And(EqDatatype(ApplyBinaryRecursiveDatatypeConstructor(node, leaf, x), ApplyBinaryRecursiveDatatypeConstructor(node, leaf, y)), Not(EqDatatype(x, y)))
	if result := Check(Assert(2, NewSolver(context), secondConflict)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("second-field injectivity result=%#v", result)
	}
	cycle := EqDatatype(x, ApplyBinaryRecursiveDatatypeConstructor(node, leaf, x))
	if result := Check(Assert(3, NewSolver(context), cycle)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("acyclicity result=%#v", result)
	}
}

func TestNaryRecursiveDatatypeConstructorSelectorsAndModel(t *testing.T) {
	context := NewContext(86)
	leaf := DatatypeConstructor(86, 2, 0, context, "leaf")
	branch := DeclareNaryRecursiveDatatypeConstructor(86, 2, 1, 3, context, "branch", narySelectorNames())
	nested := ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(leaf, leaf, leaf))
	tree := ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(leaf, nested, leaf))
	x := DatatypeConst(86, 2, context, "x", 1)
	formula := And(
		EqDatatype(x, tree),
		EqDatatype(SelectNaryRecursiveDatatypeConstructor(vec.Zero{}, branch, x), leaf),
		EqDatatype(SelectNaryRecursiveDatatypeConstructor(vec.Succ{Prev: vec.Zero{}}, branch, x), nested),
		EqDatatype(SelectNaryRecursiveDatatypeConstructor(vec.Succ{Prev: vec.Succ{Prev: vec.Zero{}}}, branch, x), leaf),
		IsNaryRecursiveDatatypeConstructor(branch, x),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	value, found := EvalDatatype(86, 2, result.Value, x)
	second, secondOK := value.Children.At(1)
	if !found || value.ConstructorID != 1 || value.Children.Len() != 3 || !secondOK || second.ConstructorID != 1 || second.Children.Len() != 3 {
		t.Fatalf("model=%#v/%v", value, found)
	}
}

func TestNaryRecursiveDatatypeInjectivityAndAcyclicity(t *testing.T) {
	context := NewContext(87)
	leaf := DatatypeConstructor(87, 2, 0, context, "leaf")
	branch := DeclareNaryRecursiveDatatypeConstructor(87, 2, 1, 3, context, "branch", narySelectorNames())
	x := DatatypeConst(87, 2, context, "x", 1)
	y := DatatypeConst(87, 2, context, "y", 2)
	first := ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(leaf, leaf, x))
	second := ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(leaf, leaf, y))
	if _, ok := Check(Assert(1, NewSolver(context), And(EqDatatype(first, second), Not(EqDatatype(x, y))))).(Unsat); !ok {
		t.Fatal("n-ary constructor must be injective in every field")
	}
	cycle := EqDatatype(x, ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(leaf, leaf, x)))
	if _, ok := Check(Assert(2, NewSolver(context), cycle)).(Unsat); !ok {
		t.Fatal("n-ary recursive cycle must be unsatisfiable")
	}
}

func TestGroundUninterpretedFunctionZeroIdentifiersUseCompactPath(t *testing.T) {
	context := NewContext(102)
	a := UninterpretedConst(0, context, "a", 0)
	b := UninterpretedConst(0, context, "b", 1)
	f := DeclareUnary(0, 0, context, "f", 0)
	formula := And(
		EqUninterpreted(a, b),
		Not(EqUninterpreted(ApplyUninterpreted(f, a), ApplyUninterpreted(f, b))),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestGroundBinaryUninterpretedFunctionCongruence(t *testing.T) {
	context := NewContext(12)
	a := UninterpretedConst(1, context, "a", 1)
	aPrime := UninterpretedConst(1, context, "a-prime", 2)
	b := UninterpretedConst(2, context, "b", 3)
	bPrime := UninterpretedConst(2, context, "b-prime", 4)
	combine := DeclareBinary(1, 2, 3, context, "combine", 5)
	formula := And(
		EqUninterpreted(a, aPrime),
		EqUninterpreted(b, bPrime),
		Not(EqUninterpreted(
			ApplyBinaryUninterpreted(combine, a, b),
			ApplyBinaryUninterpreted(combine, aPrime, bPrime),
		)),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestDisjointEUFLinearRealCombination(t *testing.T) {
	context := NewContext(15)
	a := UninterpretedConst(1, context, "a", 1)
	b := UninterpretedConst(1, context, "b", 2)
	function := DeclareUnary(1, 1, context, "f", 3)
	x := RealConst(context, "x", 4)
	formula := And(
		Not(EqUninterpreted(a, b)),
		EqUninterpreted(ApplyUninterpreted(function, a), ApplyUninterpreted(function, b)),
		LeReal(RealVal(context, Rational(1, 1)), x),
		LeReal(x, RealVal(context, Rational(2, 1))),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	value, found := EvalReal(result.Value, x)
	if !found || CompareRational(value, Rational(1, 1)) < 0 || CompareRational(value, Rational(2, 1)) > 0 {
		t.Fatalf("x=%s/%v", value, found)
	}
}

func TestRealFunctionCongruenceAndSharedBoundary(t *testing.T) {
	context := NewContext(16)
	x := RealConst(context, "x", 1)
	y := RealConst(context, "y", 2)
	function := DeclareRealFunction(context, "f", 3)
	congruence := And(
		EqReal(x, y),
		Not(EqReal(ApplyRealFunction(function, x), ApplyRealFunction(function, y))),
	)
	if result := Check(Assert(1, NewSolver(context), congruence)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("congruence result=%T", result)
	}
	shared := And(
		LeReal(x, y),
		LeReal(y, x),
		Not(EqReal(ApplyRealFunction(function, x), ApplyRealFunction(function, y))),
	)
	if result := Check(Assert(2, NewSolver(context), shared)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("shared result=%T", result)
	}
}

func TestRealFunctionApplicationsInsideArithmeticArePurified(t *testing.T) {
	context := NewContext(17)
	x := RealConst(context, "x", 1)
	y := RealConst(context, "y", 2)
	zero := RealVal(context, Rational(0, 1))
	function := DeclareRealFunction(context, "f", 3)
	formula := And(
		EqReal(x, y),
		LeReal(ApplyRealFunction(function, x), zero),
		LtReal(zero, ApplyRealFunction(function, y)),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%T", result)
	}
}

func TestRealBinaryFunctionApplicationsInsideArithmeticArePurified(t *testing.T) {
	context := NewContext(71)
	x := RealConst(context, "x", 1)
	y := RealConst(context, "y", 2)
	zero := RealVal(context, Rational(0, 1))
	function := DeclareRealBinary(context, "combine", 3)
	left := ApplyRealBinary(function, AddReal(x, RealVal(context, Rational(1, 1))), y)
	right := ApplyRealBinary(function, AddReal(y, RealVal(context, Rational(1, 1))), x)
	formula := And(
		EqReal(x, y),
		LeReal(left, zero),
		LtReal(zero, right),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("binary applications with congruent affine arguments should be unsatisfiable")
	}
}

func TestIndexedBitVectorOperations(t *testing.T) {
	context := NewContext(72)
	x := BitVecConst(8, context, "x", 1)
	value := BitVecValue(8, context, 0xa5)
	masked := AndBitVec(x, BitVecValue(8, context, 0x0f))
	formula := And(
		EqBitVec(x, value),
		Not(EqBitVec(masked, BitVecValue(8, context, 0x05))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("indexed bit-vector contradiction should be unsatisfiable")
	}
	wrapped := AddBitVec(BitVecValue(8, context, 255), BitVecValue(8, context, 1))
	if _, ok := Check(Assert(2, NewSolver(context), Not(EqBitVec(wrapped, BitVecValue(8, context, 0))))).(Unsat); !ok {
		t.Fatal("indexed 8-bit addition should wrap")
	}
}

func TestIndexedBitVectorModel(t *testing.T) {
	context := NewContext(73)
	x := BitVecConst(8, context, "x", 1)
	result := Check(Assert(1, NewSolver(context), EqBitVec(x, BitVecValue(8, context, 0xa5))))
	sat, ok := result.(Sat)
	if !ok {
		t.Fatalf("result=%T", result)
	}
	value, ok := ModelBitVec(sat.Value, x)
	bits, small := value.Uint64()
	if !ok || !small || bits != 0xa5 {
		t.Fatalf("model value=(%#x,%v,%v)", bits, small, ok)
	}
}

func TestBitVectorIntegerConversions(t *testing.T) {
	context := NewContext(1)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 0xff)),
		EqInt(BvToNat(x), IntVal(context, 255)),
		EqInt(BvToInt(x), IntVal(context, -1)),
		EqBitVec(IntToBitVec(8, IntVal(context, -129)), BitVecValue(8, context, 0x7f)),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Sat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
}

func TestGroundIntegerArrayReadOverWrite(t *testing.T) {
	context := NewContext(31)
	base := ConstIntArray(IntVal(context, 0))
	updated := StoreIntArray(base, IntVal(context, 7), IntVal(context, 42))
	nested := StoreIntArray(updated, IntVal(context, 8), IntVal(context, 99))
	formula := And(
		EqInt(SelectIntArray(updated, IntVal(context, 7)), IntVal(context, 42)),
		EqInt(SelectIntArray(updated, IntVal(context, 8)), IntVal(context, 0)),
		EqInt(SelectIntArray(nested, IntVal(context, 7)), IntVal(context, 42)),
		EqInt(SelectIntArray(nested, IntVal(context, 8)), IntVal(context, 99)),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Sat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
	contradiction := Not(EqInt(SelectIntArray(updated, IntVal(context, 7)), IntVal(context, 42)))
	if result := Check(Assert(2, NewSolver(context), contradiction)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("contradiction=%#v", result)
	}
}

func TestGroundIntegerArraySelectCongruence(t *testing.T) {
	context := NewContext(32)
	a := IntArrayConst(context, "a", 1)
	b := IntArrayConst(context, "b", 2)
	index := IntVal(context, 7)
	formula := And(EqArray(a, b), Not(EqInt(SelectIntArray(a, index), SelectIntArray(b, index))))
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
}

func TestGroundIntegerArraySymbolicIndex(t *testing.T) {
	context := NewContext(33)
	a := IntArrayConst(context, "a", 1)
	i := IntConst(context, "i", 11)
	j := IntConst(context, "j", 12)
	formula := And(EqInt(i, j), Not(EqInt(SelectIntArray(StoreIntArray(a, i, IntVal(context, 42)), j), IntVal(context, 42))))
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
}

func TestGroundIntegerArrayExtensionalModel(t *testing.T) {
	context := NewContext(34)
	a := IntArrayConst(context, "a", 31)
	b := IntArrayConst(context, "b", 32)
	seven := IntVal(context, 7)
	formula := And(Not(EqArray(a, b)), EqInt(SelectIntArray(a, seven), IntVal(context, 42)))
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%#v", Check(Assert(1, NewSolver(context), formula)))
	}
	sevenValue, sevenOK := EvalIntArray(result.Value, a, smt.NewIntegerValue(7))
	aWitness, aOK := EvalIntArray(result.Value, a, smt.NewIntegerValue(8))
	bWitness, bOK := EvalIntArray(result.Value, b, smt.NewIntegerValue(8))
	if !sevenOK || smt.CompareIntegerValue(sevenValue, smt.NewIntegerValue(42)) != 0 {
		t.Fatalf("a[7]=%v/%v", sevenValue, sevenOK)
	}
	if !aOK || !bOK || smt.CompareIntegerValue(aWitness, bWitness) == 0 {
		t.Fatalf("witness a[8]=%v/%v b[8]=%v/%v", aWitness, aOK, bWitness, bOK)
	}
}

func TestGroundIntegerArrayStoreExtensionality(t *testing.T) {
	context := NewContext(35)
	a := IntArrayConst(context, "a", 41)
	seven, eight := IntVal(context, 7), IntVal(context, 8)
	identity := StoreIntArray(a, seven, SelectIntArray(a, seven))
	left := StoreIntArray(StoreIntArray(a, seven, IntVal(context, 1)), eight, IntVal(context, 2))
	right := StoreIntArray(StoreIntArray(a, eight, IntVal(context, 2)), seven, IntVal(context, 1))
	formula := And(EqArray(identity, a), Not(EqArray(left, right)))
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
	different := Not(EqArray(StoreIntArray(a, seven, IntVal(context, 1)), StoreIntArray(a, seven, IntVal(context, 2))))
	if result := Check(Assert(2, NewSolver(context), different)); func() bool { _, ok := result.(Sat); return ok }() == false {
		t.Fatalf("different=%#v", result)
	}
}

func TestGroundIntegerArrayCrossBaseStoreEquality(t *testing.T) {
	context := NewContext(36)
	a := IntArrayConst(context, "a", 51)
	b := IntArrayConst(context, "b", 52)
	seven, eight := IntVal(context, 7), IntVal(context, 8)
	left := StoreIntArray(a, seven, IntVal(context, 1))
	right := StoreIntArray(b, seven, IntVal(context, 1))
	formula := And(EqArray(left, right), Not(EqInt(SelectIntArray(a, eight), SelectIntArray(b, eight))))
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("outside bridge=%#v", result)
	}
	overwritten := And(
		EqArray(left, right),
		EqInt(SelectIntArray(a, seven), IntVal(context, 2)),
		EqInt(SelectIntArray(b, seven), IntVal(context, 3)),
	)
	result, ok := Check(Assert(2, NewSolver(context), overwritten)).(Sat)
	if !ok {
		t.Fatalf("overwritten=%#v", Check(Assert(2, NewSolver(context), overwritten)))
	}
	aOutside, aOK := EvalIntArray(result.Value, a, smt.NewIntegerValue(8))
	bOutside, bOK := EvalIntArray(result.Value, b, smt.NewIntegerValue(8))
	if !aOK || !bOK || smt.CompareIntegerValue(aOutside, bOutside) != 0 {
		t.Fatalf("model bridge a[8]=%v/%v b[8]=%v/%v", aOutside, aOK, bOutside, bOK)
	}
}

func TestGroundIntegerArrayConstantBaseEquality(t *testing.T) {
	context := NewContext(37)
	a := IntArrayConst(context, "a", 61)
	zero := ConstIntArray(IntVal(context, 0))
	seven, eight := IntVal(context, 7), IntVal(context, 8)
	formula := And(EqArray(a, zero), Not(EqInt(SelectIntArray(a, eight), IntVal(context, 0))))
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("default=%#v", result)
	}
	overwritten := And(
		EqArray(StoreIntArray(a, seven, IntVal(context, 0)), StoreIntArray(zero, seven, IntVal(context, 0))),
		EqInt(SelectIntArray(a, seven), IntVal(context, 5)),
	)
	result, ok := Check(Assert(2, NewSolver(context), overwritten)).(Sat)
	if !ok {
		t.Fatalf("overwritten=%#v", Check(Assert(2, NewSolver(context), overwritten)))
	}
	outside, found := EvalIntArray(result.Value, a, smt.NewIntegerValue(8))
	if !found || smt.CompareIntegerValue(outside, smt.NewIntegerValue(0)) != 0 {
		t.Fatalf("model a[8]=%v/%v", outside, found)
	}
}

func TestMixedArrayArithmeticSolving(t *testing.T) {
	context := NewContext(38)
	a := IntArrayConst(context, "a", 71)
	i := IntConst(context, "i", 91)
	j := IntConst(context, "j", 92)
	value := IntVal(context, 42)
	readConflict := Not(EqInt(SelectIntArray(StoreIntArray(a, i, value), j), value))
	equalBounds := And(Le(i, j), Le(j, i), readConflict)
	if result := Check(Assert(1, NewSolver(context), equalBounds)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("shared indices=%#v", result)
	}
	strictBounds := And(Lt(i, j), readConflict)
	result, ok := Check(Assert(2, NewSolver(context), strictBounds)).(Sat)
	if !ok {
		t.Fatalf("distinct indices=%#v", Check(Assert(2, NewSolver(context), strictBounds)))
	}
	iValue, iOK := EvalIntExact(result.Value, i)
	jValue, jOK := EvalIntExact(result.Value, j)
	if !iOK || !jOK || smt.CompareIntegerValue(iValue, jValue) >= 0 {
		t.Fatalf("model i=%v/%v j=%v/%v", iValue, iOK, jValue, jOK)
	}
	exactIndex := IntVal(context, 7)
	arrayLaw := EqInt(SelectIntArray(StoreIntArray(a, exactIndex, value), exactIndex), value)
	bvConflict := Not(EqBitVec(BitVecValue(8, context, 0xa5), BitVecValue(8, context, 0xa5)))
	if result := Check(Assert(3, NewSolver(context), And(arrayLaw, bvConflict))); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("array+BV=%#v", result)
	}
}

func TestGroundBitVectorArrayReadOverWrite(t *testing.T) {
	context := NewContext(40)
	base := ConstBitVecArray(4, BitVecValue(8, context, 0))
	three := BitVecValue(4, context, 3)
	four := BitVecValue(4, context, 4)
	value := BitVecValue(8, context, 0xa5)
	updated := StoreBitVecArray(base, three, value)
	formula := And(
		EqBitVec(SelectBitVecArray(updated, three), value),
		EqBitVec(SelectBitVecArray(updated, four), BitVecValue(8, context, 0)),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Sat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
	contradiction := Not(EqBitVec(SelectBitVecArray(updated, three), value))
	if result := Check(Assert(2, NewSolver(context), contradiction)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("contradiction=%#v", result)
	}
	symbol := BitVecArrayConst(4, 8, context, "memory", 1)
	symbolUpdated := StoreBitVecArray(symbol, three, value)
	if result := Check(Assert(3, NewSolver(context), Not(EqBitVec(SelectBitVecArray(symbolUpdated, three), value)))); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("symbol read-over-write=%#v", result)
	}
}

func TestGroundBitVectorArrayCongruence(t *testing.T) {
	context := NewContext(41)
	left := BitVecArrayConst(4, 8, context, "left", 1)
	right := BitVecArrayConst(4, 8, context, "right", 2)
	index := BitVecValue(4, context, 7)
	formula := And(
		EqBitVecArray(left, right),
		Not(EqBitVec(SelectBitVecArray(left, index), SelectBitVecArray(right, index))),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
}

func TestGroundBitVectorArrayDisequality(t *testing.T) {
	context := NewContext(43)
	left := BitVecArrayConst(4, 8, context, "left", 1)
	right := BitVecArrayConst(4, 8, context, "right", 2)
	if result := Check(Assert(1, NewSolver(context), Not(EqBitVecArray(left, right)))); func() bool { _, ok := result.(Sat); return ok }() == false {
		t.Fatalf("distinct arrays=%#v", result)
	}
	formula := And(EqBitVecArray(left, right), Not(EqBitVecArray(left, right)))
	if result := Check(Assert(2, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("equal and distinct=%#v", result)
	}
}

func TestGroundBitVectorArrayExtensionalModel(t *testing.T) {
	context := NewContext(45)
	left := BitVecArrayConst(4, 8, context, "left", 1)
	right := BitVecArrayConst(4, 8, context, "right", 2)
	result, ok := Check(Assert(1, NewSolver(context), Not(EqBitVecArray(left, right)))).(Sat)
	if !ok {
		t.Fatalf("result=%#v", Check(Assert(1, NewSolver(context), Not(EqBitVecArray(left, right)))))
	}
	index := smt.NewBitVectorUint64(4, 0)
	leftValue, leftOK := EvalBitVecArray(result.Value, left, index)
	rightValue, rightOK := EvalBitVecArray(result.Value, right, index)
	if !leftOK || !rightOK || smt.EqualBitVectorValue(leftValue, rightValue) {
		t.Fatalf("left=%#v/%v right=%#v/%v", leftValue, leftOK, rightValue, rightOK)
	}
}

func TestGroundBitVectorArrayStoreExtensionality(t *testing.T) {
	context := NewContext(44)
	base := BitVecArrayConst(4, 8, context, "memory", 1)
	three := BitVecValue(4, context, 3)
	four := BitVecValue(4, context, 4)
	one := BitVecValue(8, context, 1)
	two := BitVecValue(8, context, 2)
	left := StoreBitVecArray(StoreBitVecArray(base, three, one), four, two)
	right := StoreBitVecArray(StoreBitVecArray(base, four, two), three, one)
	if result := Check(Assert(1, NewSolver(context), Not(EqBitVecArray(left, right)))); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("commuting stores=%#v", result)
	}
	overwrite := StoreBitVecArray(StoreBitVecArray(base, three, one), three, two)
	final := StoreBitVecArray(base, three, two)
	if result := Check(Assert(2, NewSolver(context), Not(EqBitVecArray(overwrite, final)))); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("overwrite=%#v", result)
	}
}

func TestGroundBitVectorArraySymbolicIndex(t *testing.T) {
	context := NewContext(42)
	array := BitVecArrayConst(4, 8, context, "memory", 1)
	left := BitVecConst(4, context, "i", 2)
	right := BitVecConst(4, context, "j", 3)
	value := BitVecValue(8, context, 0xa5)
	formula := And(
		EqBitVec(left, right),
		Not(EqBitVec(SelectBitVecArray(StoreBitVecArray(array, left, value), right), value)),
	)
	if result := Check(Assert(1, NewSolver(context), formula)); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("result=%#v", result)
	}
}

func TestIndexedBitVectorOrdering(t *testing.T) {
	context := NewContext(74)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 0x7f)),
		Not(UltBitVec(x, BitVecValue(8, context, 0x80))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("127 must be unsigned-less than 128")
	}
	if _, ok := Check(Assert(2, NewSolver(context), Not(SltBitVec(BitVecValue(8, context, 0xff), BitVecValue(8, context, 0))))).(Unsat); !ok {
		t.Fatal("signed -1 must be less than zero")
	}
}

func TestIndexedBitVectorSubtractionAndMultiplication(t *testing.T) {
	context := NewContext(75)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 13)),
		Not(EqBitVec(MulBitVec(x, BitVecValue(8, context, 7)), BitVecValue(8, context, 91))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("symbol-dependent modular multiplication should be exact")
	}
	underflow := SubBitVec(BitVecValue(8, context, 0), BitVecValue(8, context, 1))
	if _, ok := Check(Assert(2, NewSolver(context), Not(EqBitVec(underflow, BitVecValue(8, context, 0xff))))).(Unsat); !ok {
		t.Fatal("subtraction should wrap at the indexed width")
	}
}

func TestIndexedBitVectorShifts(t *testing.T) {
	context := NewContext(76)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 0x81)),
		Not(EqBitVec(LshrBitVec(x, BitVecValue(8, context, 4)), BitVecValue(8, context, 8))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("symbol-dependent logical shift should be exact")
	}
	if _, ok := Check(Assert(2, NewSolver(context), Not(EqBitVec(AshrBitVec(BitVecValue(8, context, 0x80), BitVecValue(8, context, 9)), BitVecValue(8, context, 0xff))))).(Unsat); !ok {
		t.Fatal("out-of-range arithmetic shift should sign-fill")
	}
}

func TestIndexedBitVectorDivisionAndRemainder(t *testing.T) {
	context := NewContext(77)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 100)),
		Not(EqBitVec(UdivBitVec(x, BitVecValue(8, context, 7)), BitVecValue(8, context, 14))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("symbol-dependent unsigned division should be exact")
	}
	zero := BitVecValue(8, context, 0)
	if _, ok := Check(Assert(2, NewSolver(context), Not(EqBitVec(SdivBitVec(BitVecValue(8, context, 0x80), zero), BitVecValue(8, context, 1))))).(Unsat); !ok {
		t.Fatal("negative signed division by zero should yield one")
	}
}

func TestIndexedBitVectorStructuralOperators(t *testing.T) {
	context := NewContext(78)
	x := BitVecConst(8, context, "x", 1)
	upper := ExtractBitVec(7, 4, x)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 0xab)),
		Not(EqBitVec(upper, BitVecValue(4, context, 0xa))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("symbol-dependent extraction should preserve computed width")
	}
	joined := ConcatBitVec(4, 4, BitVecValue(4, context, 0xa), BitVecValue(4, context, 0xb))
	if _, ok := Check(Assert(2, NewSolver(context), Not(EqBitVec(joined, BitVecValue(8, context, 0xab))))).(Unsat); !ok {
		t.Fatal("concatenation should add indexed widths")
	}
}

func TestContextIndexedMixedDatatype(t *testing.T) {
	context := NewContext(82)
	signature := IntDatatypeMixedField("payload", SelfDatatypeMixedField("next", EmptyDatatypeMixedSignature()))
	node := DeclareMixedDatatypeConstructor(820, 2, 1, context, "node", signature)
	leaf := DatatypeConstructor(820, 2, 0, context, "leaf")
	arguments := IntDatatypeMixedArgument(IntVal(context, 42), SelfDatatypeMixedArgument(leaf, EmptyDatatypeMixedArguments(context)))
	x := DatatypeConst(820, 2, context, "x", 1)
	value := ApplyMixedDatatypeConstructor(node, arguments)
	payload := MixedDatatypeFields(node)
	next := NextMixedDatatypeField(payload)
	formula := And(
		EqDatatype(x, value),
		EqInt(SelectMixedIntDatatypeField(payload, x), IntVal(context, 42)),
		EqDatatype(SelectMixedSelfDatatypeField(next, x), leaf),
		IsMixedDatatypeConstructor(node, x),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("mixed datatype result=%#v", Check(Assert(1, NewSolver(context), formula)))
	}
	model, found := EvalDatatype(820, 2, result.Value, x)
	payloadValue, payloadOK := model.Fields.At(0)
	nextValue, nextOK := model.Fields.At(1)
	if !found || model.ConstructorID != 1 || !payloadOK || smt.CompareIntegerValue(payloadValue.Integer, smt.NewIntegerValue(42)) != 0 || !nextOK || nextValue.Datatype == nil || nextValue.Datatype.ConstructorID != 0 {
		t.Fatalf("mixed datatype model=%+v found=%v", model, found)
	}
}

func TestContextIndexedMutuallyRecursiveDatatypes(t *testing.T) {
	context := NewContext(84)
	treeLeaf := DatatypeConstructor(840, 2, 0, context, "leaf")
	forestNil := DatatypeConstructor(841, 2, 0, context, "nil")
	treeNode := DeclareMixedDatatypeConstructor(840, 2, 1, context, "node",
		DatatypeReferenceMixedField(841, 2, "children", EmptyDatatypeMixedSignature()))
	forestCons := DeclareMixedDatatypeConstructor(841, 2, 1, context, "cons",
		DatatypeReferenceMixedField(840, 2, "head", SelfDatatypeMixedField("tail", EmptyDatatypeMixedSignature())))
	forest := ApplyMixedDatatypeConstructor(forestCons,
		DatatypeReferenceMixedArgument(840, 2, treeLeaf, SelfDatatypeMixedArgument(forestNil, EmptyDatatypeMixedArguments(context))))
	tree := ApplyMixedDatatypeConstructor(treeNode,
		DatatypeReferenceMixedArgument(841, 2, forest, EmptyDatatypeMixedArguments(context)))
	x := DatatypeConst(840, 2, context, "x", 1)
	children := MixedDatatypeFields(treeNode)
	head := MixedDatatypeFields(forestCons)
	selectedForest := SelectMixedDatatypeReferenceField(841, 2, children, x)
	formula := And(
		EqDatatype(x, tree),
		EqDatatype(SelectMixedDatatypeReferenceField(840, 2, head, selectedForest), treeLeaf),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("mutual datatype result=%#v", Check(Assert(1, NewSolver(context), formula)))
	}
	model, found := EvalDatatype(840, 2, result.Value, x)
	childrenValue, childrenOK := model.Fields.At(0)
	if !found || !childrenOK || childrenValue.Datatype == nil || childrenValue.Datatype.ConstructorID != 1 {
		t.Fatalf("mutual datatype model=%+v found=%v", model, found)
	}
}

func TestIndexedBitVectorRotateRepeatOperators(t *testing.T) {
	context := NewContext(79)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 0x81)),
		Not(EqBitVec(RotateLeftBitVec(1, x), BitVecValue(8, context, 0x03))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("symbol-dependent rotation should be exact")
	}
	repeated := RepeatBitVec(2, BitVecValue(4, context, 0xa))
	if _, ok := Check(Assert(2, NewSolver(context), Not(EqBitVec(repeated, BitVecValue(8, context, 0xaa))))).(Unsat); !ok {
		t.Fatal("repeat should multiply the indexed width")
	}
	script := `(set-logic QF_BV)
(assert (= ((_ rotate_right 1) #x03) #x81))
(assert (= ((_ repeat 2) #xa) #xaa))
(check-sat)`
	result, ok := ExecuteSMTLib(script).(smtlib.Executed)
	if !ok || len(result.Responses) != 4 {
		t.Fatalf("SMT-LIB result=%#v", result)
	}
}

func TestIndexedBitVectorOverflowPredicates(t *testing.T) {
	context := NewContext(80)
	x := BitVecConst(8, context, "x", 1)
	formula := And(
		EqBitVec(x, BitVecValue(8, context, 0xff)),
		Not(UaddOverflowBitVec(x, BitVecValue(8, context, 1))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("symbol-dependent unsigned-add overflow should be exact")
	}
	boundaries := []BoolExpr{
		SaddOverflowBitVec(BitVecValue(8, context, 0x7f), BitVecValue(8, context, 1)),
		UsubOverflowBitVec(BitVecValue(8, context, 0), BitVecValue(8, context, 1)),
		SsubOverflowBitVec(BitVecValue(8, context, 0x80), BitVecValue(8, context, 1)),
		UmulOverflowBitVec(BitVecValue(8, context, 0x10), BitVecValue(8, context, 0x10)),
		SmulOverflowBitVec(BitVecValue(8, context, 0x40), BitVecValue(8, context, 2)),
		SdivOverflowBitVec(BitVecValue(8, context, 0x80), BitVecValue(8, context, 0xff)),
		NegOverflowBitVec(BitVecValue(8, context, 0x80)),
	}
	for index, predicate := range boundaries {
		if _, ok := Check(Assert(index+2, NewSolver(context), Not(predicate))).(Unsat); !ok {
			t.Fatalf("boundary %d should overflow", index)
		}
	}
}

func TestGroundBitVectorUninterpretedFunctions(t *testing.T) {
	context := NewContext(81)
	x := BitVecConst(8, context, "x", 1)
	y := BitVecConst(8, context, "y", 2)
	function := DeclareBitVecFunction(8, 4, context, "f", 3)
	formula := And(
		EqBitVec(x, y),
		Not(EqBitVec(ApplyBitVecFunction(function, x), ApplyBitVecFunction(function, y))),
	)
	if _, ok := Check(Assert(1, NewSolver(context), formula)).(Unsat); !ok {
		t.Fatal("unary QF_UFBV congruence should be exact")
	}
	a := BitVecConst(4, context, "a", 4)
	b := BitVecConst(4, context, "b", 5)
	binary := DeclareBitVecBinary(8, 4, 16, context, "combine", 6)
	left := ApplyBitVecBinary(binary, x, a)
	right := ApplyBitVecBinary(binary, y, b)
	if _, ok := Check(Assert(2, NewSolver(context), And(EqBitVec(x, y), EqBitVec(a, b), Not(EqBitVec(left, right))))).(Unsat); !ok {
		t.Fatal("binary QF_UFBV congruence should be exact")
	}
}

func TestExactLinearRealModel(t *testing.T) {
	context := NewContext(13)
	x := RealConst(context, "x", 1)
	y := RealConst(context, "y", 2)
	formula := And(
		LeReal(AddReal(x, y), RealVal(context, Rational(3, 1))),
		LeReal(RealVal(context, Rational(1, 2)), x),
		LtReal(RealVal(context, Rational(1, 3)), y),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	xValue, xOK := EvalReal(result.Value, x)
	yValue, yOK := EvalReal(result.Value, y)
	if !xOK || !yOK || xValue.Sign() < 0 || yValue.Sign() <= 0 {
		t.Fatalf("model x=%s/%v y=%s/%v", xValue, xOK, yValue, yOK)
	}
}

func TestExactLinearRealFastPathOverflowsInlineCoefficients(t *testing.T) {
	context := NewContext(14)
	variables := []RealExpr{
		RealConst(context, "a", 1), RealConst(context, "b", 2),
		RealConst(context, "c", 3), RealConst(context, "d", 4),
		RealConst(context, "e", 5), RealConst(context, "f", 6),
	}
	formula := And(
		LeReal(AddReal(variables...), RealVal(context, Rational(6, 1))),
		LeReal(RealVal(context, Rational(1, 1)), variables[0]),
		LeReal(RealVal(context, Rational(1, 1)), variables[1]),
		LeReal(RealVal(context, Rational(1, 1)), variables[2]),
		LeReal(RealVal(context, Rational(1, 1)), variables[3]),
		LeReal(RealVal(context, Rational(1, 1)), variables[4]),
		LeReal(RealVal(context, Rational(1, 1)), variables[5]),
	)
	result, ok := Check(Assert(1, NewSolver(context), formula)).(Sat)
	if !ok {
		t.Fatalf("result=%T", Check(Assert(1, NewSolver(context), formula)))
	}
	for index, variable := range variables {
		value, found := EvalReal(result.Value, variable)
		if !found || CompareRational(value, Rational(1, 1)) < 0 {
			t.Fatalf("variable %d=%s/%v", index, value, found)
		}
	}
}
