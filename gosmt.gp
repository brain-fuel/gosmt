// Package gosmt exposes Z3-shaped, context-indexed solver construction over
// the essential Go+ standard-library SMT core.
package gosmt

import (
	smt "goforge.dev/goplus/std/smt"
	"goforge.dev/goplus/std/smtlib"
	"goforge.dev/goplus/std/vec"
)

//goplus:derive off
//goplus:repr transparent
type Context[c nat] enum { contextValue(ID int) Context[c] }

// Expressions from different contexts cannot be composed in Go+.
//goplus:derive off
//goplus:repr transparent
type BoolExpr[c nat] enum { boolExprValue(ContextID int, Term smt.Term[smt.BoolSort], Fast booleanFast) BoolExpr[c] }
//goplus:derive off
//goplus:repr transparent
type IntExpr[c nat] enum { intExprValue(ContextID int, Term smt.Term[smt.IntSort], Fast integerFast) IntExpr[c] }
//goplus:derive off
//goplus:repr transparent
type RealExpr[c nat] enum { realExprValue(ContextID int, Term smt.Term[smt.RealSort], Fast realFast) RealExpr[c] }
//goplus:derive off
//goplus:repr transparent
type StringExpr[c nat] enum { stringExprValue(ContextID int, Term smt.Term[smt.StringSort], Fast stringFast) StringExpr[c] }
//goplus:derive off
//goplus:repr transparent
type RegexExpr[c nat] enum { regexExprValue(ContextID int, Core smt.Regex[smt.StringSort], Fast regexFast) RegexExpr[c] }
//goplus:derive off
//goplus:repr transparent
type BitVecExpr[c nat, w nat] enum { bitVecExprValue(ContextID int, Term smt.Term[smt.BitVecSort[w]], Fast bitVectorFast) BitVecExpr[c, w] }
//goplus:derive off
type ArrayExpr[c nat, I any, E any] enum { arrayExprValue(ContextID int, Term smt.Term[smt.ArraySort[I, E]], Fast arrayFast) ArrayExpr[c, I, E] }
//goplus:derive off
//goplus:repr transparent
type BitVecArrayExpr[c nat, iw nat, ew nat] enum { bitVecArrayExprValue(ContextID int, Term smt.Term[smt.ArraySort[smt.BitVecSort[iw], smt.BitVecSort[ew]]], Fast bitVecArrayFast) BitVecArrayExpr[c, iw, ew] }
//goplus:derive off
//goplus:repr transparent
type DatatypeExpr[c nat, d nat, n nat] enum { datatypeExprValue(ContextID int, Term smt.Term[smt.DatatypeSort[d, n]]) DatatypeExpr[c, d, n] }
//goplus:derive off
//goplus:repr transparent
type DatatypeRecursiveConstructor[c nat, d nat, n nat, k nat] enum { datatypeRecursiveConstructorValue(ContextID int, Core smt.RecursiveDatatypeConstructor[d, n, k]) DatatypeRecursiveConstructor[c, d, n, k] }
//goplus:derive off
//goplus:repr transparent
type DatatypeBinaryRecursiveConstructor[c nat, d nat, n nat, k nat] enum { datatypeBinaryRecursiveConstructorValue(ContextID int, Core smt.BinaryRecursiveDatatypeConstructor[d, n, k]) DatatypeBinaryRecursiveConstructor[c, d, n, k] }
//goplus:derive off
//goplus:repr transparent
type DatatypeNaryRecursiveConstructor[c nat, d nat, n nat, k nat, a nat] enum { datatypeNaryRecursiveConstructorValue(ContextID int, Core smt.NaryRecursiveDatatypeConstructor[d, n, k, a]) DatatypeNaryRecursiveConstructor[c, d, n, k, a] }
//goplus:derive off
//goplus:repr transparent
type DatatypeMixedConstructor[c nat, d nat, n nat, k nat, fields smt.DatatypeFieldList] enum { datatypeMixedConstructorValue(ContextID int, Core smt.MixedRecursiveDatatypeConstructor[d, n, k, fields]) DatatypeMixedConstructor[c, d, n, k, fields] }
//goplus:derive off
//goplus:repr transparent
type DatatypeMixedArguments[c nat, d nat, n nat, fields smt.DatatypeFieldList] enum { datatypeMixedArgumentsValue(ContextID int, Core smt.MixedDatatypeArguments[d, n, fields]) DatatypeMixedArguments[c, d, n, fields] }
//goplus:derive off
//goplus:repr transparent
type DatatypeMixedCursor[c nat, d nat, n nat, k nat, fields smt.DatatypeFieldList] enum { datatypeMixedCursorValue(ContextID int, Core smt.MixedDatatypeCursor[d, n, k, fields]) DatatypeMixedCursor[c, d, n, k, fields] }
//goplus:derive off
//goplus:repr transparent
type UninterpretedExpr[c nat, s nat] enum { uninterpretedExprValue(ContextID int, Term smt.Term[smt.UninterpretedSort[s]], Fast uninterpretedFast) UninterpretedExpr[c, s] }
//goplus:derive off
//goplus:repr transparent
type UnaryFunc[c nat, d nat, r nat] enum { unaryFuncValue(ContextID int, Function smt.UnaryFunction[d, r], Fast uninterpretedUnaryFunctionFast) UnaryFunc[c, d, r] }
//goplus:derive off
//goplus:repr transparent
type BinaryFunc[c nat, a nat, b nat, r nat] enum { binaryFuncValue(ContextID int, Function smt.BinaryFunction[a, b, r], Fast uninterpretedBinaryFunctionFast) BinaryFunc[c, a, b, r] }
//goplus:derive off
//goplus:repr transparent
type RealFunc[c nat] enum { realFuncValue(ContextID int, Function smt.SortedUnaryFunction[smt.RealSort, smt.RealSort], Fast realFunctionFast) RealFunc[c] }
//goplus:derive off
//goplus:repr transparent
type RealBinaryFunc[c nat] enum { realBinaryFuncValue(ContextID int, Function smt.SortedBinaryFunction[smt.RealSort, smt.RealSort, smt.RealSort], Fast realBinaryFunctionFast) RealBinaryFunc[c] }
//goplus:derive off
//goplus:repr transparent
type BitVecFunc[c nat, d nat, r nat] enum { bitVecFuncValue(ContextID int, Function smt.SortedUnaryFunction[smt.BitVecSort[d], smt.BitVecSort[r]]) BitVecFunc[c, d, r] }
//goplus:derive off
//goplus:repr transparent
type BitVecBinaryFunc[c nat, a nat, b nat, r nat] enum { bitVecBinaryFuncValue(ContextID int, Function smt.SortedBinaryFunction[smt.BitVecSort[a], smt.BitVecSort[b], smt.BitVecSort[r]]) BitVecBinaryFunc[c, a, b, r] }

//goplus:derive off
//goplus:repr transparent
type Solver[c nat, a nat, d nat] enum { solverValue(ContextID int, Core smt.Solver[a, d]) Solver[c, a, d] }
//goplus:derive off
//goplus:repr transparent
type Model[c nat, a nat] enum { modelValue(ContextID int, Core smt.Model[a]) Model[c, a] }

type Result[c nat, a nat] enum {
	Sat(Value Model[c, a])
	Unsat(Context Context[c], Proof smt.Proof[a])
	Unknown(Context Context[c], Proof smt.Proof[a], Reason smt.UnknownReason)
}

type AssumptionResult[c nat, a nat] enum {
	AssumptionSat(Value Model[c, a])
	AssumptionUnsat(Context Context[c], Proof smt.Proof[a], Indices []int)
	AssumptionUnknown(Context Context[c], Proof smt.Proof[a], Reason smt.UnknownReason)
}

func ParseSMTLib(source string) smtlib.ParseResult { return smtlib.Parse(source) }
func ExecuteSMTLib(source string) smtlib.ExecutionResult { return smtlib.Execute(source) }

func NewContext(id nat) Context[id] {
	if id < 0 { panic("gosmt: negative context identity") }
	return contextValue(int(id))
}

func BoolConst(0 c nat, context Context[c], name string, id int) BoolExpr[c] {
	match context {
	case contextValue(contextID):
		if id >= 0 { return fastBooleanVariable(contextID, id) }
		return boolExprValue(contextID, smt.BoolSymbol(id, name), booleanFast{})
	}
}

func BoolValue(0 c nat, context Context[c], value bool) BoolExpr[c] {
	match context { case contextValue(contextID): return boolExprValue(contextID, smt.Bool(value), booleanFast{}) }
}

func StringVal(0 c nat, context Context[c], value string) StringExpr[c] {
	match context { case contextValue(contextID): return fastStringValue(contextID, value) }
}

func StringConst(0 c nat, context Context[c], name string, id int) StringExpr[c] {
	match context { case contextValue(contextID): return fastStringConst(contextID, name, id) }
}

func ConcatString(0 c nat, values ...StringExpr[c]) StringExpr[c] {
	return fastConcatString(values)
}

func LengthString(0 c nat, value StringExpr[c]) IntExpr[c] {
	match value { case stringExprValue(contextID, term, fast):
		compact, ok := compactString(stringExprValue(contextID, term, fast))
		if ok { return intExprValue(contextID, nil, integerFast{kind: integerFastStringLength, string: compact}) }
		return intExprValue(contextID, smt.StringLength(materializeString(stringExprValue(contextID, term, fast))), integerFast{})
	}
}

func ContainsString(0 c nat, value StringExpr[c], substring StringExpr[c]) BoolExpr[c] {
	return fastStringRelation(smt.CompactStringContains, value, substring)
}

func HasPrefixString(0 c nat, value StringExpr[c], prefix StringExpr[c]) BoolExpr[c] {
	return fastStringRelation(smt.CompactStringPrefix, value, prefix)
}

func HasSuffixString(0 c nat, value StringExpr[c], suffix StringExpr[c]) BoolExpr[c] {
	return fastStringRelation(smt.CompactStringSuffix, value, suffix)
}

func EqString(0 c nat, left StringExpr[c], right StringExpr[c]) BoolExpr[c] {
	return fastStringRelation(smt.CompactStringEqual, left, right)
}

func AtString(0 c nat, value StringExpr[c], index IntExpr[c]) StringExpr[c] {
	return fastAtString(value, index)
}

func Substring(0 c nat, value StringExpr[c], offset IntExpr[c], length IntExpr[c]) StringExpr[c] {
	return fastSubstring(value, offset, length)
}

func IndexOfString(0 c nat, value StringExpr[c], substring StringExpr[c], offset IntExpr[c]) IntExpr[c] {
	return fastIndexOfString(value, substring, offset)
}

func ReplaceString(0 c nat, value StringExpr[c], source StringExpr[c], replacement StringExpr[c]) StringExpr[c] {
	return fastReplaceString(value, source, replacement)
}

func ReplaceAllString(0 c nat, value StringExpr[c], source StringExpr[c], replacement StringExpr[c]) StringExpr[c] {
	return fastReplaceAllString(value, source, replacement)
}

func ToIntString(0 c nat, value StringExpr[c]) IntExpr[c] {
	return fastStringToInt(value)
}

func FromIntString(0 c nat, value IntExpr[c]) StringExpr[c] {
	return fastIntToString(value)
}

func ToCodeString(0 c nat, value StringExpr[c]) IntExpr[c] {
	return fastStringToCode(value)
}

func FromCodeString(0 c nat, value IntExpr[c]) StringExpr[c] {
	return fastCodeToString(value)
}

func IsDigitString(0 c nat, value StringExpr[c]) BoolExpr[c] {
	return fastStringIsDigit(value)
}

func ToRegexString(0 c nat, value StringExpr[c]) RegexExpr[c] {
	match value { case stringExprValue(contextID, term, fast):
		if fast.kind == stringFastLiteral { return regexExprValue(contextID, smt.Regex[smt.StringSort]{}, regexFast{kind: regexFastLiteral, value: fast.value}) }
		return regexExprValue(contextID, smt.StringToRegex(materializeString(stringExprValue(contextID, term, fast))), regexFast{})
	}
}

func RangeRegexString(0 c nat, low StringExpr[c], high StringExpr[c]) RegexExpr[c] {
	match low { case stringExprValue(contextID, lowTerm, lowFast): match high { case stringExprValue(highContext, highTerm, highFast):
		if contextID != highContext { panic("gosmt: erased regex range context mismatch") }
		return regexExprValue(contextID, smt.StringRangeRegex(
			materializeString(stringExprValue(contextID, lowTerm, lowFast)),
			materializeString(stringExprValue(highContext, highTerm, highFast))), regexFast{})
	} }
}

func EmptyStringRegex(0 c nat, context Context[c]) RegexExpr[c] {
	match context { case contextValue(contextID): return regexExprValue(contextID, smt.Regex[smt.StringSort]{}, regexFast{kind: regexFastEmpty}) }
}

func FullStringRegex(0 c nat, context Context[c]) RegexExpr[c] {
	match context { case contextValue(contextID): return regexExprValue(contextID, smt.Regex[smt.StringSort]{}, regexFast{kind: regexFastFull}) }
}

func AllCharStringRegex(0 c nat, context Context[c]) RegexExpr[c] {
	match context { case contextValue(contextID): return regexExprValue(contextID, smt.Regex[smt.StringSort]{}, regexFast{kind: regexFastAllChar}) }
}

func ConcatRegexExpr(0 c nat, left RegexExpr[c], right RegexExpr[c]) RegexExpr[c] {
	match left { case regexExprValue(contextID, leftCore, leftFast): match right { case regexExprValue(rightContext, rightCore, rightFast):
		if contextID != rightContext { panic("gosmt: erased regex concat context mismatch") }
		return regexExprValue(contextID, smt.ConcatRegex(materializeRegex(leftCore, leftFast), materializeRegex(rightCore, rightFast)), regexFast{})
	} }
}

func UnionRegexExpr(0 c nat, left RegexExpr[c], right RegexExpr[c]) RegexExpr[c] {
	match left { case regexExprValue(contextID, leftCore, leftFast): match right { case regexExprValue(rightContext, rightCore, rightFast):
		if contextID != rightContext { panic("gosmt: erased regex union context mismatch") }
		return regexExprValue(contextID, smt.UnionRegex(materializeRegex(leftCore, leftFast), materializeRegex(rightCore, rightFast)), regexFast{})
	} }
}

func IntersectRegexExpr(0 c nat, left RegexExpr[c], right RegexExpr[c]) RegexExpr[c] {
	match left { case regexExprValue(contextID, leftCore, leftFast): match right { case regexExprValue(rightContext, rightCore, rightFast):
		if contextID != rightContext { panic("gosmt: erased regex intersection context mismatch") }
		return regexExprValue(contextID, smt.IntersectRegex(materializeRegex(leftCore, leftFast), materializeRegex(rightCore, rightFast)), regexFast{})
	} }
}

func DifferenceRegexExpr(0 c nat, left RegexExpr[c], right RegexExpr[c]) RegexExpr[c] {
	match left { case regexExprValue(contextID, leftCore, leftFast): match right { case regexExprValue(rightContext, rightCore, rightFast):
		if contextID != rightContext { panic("gosmt: erased regex difference context mismatch") }
		return regexExprValue(contextID, smt.DifferenceRegex(materializeRegex(leftCore, leftFast), materializeRegex(rightCore, rightFast)), regexFast{})
	} }
}

func ComplementRegexExpr(0 c nat, value RegexExpr[c]) RegexExpr[c] {
	match value { case regexExprValue(contextID, core, fast): return regexExprValue(contextID, smt.ComplementRegex(materializeRegex(core, fast)), regexFast{}) }
}

func StarRegexExpr(0 c nat, value RegexExpr[c]) RegexExpr[c] {
	match value { case regexExprValue(contextID, core, fast): return regexExprValue(contextID, smt.StarRegex(materializeRegex(core, fast)), regexFast{}) }
}

func PlusRegexExpr(0 c nat, value RegexExpr[c]) RegexExpr[c] {
	match value { case regexExprValue(contextID, core, fast): return regexExprValue(contextID, smt.PlusRegex(materializeRegex(core, fast)), regexFast{}) }
}

func OptionalRegexExpr(0 c nat, value RegexExpr[c]) RegexExpr[c] {
	match value { case regexExprValue(contextID, core, fast): return regexExprValue(contextID, smt.OptionalRegex(materializeRegex(core, fast)), regexFast{}) }
}

func LoopRegexExpr(0 c nat, minimum int, maximum int, value RegexExpr[c]) RegexExpr[c] {
	match value { case regexExprValue(contextID, core, fast): return regexExprValue(contextID, smt.LoopRegex(minimum, maximum, materializeRegex(core, fast)), regexFast{}) }
}

func InRegexString(0 c nat, value StringExpr[c], expression RegexExpr[c]) BoolExpr[c] {
	match value { case stringExprValue(contextID, term, fast): match expression { case regexExprValue(regexContext, core, regex):
		if contextID != regexContext { panic("gosmt: erased regex membership context mismatch") }
		if fast.kind == stringFastLiteral {
			if regex.kind == regexFastLiteral { return boolExprValue(contextID, smt.Bool{Value: fast.value == regex.value}, booleanFast{}) }
			if regex.kind == regexFastEmpty { return boolExprValue(contextID, smt.Bool{Value: false}, booleanFast{}) }
			if regex.kind == regexFastFull { return boolExprValue(contextID, smt.Bool{Value: true}, booleanFast{}) }
		}
		return fastBooleanAtom(contextID, smt.StringInRegex(materializeString(stringExprValue(contextID, term, fast)), materializeRegex(core, regex)))
	} }
}

func DatatypeConst(datatype nat, constructors nat, 0 c nat, context Context[c], name string, id int) DatatypeExpr[c, datatype, constructors] {
	match context { case contextValue(contextID): return datatypeExprValue(contextID, smt.DatatypeConst(datatype, constructors, id, name)) }
}

func DatatypeConstructor(datatype nat, constructors nat, constructor nat, 0 c nat, context Context[c], name string) DatatypeExpr[c, datatype, constructors] {
	match context { case contextValue(contextID): return datatypeExprValue(contextID, smt.DatatypeConstructor(datatype, constructors, constructor, name)) }
}

func DeclareRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, 0 c nat, context Context[c], name string, selectorName string) DatatypeRecursiveConstructor[c, datatype, constructors, constructor] {
	match context { case contextValue(contextID): return datatypeRecursiveConstructorValue(contextID, smt.DeclareRecursiveDatatypeConstructor(datatype, constructors, constructor, name, selectorName)) }
}

func ApplyRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration DatatypeRecursiveConstructor[c, datatype, constructors, constructor], value DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased recursive datatype constructor context mismatch") }
		return datatypeExprValue(contextID, smt.ApplyRecursiveDatatypeConstructor(core, term))
	} }
}

func SelectRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration DatatypeRecursiveConstructor[c, datatype, constructors, constructor], value DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased recursive datatype selector context mismatch") }
		return datatypeExprValue(contextID, smt.SelectRecursiveDatatypeConstructor(core, term))
	} }
}

func IsRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration DatatypeRecursiveConstructor[c, datatype, constructors, constructor], value DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match declaration { case datatypeRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased recursive datatype recognizer context mismatch") }
		return fastBooleanAtom(contextID, smt.IsRecursiveDatatypeConstructor(core, term))
	} }
}

func DeclareBinaryRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, 0 c nat, context Context[c], name string, firstSelectorName string, secondSelectorName string) DatatypeBinaryRecursiveConstructor[c, datatype, constructors, constructor] {
	match context { case contextValue(contextID): return datatypeBinaryRecursiveConstructorValue(contextID, smt.DeclareBinaryRecursiveDatatypeConstructor(datatype, constructors, constructor, name, firstSelectorName, secondSelectorName)) }
}

func ApplyBinaryRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration DatatypeBinaryRecursiveConstructor[c, datatype, constructors, constructor], first DatatypeExpr[c, datatype, constructors], second DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeBinaryRecursiveConstructorValue(contextID, core): match first { case datatypeExprValue(firstContext, firstTerm): match second { case datatypeExprValue(secondContext, secondTerm):
		if contextID != firstContext || contextID != secondContext { panic("gosmt: erased binary recursive datatype constructor context mismatch") }
		return datatypeExprValue(contextID, smt.ApplyBinaryRecursiveDatatypeConstructor(core, firstTerm, secondTerm))
	} } }
}

func FirstDatatypeField() smt.BinaryDatatypeField { return smt.FirstDatatypeField() }
func SecondDatatypeField() smt.BinaryDatatypeField { return smt.SecondDatatypeField() }

func SelectBinaryRecursiveDatatypeConstructor(field smt.BinaryDatatypeField, 0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration DatatypeBinaryRecursiveConstructor[c, datatype, constructors, constructor], value DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeBinaryRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased binary recursive datatype selector context mismatch") }
		return datatypeExprValue(contextID, smt.SelectBinaryRecursiveDatatypeConstructor(field, core, term))
	} }
}

func IsBinaryRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, declaration DatatypeBinaryRecursiveConstructor[c, datatype, constructors, constructor], value DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match declaration { case datatypeBinaryRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased binary recursive datatype recognizer context mismatch") }
		return fastBooleanAtom(contextID, smt.IsBinaryRecursiveDatatypeConstructor(core, term))
	} }
}

func DeclareNaryRecursiveDatatypeConstructor(datatype nat, constructors nat, constructor nat, arity nat, 0 c nat, context Context[c], name string, selectorNames vec.Vec[string, arity]) DatatypeNaryRecursiveConstructor[c, datatype, constructors, constructor, arity] {
	match context { case contextValue(contextID): return datatypeNaryRecursiveConstructorValue(contextID, smt.DeclareNaryRecursiveDatatypeConstructorCompact(int(datatype), int(constructors), int(constructor), name, naryDatatypeSelectorNames(selectorNames))) }
}

func ApplyNaryRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 arity nat, declaration DatatypeNaryRecursiveConstructor[c, datatype, constructors, constructor, arity], values vec.Vec[DatatypeExpr[c, datatype, constructors], arity]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeNaryRecursiveConstructorValue(contextID, core):
		return datatypeExprValue(contextID, smt.ApplyNaryRecursiveDatatypeConstructorCompact(core, naryDatatypeTerms(contextID, values)))
	}
}

func SelectNaryRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 arity nat, field vec.Fin[arity], declaration DatatypeNaryRecursiveConstructor[c, datatype, constructors, constructor, arity], value DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeNaryRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased n-ary recursive datatype selector context mismatch") }
		return datatypeExprValue(contextID, smt.SelectNaryRecursiveDatatypeConstructorDynamic(naryDatatypeFieldIndex(field), core, term))
	} }
}

func IsNaryRecursiveDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 arity nat, declaration DatatypeNaryRecursiveConstructor[c, datatype, constructors, constructor, arity], value DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match declaration { case datatypeNaryRecursiveConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term):
		if contextID != valueContext { panic("gosmt: erased n-ary recursive datatype recognizer context mismatch") }
		return fastBooleanAtom(contextID, smt.IsNaryRecursiveDatatypeConstructor(core, term))
	} }
}

func EmptyDatatypeMixedSignature() smt.MixedDatatypeSignature[smt.NoDatatypeFields] { return smt.EmptyMixedDatatypeSignature() }
func BoolDatatypeMixedField(name string, 0 tail smt.DatatypeFieldList, rest smt.MixedDatatypeSignature[tail]) smt.MixedDatatypeSignature[smt.DatatypeFieldCons(smt.BoolDatatypeFieldSort, tail)] { return smt.BoolDatatypeField(name, rest) }
func IntDatatypeMixedField(name string, 0 tail smt.DatatypeFieldList, rest smt.MixedDatatypeSignature[tail]) smt.MixedDatatypeSignature[smt.DatatypeFieldCons(smt.IntDatatypeFieldSort, tail)] { return smt.IntDatatypeField(name, rest) }
func RealDatatypeMixedField(name string, 0 tail smt.DatatypeFieldList, rest smt.MixedDatatypeSignature[tail]) smt.MixedDatatypeSignature[smt.DatatypeFieldCons(smt.RealDatatypeFieldSort, tail)] { return smt.RealDatatypeField(name, rest) }
func BitVecDatatypeMixedField(width nat, name string, 0 tail smt.DatatypeFieldList, rest smt.MixedDatatypeSignature[tail]) smt.MixedDatatypeSignature[smt.DatatypeFieldCons(smt.BitVecDatatypeFieldSort(width), tail)] { return smt.BitVecDatatypeField(width, name, rest) }
func SelfDatatypeMixedField(name string, 0 tail smt.DatatypeFieldList, rest smt.MixedDatatypeSignature[tail]) smt.MixedDatatypeSignature[smt.DatatypeFieldCons(smt.SelfDatatypeFieldSort, tail)] { return smt.SelfDatatypeField(name, rest) }
func DatatypeReferenceMixedField(targetDatatype nat, targetConstructors nat, name string, 0 tail smt.DatatypeFieldList, rest smt.MixedDatatypeSignature[tail]) smt.MixedDatatypeSignature[smt.DatatypeFieldCons(smt.DatatypeReferenceFieldSort(targetDatatype, targetConstructors), tail)] { return smt.DatatypeReferenceField(targetDatatype, targetConstructors, name, rest) }

func EmptyDatatypeMixedArguments(0 c nat, 0 datatype nat, 0 constructors nat, context Context[c]) DatatypeMixedArguments[c, datatype, constructors, smt.NoDatatypeFields] {
	match context { case contextValue(contextID): return datatypeMixedArgumentsValue(contextID, smt.EmptyMixedDatatypeArguments()) }
}
func EmptyDatatypeMixedArgumentsFor(datatype nat, constructors nat, 0 c nat, context Context[c]) DatatypeMixedArguments[c, datatype, constructors, smt.NoDatatypeFields] {
	match context { case contextValue(contextID): return datatypeMixedArgumentsValue(contextID, smt.EmptyMixedDatatypeArgumentsFor(datatype, constructors)) }
}

func BoolDatatypeMixedArgument(0 c nat, 0 datatype nat, 0 constructors nat, 0 tail smt.DatatypeFieldList, value BoolExpr[c], rest DatatypeMixedArguments[c, datatype, constructors, tail]) DatatypeMixedArguments[c, datatype, constructors, smt.DatatypeFieldCons(smt.BoolDatatypeFieldSort, tail)] {
	match value { case boolExprValue(contextID, term, _): match rest { case datatypeMixedArgumentsValue(restContext, core): if contextID != restContext { panic("gosmt: erased mixed datatype argument context mismatch") }; return datatypeMixedArgumentsValue(contextID, smt.BoolDatatypeArgument(term, core)) } }
}
func IntDatatypeMixedArgument(0 c nat, 0 datatype nat, 0 constructors nat, 0 tail smt.DatatypeFieldList, value IntExpr[c], rest DatatypeMixedArguments[c, datatype, constructors, tail]) DatatypeMixedArguments[c, datatype, constructors, smt.DatatypeFieldCons(smt.IntDatatypeFieldSort, tail)] {
	match value { case intExprValue(contextID, term, _): match rest { case datatypeMixedArgumentsValue(restContext, core): if contextID != restContext { panic("gosmt: erased mixed datatype argument context mismatch") }; return datatypeMixedArgumentsValue(contextID, smt.IntDatatypeArgument(term, core)) } }
}
func RealDatatypeMixedArgument(0 c nat, 0 datatype nat, 0 constructors nat, 0 tail smt.DatatypeFieldList, value RealExpr[c], rest DatatypeMixedArguments[c, datatype, constructors, tail]) DatatypeMixedArguments[c, datatype, constructors, smt.DatatypeFieldCons(smt.RealDatatypeFieldSort, tail)] {
	match value { case realExprValue(contextID, term, _): match rest { case datatypeMixedArgumentsValue(restContext, core): if contextID != restContext { panic("gosmt: erased mixed datatype argument context mismatch") }; return datatypeMixedArgumentsValue(contextID, smt.RealDatatypeArgument(term, core)) } }
}
func BitVecDatatypeMixedArgument(width nat, 0 c nat, 0 datatype nat, 0 constructors nat, 0 tail smt.DatatypeFieldList, value BitVecExpr[c, width], rest DatatypeMixedArguments[c, datatype, constructors, tail]) DatatypeMixedArguments[c, datatype, constructors, smt.DatatypeFieldCons(smt.BitVecDatatypeFieldSort(width), tail)] {
	match value { case bitVecExprValue(contextID, term, _): match rest { case datatypeMixedArgumentsValue(restContext, core): if contextID != restContext { panic("gosmt: erased mixed datatype argument context mismatch") }; return datatypeMixedArgumentsValue(contextID, smt.BitVecDatatypeArgument(width, term, core)) } }
}
func SelfDatatypeMixedArgument(0 c nat, 0 datatype nat, 0 constructors nat, 0 tail smt.DatatypeFieldList, value DatatypeExpr[c, datatype, constructors], rest DatatypeMixedArguments[c, datatype, constructors, tail]) DatatypeMixedArguments[c, datatype, constructors, smt.DatatypeFieldCons(smt.SelfDatatypeFieldSort, tail)] {
	match value { case datatypeExprValue(contextID, term): match rest { case datatypeMixedArgumentsValue(restContext, core): if contextID != restContext { panic("gosmt: erased mixed datatype argument context mismatch") }; return datatypeMixedArgumentsValue(contextID, smt.SelfDatatypeArgument(term, core)) } }
}
func DatatypeReferenceMixedArgument(targetDatatype nat, targetConstructors nat, 0 c nat, 0 datatype nat, 0 constructors nat, 0 tail smt.DatatypeFieldList, value DatatypeExpr[c, targetDatatype, targetConstructors], rest DatatypeMixedArguments[c, datatype, constructors, tail]) DatatypeMixedArguments[c, datatype, constructors, smt.DatatypeFieldCons(smt.DatatypeReferenceFieldSort(targetDatatype, targetConstructors), tail)] {
	match value { case datatypeExprValue(contextID, term): match rest { case datatypeMixedArgumentsValue(restContext, core): if contextID != restContext { panic("gosmt: erased datatype reference argument context mismatch") }; return datatypeMixedArgumentsValue(contextID, smt.DatatypeReferenceArgument(targetDatatype, targetConstructors, term, core)) } }
}

func DeclareMixedDatatypeConstructor(datatype nat, constructors nat, constructor nat, 0 c nat, 0 fields smt.DatatypeFieldList, context Context[c], name string, signature smt.MixedDatatypeSignature[fields]) DatatypeMixedConstructor[c, datatype, constructors, constructor, fields] {
	match context { case contextValue(contextID): return datatypeMixedConstructorValue(contextID, smt.DeclareMixedRecursiveDatatypeConstructor(datatype, constructors, constructor, name, signature)) }
}
func ApplyMixedDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields smt.DatatypeFieldList, declaration DatatypeMixedConstructor[c, datatype, constructors, constructor, fields], arguments DatatypeMixedArguments[c, datatype, constructors, fields]) DatatypeExpr[c, datatype, constructors] {
	match declaration { case datatypeMixedConstructorValue(contextID, core): match arguments { case datatypeMixedArgumentsValue(argumentContext, values): if contextID != argumentContext { panic("gosmt: erased mixed datatype constructor context mismatch") }; return datatypeExprValue(contextID, smt.ApplyMixedRecursiveDatatypeConstructor(core, values)) } }
}
func MixedDatatypeFields(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields smt.DatatypeFieldList, declaration DatatypeMixedConstructor[c, datatype, constructors, constructor, fields]) DatatypeMixedCursor[c, datatype, constructors, constructor, fields] {
	match declaration { case datatypeMixedConstructorValue(contextID, core): return datatypeMixedCursorValue(contextID, smt.MixedDatatypeFields(core)) }
}
func NextMixedDatatypeField(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 head smt.DatatypeFieldSort, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(head, tail)]) DatatypeMixedCursor[c, datatype, constructors, constructor, tail] {
	match cursor { case datatypeMixedCursorValue(contextID, core): return datatypeMixedCursorValue(contextID, smt.NextMixedDatatypeField(core)) }
}
func SelectMixedBoolDatatypeField(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(smt.BoolDatatypeFieldSort, tail)], value DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match cursor { case datatypeMixedCursorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased mixed datatype selector context mismatch") }; return boolExprValue(contextID, smt.SelectMixedBoolDatatypeField(core, term), booleanFast{}) } }
}
func SelectMixedIntDatatypeField(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(smt.IntDatatypeFieldSort, tail)], value DatatypeExpr[c, datatype, constructors]) IntExpr[c] {
	match cursor { case datatypeMixedCursorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased mixed datatype selector context mismatch") }; return intExprValue(contextID, smt.SelectMixedIntDatatypeField(core, term), integerFast{}) } }
}
func SelectMixedRealDatatypeField(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(smt.RealDatatypeFieldSort, tail)], value DatatypeExpr[c, datatype, constructors]) RealExpr[c] {
	match cursor { case datatypeMixedCursorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased mixed datatype selector context mismatch") }; return realExprValue(contextID, smt.SelectMixedRealDatatypeField(core, term), realFast{}) } }
}
func SelectMixedBitVecDatatypeField(width nat, 0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(smt.BitVecDatatypeFieldSort(width), tail)], value DatatypeExpr[c, datatype, constructors]) BitVecExpr[c, width] {
	match cursor { case datatypeMixedCursorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased mixed datatype selector context mismatch") }; return bitVecExprValue(contextID, smt.SelectMixedBitVecDatatypeField(width, core, term), bitVectorFast{}) } }
}
func SelectMixedSelfDatatypeField(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(smt.SelfDatatypeFieldSort, tail)], value DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, datatype, constructors] {
	match cursor { case datatypeMixedCursorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased mixed datatype selector context mismatch") }; return datatypeExprValue(contextID, smt.SelectMixedSelfDatatypeField(core, term)) } }
}
func SelectMixedDatatypeReferenceField(targetDatatype nat, targetConstructors nat, 0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 tail smt.DatatypeFieldList, cursor DatatypeMixedCursor[c, datatype, constructors, constructor, smt.DatatypeFieldCons(smt.DatatypeReferenceFieldSort(targetDatatype, targetConstructors), tail)], value DatatypeExpr[c, datatype, constructors]) DatatypeExpr[c, targetDatatype, targetConstructors] {
	match cursor { case datatypeMixedCursorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased datatype reference selector context mismatch") }; return datatypeExprValue(contextID, smt.SelectMixedDatatypeReferenceField(targetDatatype, targetConstructors, core, term)) } }
}
func IsMixedDatatypeConstructor(0 c nat, 0 datatype nat, 0 constructors nat, 0 constructor nat, 0 fields smt.DatatypeFieldList, declaration DatatypeMixedConstructor[c, datatype, constructors, constructor, fields], value DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match declaration { case datatypeMixedConstructorValue(contextID, core): match value { case datatypeExprValue(valueContext, term): if contextID != valueContext { panic("gosmt: erased mixed datatype recognizer context mismatch") }; return boolExprValue(contextID, smt.IsMixedRecursiveDatatypeConstructor(core, term), booleanFast{}) } }
}

func EqDatatype(0 c nat, 0 datatype nat, 0 constructors nat, left DatatypeExpr[c, datatype, constructors], right DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match left { case datatypeExprValue(contextID, leftTerm): match right { case datatypeExprValue(rightContext, rightTerm):
		if contextID != rightContext { panic("gosmt: erased datatype equality context mismatch") }
		return fastBooleanAtom(contextID, smt.Equal(leftTerm, rightTerm))
	} }
}

func IsDatatypeConstructor(datatype nat, constructors nat, constructor nat, 0 c nat, value DatatypeExpr[c, datatype, constructors]) BoolExpr[c] {
	match value { case datatypeExprValue(contextID, term): return fastBooleanAtom(contextID, smt.IsDatatypeConstructor(datatype, constructors, constructor, term)) }
}

func IntConst(0 c nat, context Context[c], name string, id int) IntExpr[c] {
	match context { case contextValue(contextID): return intExprValue(contextID, smt.IntegerVariable(id), integerFast{}) }
}

func IntVal(0 c nat, context Context[c], value int64) IntExpr[c] {
	match context { case contextValue(contextID): return intExprValue(contextID, smt.Integer(value), integerFast{}) }
}

func ParseInteger(value string) (smt.IntegerValue, error) { return smt.ParseIntegerValue(value) }

func IntValExact(0 c nat, context Context[c], value smt.IntegerValue) IntExpr[c] {
	match context { case contextValue(contextID): return intExprValue(contextID, smt.IntegerTerm(value), integerFast{}) }
}

func Rational(numerator int64, denominator int64) smt.Rational { return smt.NewRational(numerator, denominator) }
func ParseRational(value string) (smt.Rational, error) { return smt.ParseRational(value) }
func CompareRational(left smt.Rational, right smt.Rational) int { return smt.CompareRational(left, right) }

func RealConst(0 c nat, context Context[c], name string, id int) RealExpr[c] {
	match context { case contextValue(contextID): return fastRealSymbol(contextID, id) }
}

func RealVal(0 c nat, context Context[c], value smt.Rational) RealExpr[c] {
	match context { case contextValue(contextID): return fastRealValue(contextID, value) }
}

func BitVecValue(width nat, 0 c nat, context Context[c], value uint64) BitVecExpr[c, width] {
	match context { case contextValue(contextID): return fastBitVectorValue(contextID, int(width), value) }
}

func BitVecConst(width nat, 0 c nat, context Context[c], name string, id int) BitVecExpr[c, width] {
	match context { case contextValue(contextID): return fastBitVectorSymbol(contextID, int(width), id, name) }
}

// BvToNat interprets a bit vector as an unsigned mathematical integer.
func BvToNat(0 c nat, 0 width nat, value BitVecExpr[c, width]) IntExpr[c] {
	match value {
	case bitVecExprValue(contextID, term, fast):
		return fastBitVectorToInteger(contextID, term, fast, false)
	}
}

// BvToInt interprets a bit vector using two's-complement signed semantics.
func BvToInt(0 c nat, 0 width nat, value BitVecExpr[c, width]) IntExpr[c] {
	match value {
	case bitVecExprValue(contextID, term, fast):
		return fastBitVectorToInteger(contextID, term, fast, true)
	}
}

// IntToBitVec reduces an integer modulo 2^width. Its result width remains a
// dependent index, so mismatched widths are rejected by Go+ at compile time.
func IntToBitVec(width nat, 0 c nat, value IntExpr[c]) BitVecExpr[c, width] {
	match value {
	case intExprValue(contextID, term, fast):
		return bitVecExprValue(contextID, smt.IntToBitVec(width, materializeInteger(term, fast)), bitVectorFast{})
	}
}

func ArrayConst[I any, E any](0 c nat, context Context[c], name string, id int) ArrayExpr[c, I, E] {
	match context { case contextValue(contextID): return arrayExprValue(contextID, smt.ArrayConst[I, E](id, name), arrayFast{}) }
}

func ConstArray[I any, E any](0 c nat, context Context[c], value smt.Term[E]) ArrayExpr[c, I, E] {
	match context { case contextValue(contextID): return arrayExprValue(contextID, smt.ConstArray[I, E](value), arrayFast{}) }
}

func SelectArray[I any, E any](0 c nat, array ArrayExpr[c, I, E], index smt.Term[I]) smt.Term[E] {
	match array { case arrayExprValue(_, term, fast): return smt.Select(materializeArray(term, fast), index) }
}

func StoreArray[I any, E any](0 c nat, array ArrayExpr[c, I, E], index smt.Term[I], value smt.Term[E]) ArrayExpr[c, I, E] {
	match array { case arrayExprValue(contextID, term, fast): return arrayExprValue(contextID, smt.Store(materializeArray(term, fast), index, value), arrayFast{}) }
}

func EqArray[I any, E any](0 c nat, left ArrayExpr[c, I, E], right ArrayExpr[c, I, E]) BoolExpr[c] {
	match left {
	case arrayExprValue(contextID, leftTerm, leftFast):
		match right {
		case arrayExprValue(rightContext, rightTerm, rightFast):
			if contextID != rightContext { panic("gosmt: erased array context mismatch") }
			return fastEqArray(contextID, leftTerm, leftFast, rightTerm, rightFast)
		}
	}
}

func IntArrayConst(0 c nat, context Context[c], name string, id int) ArrayExpr[c, smt.IntSort, smt.IntSort] {
	match context { case contextValue(contextID): return fastIntArraySymbol(contextID, id, name) }
}

func ConstIntArray(0 c nat, value IntExpr[c]) ArrayExpr[c, smt.IntSort, smt.IntSort] {
	match value { case intExprValue(contextID, term, fast): return fastConstIntArray(contextID, materializeInteger(term, fast)) }
}

func SelectIntArray(0 c nat, array ArrayExpr[c, smt.IntSort, smt.IntSort], index IntExpr[c]) IntExpr[c] {
	match array {
	case arrayExprValue(contextID, term, fast):
		match index {
		case intExprValue(indexContext, indexTerm, indexFast):
			if contextID != indexContext { panic("gosmt: erased array/index context mismatch") }
			return selectIntArray(contextID, term, fast, materializeInteger(indexTerm, indexFast))
		}
	}
}

func StoreIntArray(0 c nat, array ArrayExpr[c, smt.IntSort, smt.IntSort], index IntExpr[c], value IntExpr[c]) ArrayExpr[c, smt.IntSort, smt.IntSort] {
	match array {
	case arrayExprValue(contextID, term, fast):
		match index {
		case intExprValue(indexContext, indexTerm, indexFast):
			match value {
			case intExprValue(valueContext, valueTerm, valueFast):
				if contextID != indexContext || contextID != valueContext { panic("gosmt: erased array store context mismatch") }
				return storeIntArray(contextID, term, fast, materializeInteger(indexTerm, indexFast), materializeInteger(valueTerm, valueFast))
			}
		}
	}
}

func BitVecArrayConst(indexWidth nat, elementWidth nat, 0 c nat, context Context[c], name string, id int) BitVecArrayExpr[c, indexWidth, elementWidth] {
	match context { case contextValue(contextID): return fastBitVectorArraySymbol(contextID, int(indexWidth), int(elementWidth), id, name) }
}

func ConstBitVecArray(indexWidth nat, 0 c nat, 0 elementWidth nat, value BitVecExpr[c, elementWidth]) BitVecArrayExpr[c, indexWidth, elementWidth] {
	match value { case bitVecExprValue(contextID, term, fast): return bitVecArrayExprValue(contextID, smt.ConstArray[smt.BitVecSort[indexWidth], smt.BitVecSort[elementWidth]](materializeBitVector(term, fast)), bitVecArrayFast{}) }
}

func SelectBitVecArray(0 c nat, 0 indexWidth nat, 0 elementWidth nat, array BitVecArrayExpr[c, indexWidth, elementWidth], index BitVecExpr[c, indexWidth]) BitVecExpr[c, elementWidth] {
	match array {
	case bitVecArrayExprValue(contextID, term, arrayFast):
		match index {
		case bitVecExprValue(indexContext, indexTerm, indexFast):
			if contextID != indexContext { panic("gosmt: erased bit-vector array/index context mismatch") }
			if value, width, ok := selectFastBitVectorArray(arrayFast, indexFast); ok { return fastBitVectorValue(contextID, width, value) }
			if value, ok := selectSymbolicBitVectorArray(contextID, arrayFast, indexFast); ok { return value }
			return bitVecExprValue(contextID, smt.Select(materializeBitVectorArray(term, arrayFast), materializeBitVector(indexTerm, indexFast)), bitVectorFast{})
		}
	}
}

func StoreBitVecArray(0 c nat, 0 indexWidth nat, 0 elementWidth nat, array BitVecArrayExpr[c, indexWidth, elementWidth], index BitVecExpr[c, indexWidth], value BitVecExpr[c, elementWidth]) BitVecArrayExpr[c, indexWidth, elementWidth] {
	match array {
	case bitVecArrayExprValue(contextID, term, arrayFast):
		match index {
		case bitVecExprValue(indexContext, indexTerm, indexFast):
			match value {
			case bitVecExprValue(valueContext, valueTerm, valueFast):
				if contextID != indexContext || contextID != valueContext { panic("gosmt: erased bit-vector array store context mismatch") }
				if stored, ok := storeFastBitVectorArray(arrayFast, indexFast, valueFast); ok { return bitVecArrayExprValue(contextID, term, stored) }
				return bitVecArrayExprValue(contextID, smt.Store(materializeBitVectorArray(term, arrayFast), materializeBitVector(indexTerm, indexFast), materializeBitVector(valueTerm, valueFast)), bitVecArrayFast{})
			}
		}
	}
}

func EqBitVecArray(0 c nat, 0 indexWidth nat, 0 elementWidth nat, left BitVecArrayExpr[c, indexWidth, elementWidth], right BitVecArrayExpr[c, indexWidth, elementWidth]) BoolExpr[c] {
	match left {
	case bitVecArrayExprValue(contextID, leftTerm, leftFast):
		match right {
		case bitVecArrayExprValue(rightContext, rightTerm, rightFast):
			if contextID != rightContext { panic("gosmt: erased bit-vector array context mismatch") }
			if result, ok := fastEqBitVectorArray(contextID, leftFast, rightFast); ok { return result }
			return fastBooleanAtom(contextID, smt.Equal{Left: materializeBitVectorArray(leftTerm, leftFast), Right: materializeBitVectorArray(rightTerm, rightFast)})
		}
	}
}

func NotBitVec(0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, width] {
	return fastNotBitVector(value)
}

func AndBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return fastAndBitVector(left, right)
}

func OrBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 2)
}

func XorBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 3)
}

func AddBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 4)
}

func SubBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 5)
}

func MulBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 6)
}

func ShlBitVec(0 c nat, 0 width nat, value BitVecExpr[c, width], amount BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(value, amount, 7)
}

func LshrBitVec(0 c nat, 0 width nat, value BitVecExpr[c, width], amount BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(value, amount, 8)
}

func AshrBitVec(0 c nat, 0 width nat, value BitVecExpr[c, width], amount BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(value, amount, 9)
}

func UdivBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 10)
}

func UremBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 11)
}

func SdivBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 12)
}

func SremBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BitVecExpr[c, width] {
	return binaryBitVector(left, right, 13)
}

func UaddOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 1)
}

func SaddOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 2)
}

func UsubOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 3)
}

func SsubOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 4)
}

func UmulOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 5)
}

func SmulOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 6)
}

func SdivOverflowBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return overflowBitVector(left, right, 7)
}

func NegOverflowBitVec(0 c nat, 0 width nat, value BitVecExpr[c, width]) BoolExpr[c] {
	return negOverflowBitVector(value)
}

func ConcatBitVec(firstWidth nat, secondWidth nat, 0 c nat, first BitVecExpr[c, firstWidth], second BitVecExpr[c, secondWidth]) BitVecExpr[c, firstWidth+secondWidth] {
	return concatBitVector(int(firstWidth), int(secondWidth), first, second)
}

func ExtractBitVec(high nat, low nat, 0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, high-low+1] {
	return extractBitVector(int(high), int(low), value)
}

func ZeroExtendBitVec(additional nat, 0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, width+additional] {
	return extendBitVector(int(additional), value, false)
}

func SignExtendBitVec(additional nat, 0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, width+additional] {
	return extendBitVector(int(additional), value, true)
}

func RotateLeftBitVec(amount nat, 0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, width] {
	return rotateBitVector(int(amount), value, true)
}

func RotateRightBitVec(amount nat, 0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, width] {
	return rotateBitVector(int(amount), value, false)
}

func RepeatBitVec(count nat, 0 c nat, 0 width nat, value BitVecExpr[c, width]) BitVecExpr[c, width*count] {
	return repeatBitVector(int(count), value)
}

func EqBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return fastEqBitVector(left, right)
}

func UltBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return fastOrderBitVector(left, right, 1)
}

func UleBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return fastOrderBitVector(left, right, 2)
}

func SltBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return fastOrderBitVector(left, right, 3)
}

func SleBitVec(0 c nat, 0 width nat, left BitVecExpr[c, width], right BitVecExpr[c, width]) BoolExpr[c] {
	return fastOrderBitVector(left, right, 4)
}

func ModelBitVec(0 c nat, 0 a nat, 0 width nat, model Model[c, a], term BitVecExpr[c, width]) (smt.BitVectorValue, bool) {
	match model {
	case modelValue(contextID, core):
		match term {
		case bitVecExprValue(termContext, value, fast):
			if contextID != termContext { panic("gosmt: erased bit-vector model context mismatch") }
			return smt.BitVecModelValue(core, materializeBitVector(value, fast))
		}
	}
}

func DeclareRealFunction(0 c nat, context Context[c], name string, id int) RealFunc[c] {
	match context { case contextValue(contextID): return fastRealFunction(contextID, id, name) }
}

func ApplyRealFunction(0 c nat, function RealFunc[c], argument RealExpr[c]) RealExpr[c] {
	return applyRealFunction(function, argument)
}

func DeclareRealBinary(0 c nat, context Context[c], name string, id int) RealBinaryFunc[c] {
	match context { case contextValue(contextID): return fastRealBinaryFunction(contextID, id, name) }
}

func ApplyRealBinary(0 c nat, function RealBinaryFunc[c], first RealExpr[c], second RealExpr[c]) RealExpr[c] {
	return applyRealBinaryFunction(function, first, second)
}

func DeclareBitVecFunction(domainWidth nat, rangeWidth nat, 0 c nat, context Context[c], name string, id int) BitVecFunc[c, domainWidth, rangeWidth] {
	match context { case contextValue(contextID): return bitVecFuncValue(contextID, smt.DeclareBitVecUnaryFunction(domainWidth, rangeWidth, id, name)) }
}

func ApplyBitVecFunction(0 c nat, 0 domainWidth nat, 0 rangeWidth nat, function BitVecFunc[c, domainWidth, rangeWidth], argument BitVecExpr[c, domainWidth]) BitVecExpr[c, rangeWidth] {
	match function {
	case bitVecFuncValue(contextID, core):
		match argument {
		case bitVecExprValue(_, _, _):
			return applyBitVectorFunction(contextID, core, argument)
		}
	}
}

func DeclareBitVecBinary(firstWidth nat, secondWidth nat, rangeWidth nat, 0 c nat, context Context[c], name string, id int) BitVecBinaryFunc[c, firstWidth, secondWidth, rangeWidth] {
	match context { case contextValue(contextID): return bitVecBinaryFuncValue(contextID, smt.DeclareBitVecBinaryFunction(firstWidth, secondWidth, rangeWidth, id, name)) }
}

func ApplyBitVecBinary(0 c nat, 0 firstWidth nat, 0 secondWidth nat, 0 rangeWidth nat, function BitVecBinaryFunc[c, firstWidth, secondWidth, rangeWidth], first BitVecExpr[c, firstWidth], second BitVecExpr[c, secondWidth]) BitVecExpr[c, rangeWidth] {
	match function {
	case bitVecBinaryFuncValue(contextID, core):
		match first {
		case bitVecExprValue(firstContext, firstTerm, firstFast):
			match second {
			case bitVecExprValue(secondContext, secondTerm, secondFast):
				if contextID != firstContext || contextID != secondContext { panic("gosmt: erased binary bit-vector function context mismatch") }
				return bitVecExprValue(contextID, smt.ApplyBitVecBinary(core, materializeBitVector(firstTerm, firstFast), materializeBitVector(secondTerm, secondFast)), bitVectorFast{})
			}
		}
	}
}

func UninterpretedConst(sort nat, 0 c nat, context Context[c], name string, id int) UninterpretedExpr[c, sort] {
	match context { case contextValue(contextID): return fastUninterpretedSymbol(contextID, int(sort), id, name) }
}

func DeclareUnary(domain nat, codomain nat, 0 c nat, context Context[c], name string, id int) UnaryFunc[c, domain, codomain] {
	match context { case contextValue(contextID): return fastUninterpretedUnaryFunction(contextID, int(domain), int(codomain), id, name) }
}

func DeclareBinary(first nat, second nat, codomain nat, 0 c nat, context Context[c], name string, id int) BinaryFunc[c, first, second, codomain] {
	match context { case contextValue(contextID): return fastUninterpretedBinaryFunction(contextID, int(first), int(second), int(codomain), id, name) }
}

func ApplyUninterpreted(0 c nat, 0 domain nat, 0 codomain nat, function UnaryFunc[c, domain, codomain], argument UninterpretedExpr[c, domain]) UninterpretedExpr[c, codomain] {
	return fastApplyUninterpreted(function, argument)
}

func ApplyBinaryUninterpreted(0 c nat, 0 first nat, 0 second nat, 0 codomain nat, function BinaryFunc[c, first, second, codomain], left UninterpretedExpr[c, first], right UninterpretedExpr[c, second]) UninterpretedExpr[c, codomain] {
	return fastApplyBinaryUninterpreted(function, left, right)
}

func EqUninterpreted(0 c nat, 0 sort nat, left UninterpretedExpr[c, sort], right UninterpretedExpr[c, sort]) BoolExpr[c] {
	return fastEqUninterpreted(left, right)
}

func Not(0 c nat, value BoolExpr[c]) BoolExpr[c] {
	return fastNot(value)
}

func And(0 c nat, values ...BoolExpr[c]) BoolExpr[c] {
	return fastAnd(values)
}

func Or(0 c nat, values ...BoolExpr[c]) BoolExpr[c] {
	return fastOr(values)
}

func ImpliesBool(0 c nat, left BoolExpr[c], right BoolExpr[c]) BoolExpr[c] {
	return Or(Not(left), right)
}

func IffBool(0 c nat, left BoolExpr[c], right BoolExpr[c]) BoolExpr[c] {
	return And(ImpliesBool(left, right), ImpliesBool(right, left))
}

func EqBool(0 c nat, left BoolExpr[c], right BoolExpr[c]) BoolExpr[c] {
	match left { case boolExprValue(leftContext, leftTerm, leftFast):
		match right { case boolExprValue(rightContext, rightTerm, rightFast):
			if leftContext != rightContext { panic("gosmt: erased Boolean equality context mismatch") }
			return boolExprValue(leftContext, smt.Equal{Left: materializeBoolean(leftTerm, leftFast), Right: materializeBoolean(rightTerm, rightFast)}, booleanFast{})
		}
	}
}

func Add(0 c nat, values ...IntExpr[c]) IntExpr[c] {
	context, terms := integerTerms(values)
	return intExprValue(context, smt.Add(terms), integerFast{})
}

func Sub(0 c nat, left IntExpr[c], right IntExpr[c]) IntExpr[c] {
	return subtractInteger(left, right)
}

func ScaleInt(0 c nat, coefficient smt.IntegerValue, value IntExpr[c]) IntExpr[c] {
	match value { case intExprValue(contextID, term, fast): return intExprValue(contextID, smt.ScaleInteger(coefficient, materializeInteger(term, fast)), integerFast{}) }
}

func ScaleInt64(0 c nat, coefficient int64, value IntExpr[c]) IntExpr[c] {
	return ScaleInt(smt.NewIntegerValue(coefficient), value)
}

func DivInt(0 c nat, value IntExpr[c], divisor smt.IntegerValue) IntExpr[c] {
	match value { case intExprValue(contextID, term, fast): return intExprValue(contextID, smt.DivInteger(materializeInteger(term, fast), divisor), integerFast{}) }
}

func ModInt(0 c nat, value IntExpr[c], divisor smt.IntegerValue) IntExpr[c] {
	match value { case intExprValue(contextID, term, fast): return intExprValue(contextID, smt.ModInteger(materializeInteger(term, fast), divisor), integerFast{}) }
}

func DivInt64(0 c nat, value IntExpr[c], divisor int64) IntExpr[c] {
	return DivInt(value, smt.NewIntegerValue(divisor))
}

func ModInt64(0 c nat, value IntExpr[c], divisor int64) IntExpr[c] {
	return ModInt(value, smt.NewIntegerValue(divisor))
}

func Le(0 c nat, left IntExpr[c], right IntExpr[c]) BoolExpr[c] {
	return compareInteger(left, right, false)
}

func Lt(0 c nat, left IntExpr[c], right IntExpr[c]) BoolExpr[c] {
	return compareInteger(left, right, true)
}

func EqInt(0 c nat, left IntExpr[c], right IntExpr[c]) BoolExpr[c] {
	return fastEqInteger(left, right)
}

func NeInt(0 c nat, left IntExpr[c], right IntExpr[c]) BoolExpr[c] {
	return Not(EqInt(left, right))
}

func AddReal(0 c nat, values ...RealExpr[c]) RealExpr[c] {
	return fastAddReal(values)
}

func SubReal(0 c nat, left RealExpr[c], right RealExpr[c]) RealExpr[c] {
	return fastSubReal(left, right)
}

func ScaleReal(0 c nat, coefficient smt.Rational, value RealExpr[c]) RealExpr[c] {
	return fastScaleReal(coefficient, value)
}

func LeReal(0 c nat, left RealExpr[c], right RealExpr[c]) BoolExpr[c] {
	return fastRealRelation(left, right, false)
}

func LtReal(0 c nat, left RealExpr[c], right RealExpr[c]) BoolExpr[c] {
	return fastRealRelation(left, right, true)
}

func EqReal(0 c nat, left RealExpr[c], right RealExpr[c]) BoolExpr[c] {
	return fastEqReal(left, right)
}

func NewSolver(0 c nat, context Context[c]) Solver[c, 0, 0] {
	match context { case contextValue(contextID): return solverValue(contextID, smt.New()) }
}

func Assert(assertion nat, 0 c nat, 0 a nat, 0 d nat, solver Solver[c, a, d], formula BoolExpr[c]) Solver[c, smt.ContextID(a, assertion), d] {
	match solver {
	case solverValue(context, core):
		match formula {
		case boolExprValue(formulaContext, term, fast):
			if context != formulaContext { panic("gosmt: erased context mismatch") }
			return solverValue(context, smt.Assert(assertion, core, materializeBoolean(term, fast)))
		}
	}
}

func Check(0 c nat, 0 a nat, 0 d nat, solver Solver[c, a, d]) Result[c, a] {
	match solver {
	case solverValue(context, core):
		return cachedCheckResult(context, core)
	}
}

func CheckAssuming(0 c nat, 0 a nat, 0 d nat, solver Solver[c, a, d], assumptions ...BoolExpr[c]) AssumptionResult[c, a] {
	match solver {
	case solverValue(context, core):
		terms := assumptionTerms(context, assumptions)
		match smt.CheckAssuming(core, terms...) {
		case smt.AssumptionsSatisfiable(model): return AssumptionSat(modelValue(context, model))
		case smt.AssumptionsUnsatisfiable(proof, indices): return AssumptionUnsat(contextValue(context), proof, indices)
		case smt.AssumptionsUnknown(proof, reason): return AssumptionUnknown(contextValue(context), proof, reason)
		}
	}
}

func EvalBool(0 c nat, 0 a nat, model Model[c, a], expression BoolExpr[c]) (bool, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case boolExprValue(expressionContext, term, fast):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			return smt.BoolValue(core, materializeBoolean(term, fast))
		}
	}
}

func EvalInt(0 c nat, 0 a nat, model Model[c, a], expression IntExpr[c]) (int64, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case intExprValue(expressionContext, term, fast):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			materialized := materializeInteger(term, fast)
			value, found := smt.IntValue(core, materialized)
			if found { return value, true }
			return smt.StringIntegerModelValue(core, materialized)
		}
	}
}

func EvalIntExact(0 c nat, 0 a nat, model Model[c, a], expression IntExpr[c]) (smt.IntegerValue, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case intExprValue(expressionContext, term, fast):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			materialized := materializeInteger(term, fast)
			value, found := smt.IntegerModelValue(core, materialized)
			if found { return value, true }
			return smt.ExactStringIntegerModelValue(core, materialized)
		}
	}
}

func EvalDatatype(datatype nat, constructors nat, 0 c nat, 0 a nat, model Model[c, a], expression DatatypeExpr[c, datatype, constructors]) (smt.DatatypeValue, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case datatypeExprValue(expressionContext, term):
			if context != expressionContext { panic("gosmt: erased model/datatype context mismatch") }
			return smt.DatatypeModelValue(datatype, constructors, core, term)
		}
	}
}

func EvalIntArray(0 c nat, 0 a nat, model Model[c, a], array ArrayExpr[c, smt.IntSort, smt.IntSort], index smt.IntegerValue) (smt.IntegerValue, bool) {
	match model {
	case modelValue(context, core):
		match array {
		case arrayExprValue(arrayContext, term, fast):
			if context != arrayContext { panic("gosmt: erased model/array context mismatch") }
			return smt.IntegerArrayValue(core, materializeArray(term, fast), index)
		}
	}
}

func EvalBitVecArray(0 c nat, 0 a nat, 0 indexWidth nat, 0 elementWidth nat, model Model[c, a], array BitVecArrayExpr[c, indexWidth, elementWidth], index smt.BitVectorValue) (smt.BitVectorValue, bool) {
	match model {
	case modelValue(context, core):
		match array {
		case bitVecArrayExprValue(arrayContext, term, fast):
			if context != arrayContext { panic("gosmt: erased model/bit-vector-array context mismatch") }
			return smt.BitVectorArrayValue(core, materializeBitVectorArray(term, fast), index)
		}
	}
}

func EvalReal(0 c nat, 0 a nat, model Model[c, a], expression RealExpr[c]) (smt.Rational, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case realExprValue(expressionContext, term, fast):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			return smt.RealValue(core, materializeReal(term, fast))
		}
	}
}

func EvalString(0 c nat, 0 a nat, model Model[c, a], expression StringExpr[c]) (string, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case stringExprValue(expressionContext, term, fast):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			return smt.StringModelValue(core, materializeString(stringExprValue(expressionContext, term, fast)))
		}
	}
}
