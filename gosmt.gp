// Package gosmt exposes Z3-shaped, context-indexed solver construction over
// the essential Go+ standard-library SMT core.
package gosmt

import (
	smt "goforge.dev/goplus/std/smt"
	"goforge.dev/goplus/std/smtlib"
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
type IntExpr[c nat] enum { intExprValue(ContextID int, Term smt.Term[smt.IntSort]) IntExpr[c] }
//goplus:derive off
//goplus:repr transparent
type RealExpr[c nat] enum { realExprValue(ContextID int, Term smt.Term[smt.RealSort], Fast realFast) RealExpr[c] }
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
type UninterpretedExpr[c nat, s nat] enum { uninterpretedExprValue(ContextID int, Term smt.Term[smt.UninterpretedSort[s]]) UninterpretedExpr[c, s] }
//goplus:derive off
//goplus:repr transparent
type UnaryFunc[c nat, d nat, r nat] enum { unaryFuncValue(ContextID int, Function smt.UnaryFunction[d, r]) UnaryFunc[c, d, r] }
//goplus:derive off
//goplus:repr transparent
type BinaryFunc[c nat, a nat, b nat, r nat] enum { binaryFuncValue(ContextID int, Function smt.BinaryFunction[a, b, r]) BinaryFunc[c, a, b, r] }
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

func IntConst(0 c nat, context Context[c], name string, id int) IntExpr[c] {
	match context { case contextValue(contextID): return intExprValue(contextID, smt.IntegerVariable(id)) }
}

func IntVal(0 c nat, context Context[c], value int64) IntExpr[c] {
	match context { case contextValue(contextID): return intExprValue(contextID, smt.Integer(value)) }
}

func ParseInteger(value string) (smt.IntegerValue, error) { return smt.ParseIntegerValue(value) }

func IntValExact(0 c nat, context Context[c], value smt.IntegerValue) IntExpr[c] {
	match context { case contextValue(contextID): return intExprValue(contextID, smt.IntegerTerm(value)) }
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
		return intExprValue(contextID, smt.BitVecToNat(materializeBitVector(term, fast)))
	}
}

// BvToInt interprets a bit vector using two's-complement signed semantics.
func BvToInt(0 c nat, 0 width nat, value BitVecExpr[c, width]) IntExpr[c] {
	match value {
	case bitVecExprValue(contextID, term, fast):
		return intExprValue(contextID, smt.BitVecToInt(materializeBitVector(term, fast)))
	}
}

// IntToBitVec reduces an integer modulo 2^width. Its result width remains a
// dependent index, so mismatched widths are rejected by Go+ at compile time.
func IntToBitVec(width nat, 0 c nat, value IntExpr[c]) BitVecExpr[c, width] {
	match value {
	case intExprValue(contextID, term):
		return bitVecExprValue(contextID, smt.IntToBitVec(width, term), bitVectorFast{})
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
	match value { case intExprValue(contextID, term): return fastConstIntArray(contextID, term) }
}

func SelectIntArray(0 c nat, array ArrayExpr[c, smt.IntSort, smt.IntSort], index IntExpr[c]) IntExpr[c] {
	match array {
	case arrayExprValue(contextID, term, fast):
		match index {
		case intExprValue(indexContext, indexTerm):
			if contextID != indexContext { panic("gosmt: erased array/index context mismatch") }
			return selectIntArray(contextID, term, fast, indexTerm)
		}
	}
}

func StoreIntArray(0 c nat, array ArrayExpr[c, smt.IntSort, smt.IntSort], index IntExpr[c], value IntExpr[c]) ArrayExpr[c, smt.IntSort, smt.IntSort] {
	match array {
	case arrayExprValue(contextID, term, fast):
		match index {
		case intExprValue(indexContext, indexTerm):
			match value {
			case intExprValue(valueContext, valueTerm):
				if contextID != indexContext || contextID != valueContext { panic("gosmt: erased array store context mismatch") }
				return storeIntArray(contextID, term, fast, indexTerm, valueTerm)
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
	match context { case contextValue(contextID): return uninterpretedExprValue(contextID, smt.UninterpretedConstant(sort, id, name)) }
}

func DeclareUnary(domain nat, codomain nat, 0 c nat, context Context[c], name string, id int) UnaryFunc[c, domain, codomain] {
	match context { case contextValue(contextID): return unaryFuncValue(contextID, smt.DeclareUnaryFunction(domain, codomain, id, name)) }
}

func DeclareBinary(first nat, second nat, codomain nat, 0 c nat, context Context[c], name string, id int) BinaryFunc[c, first, second, codomain] {
	match context { case contextValue(contextID): return binaryFuncValue(contextID, smt.DeclareBinaryFunction(first, second, codomain, id, name)) }
}

func ApplyUninterpreted(0 c nat, 0 domain nat, 0 codomain nat, function UnaryFunc[c, domain, codomain], argument UninterpretedExpr[c, domain]) UninterpretedExpr[c, codomain] {
	match function {
	case unaryFuncValue(contextID, core):
		match argument {
		case uninterpretedExprValue(argumentContext, term):
			if contextID != argumentContext { panic("gosmt: erased uninterpreted application context mismatch") }
			return uninterpretedExprValue(contextID, smt.ApplyUnary(core, term))
		}
	}
}

func ApplyBinaryUninterpreted(0 c nat, 0 first nat, 0 second nat, 0 codomain nat, function BinaryFunc[c, first, second, codomain], left UninterpretedExpr[c, first], right UninterpretedExpr[c, second]) UninterpretedExpr[c, codomain] {
	match function {
	case binaryFuncValue(contextID, core):
		match left {
		case uninterpretedExprValue(leftContext, leftTerm):
			match right {
			case uninterpretedExprValue(rightContext, rightTerm):
				if contextID != leftContext || contextID != rightContext { panic("gosmt: erased binary application context mismatch") }
				return uninterpretedExprValue(contextID, smt.ApplyBinary(core, leftTerm, rightTerm))
			}
		}
	}
}

func EqUninterpreted(0 c nat, 0 sort nat, left UninterpretedExpr[c, sort], right UninterpretedExpr[c, sort]) BoolExpr[c] {
	match left {
	case uninterpretedExprValue(contextID, leftTerm):
		match right {
		case uninterpretedExprValue(rightContext, rightTerm):
			if contextID != rightContext { panic("gosmt: erased uninterpreted equality context mismatch") }
			return fastBooleanAtom(contextID, smt.Equal(leftTerm, rightTerm))
		}
	}
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

func Add(0 c nat, values ...IntExpr[c]) IntExpr[c] {
	context, terms := integerTerms(values)
	return intExprValue(context, smt.Add(terms))
}

func Sub(0 c nat, left IntExpr[c], right IntExpr[c]) IntExpr[c] {
	return subtractInteger(left, right)
}

func ScaleInt(0 c nat, coefficient smt.IntegerValue, value IntExpr[c]) IntExpr[c] {
	match value { case intExprValue(contextID, term): return intExprValue(contextID, smt.ScaleInteger(coefficient, term)) }
}

func ScaleInt64(0 c nat, coefficient int64, value IntExpr[c]) IntExpr[c] {
	return ScaleInt(smt.NewIntegerValue(coefficient), value)
}

func DivInt(0 c nat, value IntExpr[c], divisor smt.IntegerValue) IntExpr[c] {
	match value { case intExprValue(contextID, term): return intExprValue(contextID, smt.DivInteger(term, divisor)) }
}

func ModInt(0 c nat, value IntExpr[c], divisor smt.IntegerValue) IntExpr[c] {
	match value { case intExprValue(contextID, term): return intExprValue(contextID, smt.ModInteger(term, divisor)) }
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
		case intExprValue(expressionContext, term):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			return smt.IntValue(core, term)
		}
	}
}

func EvalIntExact(0 c nat, 0 a nat, model Model[c, a], expression IntExpr[c]) (smt.IntegerValue, bool) {
	match model {
	case modelValue(context, core):
		match expression {
		case intExprValue(expressionContext, term):
			if context != expressionContext { panic("gosmt: erased model/expression context mismatch") }
			return smt.IntegerModelValue(core, term)
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
