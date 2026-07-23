package gosmt

import (
	smt "goforge.dev/goplus/std/smt"
	"goforge.dev/goplus/std/vec"
	"strconv"
	"strings"
)

var resultViewKey byte

func naryDatatypeSelectorNames(values vec.Vec[string]) smt.NaryDatatypeSelectors {
	var result smt.NaryDatatypeSelectors
	for {
		switch current := values.(type) {
		case vec.Nil[string]:
			return result
		case vec.Cons[string]:
			result.Append(current.Head)
			values = current.Tail
		default:
			panic("gosmt: invalid erased n-ary datatype selector vector")
		}
	}
}

func naryDatatypeTerms(contextID int, values vec.Vec[DatatypeExpr]) smt.NaryDatatypeTerms {
	var result smt.NaryDatatypeTerms
	for {
		switch current := values.(type) {
		case vec.Nil[DatatypeExpr]:
			return result
		case vec.Cons[DatatypeExpr]:
			if current.Head.contextID != contextID {
				panic("gosmt: erased n-ary recursive datatype constructor context mismatch")
			}
			result.Append(current.Head.term)
			values = current.Tail
		default:
			panic("gosmt: invalid erased n-ary datatype argument vector")
		}
	}
}

func naryDatatypeFieldIndex(field vec.Fin) int {
	index := 0
	for {
		switch current := field.(type) {
		case vec.Zero:
			return index
		case vec.Succ:
			index++
			field = current.Prev
		default:
			panic("gosmt: invalid erased n-ary datatype field witness")
		}
	}
}

const (
	integerFastNone = iota
	integerFastBitVectorConversion
	integerFastStringLength
	integerFastStringIndexOfSymbols
)

type integerFast struct {
	kind             uint8
	width            int
	symbolID         int
	name             string
	signed           bool
	string           smt.CompactStringTerm
	eufValid         bool
	eufArity         uint8
	functionID       int
	argumentID       int
	secondArgumentID int
	thirdArgumentID  int
}

type integerFunctionFast struct {
	valid bool
	id    int
	name  string
}

type integerPredicateFast struct {
	valid bool
	id    int
	name  string
}

type integerBinaryFunctionFast struct {
	valid bool
	id    int
	name  string
}

type integerBinaryPredicateFast struct {
	valid bool
	id    int
	name  string
}

type integerTernaryFunctionFast struct {
	valid bool
	id    int
	name  string
}

type integerSequenceFast struct {
	compact  smt.CompactIntegerSequence
	symbolID int
	valid    bool
	symbol   bool
}

const (
	booleanFastNone = iota
	booleanFastLiteral
	booleanFastClause
	booleanFastRealConstraint
	booleanFastAtom
	booleanFastRealSymbolEquality
	booleanFastRealUnaryComparison
	booleanFastRealBinaryComparison
	booleanFastIntegerUnaryComparison
	booleanFastIntegerBinaryComparison
	booleanFastIntegerTernaryComparison
	booleanFastBitVectorRelation
	booleanFastBitVectorEUFRelation
	booleanFastIntegerDifference
	booleanFastIntegerSymbolEquality
	booleanFastBitVectorIntegerRelation
	booleanFastArrayEquality
	booleanFastArrayReadEquality
	booleanFastArrayStoreEquality
	booleanFastArrayConstantEquality
	booleanFastArrayReadValue
	booleanFastArrayStoreReadValue
	booleanFastBitVectorArrayStoreReadValue
	booleanFastBitVectorArrayEquality
	booleanFastIntegerLinearEquality
	booleanFastIntegerLinearDisequality
	booleanFastIntegerLinearChoice
	booleanFastIntegerDivModRelation
	booleanFastIntegerDivModSystem
	booleanFastUninterpretedEUFRelation
	booleanFastStringRelation
	booleanFastStringBooleanFormula
	booleanFastStringWordEquation
	booleanFastStringIndexedEquality
	booleanFastStringReplaceEquality
	booleanFastGroundIndexedStringFormula
	booleanFastStringIndexOfEquality
	booleanFastGroundStringEvaluationFormula
)

type booleanFast struct {
	kind                         uint8
	count                        uint8
	inline                       [4]int
	overflow                     []int
	real                         smt.LinearRealConstraint
	symbolEquality               smt.RealSymbolEquality
	unaryComparison              smt.RealUnaryComparison
	binaryComparison             smt.RealBinaryComparison
	integerUnaryComparison       smt.IntegerUnaryComparison
	integerBinaryComparison      smt.IntegerBinaryComparison
	integerTernaryComparison     smt.IntegerTernaryComparison
	bitVectorRelation            smt.BitVectorRelation
	bitVectorEUFRelation         smt.BitVectorEUFRelation
	integerDifference            smt.IntegerDifferenceConstraint
	integerSymbolLeft            int
	integerSymbolRight           int
	integerSymbolNegated         bool
	bitVectorIntegerRelation     smt.BitVectorIntegerRelation
	arrayEquality                smt.ArrayEqualityRelation
	arrayReadEquality            smt.ArrayReadRelation
	arrayStoreEquality           smt.ArrayStoreEqualityRelation
	arrayConstantEquality        smt.ArrayConstantEqualityRelation
	arrayReadValue               smt.ArrayReadValueRelation
	arrayStoreReadValue          smt.ArrayStoreReadValueRelation
	bitVectorArrayStoreReadValue smt.BitVectorArrayStoreReadValueRelation
	bitVectorArrayEquality       smt.BitVectorArrayEqualityRelation
	integerLinearEquality        smt.IntegerLinearEquality
	integerLinearChoice          smt.IntegerLinearChoice
	integerDivModRelation        smt.IntegerDivModRelation
	integerDivModSystem          smt.IntegerDivModSystem
	uninterpretedEUFRelation     smt.UninterpretedEUFRelation
	stringRelation               smt.CompactStringRelation
	stringBooleanFormula         smt.CompactStringBooleanFormula
	stringWordEquation           smt.CompactStringWordEquation
	stringIndexedEquality        smt.CompactStringIndexedEquality
	stringReplaceEquality        smt.CompactStringReplaceEquality
	groundIndexedStringFormula   *smt.CompactGroundIndexedStringFormula
	stringIndexOfEquality        smt.CompactStringIndexOfEquality
	groundStringEvaluation       *smt.CompactGroundStringEvaluationFormula
	negated                      bool
}

const (
	stringFastNone = iota
	stringFastLiteral
	stringFastSymbol
	stringFastSingleSymbolConcat
	stringFastPattern
	stringFastAt
	stringFastSubstring
	stringFastAtSymbol
	stringFastSubstringSymbols
	stringFastReplace
	stringFastReplaceAll
	stringFastReplaceSymbols
)

type stringFast struct {
	kind            uint8
	id              int
	name            string
	value           string
	suffix          string
	pattern         smt.CompactStringPattern
	offset          int64
	length          int64
	sourceID        int
	sourceName      string
	replacementID   int
	replacementName string
}

const (
	regexFastNone = iota
	regexFastLiteral
	regexFastEmpty
	regexFastFull
	regexFastAllChar
)

type regexFast struct {
	kind  uint8
	value string
}

func materializeRegex(core smt.Regex[smt.StringSort], fast regexFast) smt.Regex[smt.StringSort] {
	switch fast.kind {
	case regexFastLiteral:
		return smt.StringLiteralRegex(fast.value)
	case regexFastEmpty:
		return smt.EmptyRegex[smt.StringSort]()
	case regexFastFull:
		return smt.FullRegex[smt.StringSort]()
	case regexFastAllChar:
		return smt.AllCharRegex[smt.StringSort]()
	default:
		return core
	}
}

func compactString(value StringExpr) (smt.CompactStringTerm, bool) {
	switch value.fast.kind {
	case stringFastLiteral:
		return smt.CompactStringLiteralTerm(value.fast.value), true
	case stringFastSymbol:
		return smt.CompactStringSymbolTerm(value.fast.id, value.fast.name), true
	case stringFastSingleSymbolConcat:
		return smt.CompactStringSingleSymbolConcatTerm(
			value.fast.value, value.fast.id, value.fast.name, value.fast.suffix,
		), true
	default:
		return smt.CompactStringTerm{}, false
	}
}

func materializeString(value StringExpr) smt.Term[smt.StringSort] {
	if value.term != nil {
		return value.term
	}
	switch value.fast.kind {
	case stringFastLiteral:
		return smt.StringVal(value.fast.value)
	case stringFastSymbol:
		return smt.StringConst(value.fast.id, value.fast.name)
	case stringFastSingleSymbolConcat:
		return smt.StringConcat(
			smt.StringVal(value.fast.value),
			smt.StringConst(value.fast.id, value.fast.name),
			smt.StringVal(value.fast.suffix),
		)
	case stringFastPattern:
		pattern := value.fast.pattern
		terms := make([]smt.Term[smt.StringSort], 0, pattern.Count*2+1)
		for index := 0; index < pattern.Count; index++ {
			terms = append(terms,
				smt.StringVal(pattern.Delimiters[index]),
				smt.StringConst(pattern.SymbolIDs[index], pattern.SymbolNames[index]),
			)
		}
		terms = append(terms, smt.StringVal(pattern.Delimiters[pattern.Count]))
		return smt.StringConcat(terms...)
	case stringFastAt:
		return smt.StringAt(
			smt.StringConst(value.fast.id, value.fast.name),
			smt.Integer{Value: value.fast.offset},
		)
	case stringFastSubstring:
		return smt.StringSubstring(
			smt.StringConst(value.fast.id, value.fast.name),
			smt.Integer{Value: value.fast.offset},
			smt.Integer{Value: value.fast.length},
		)
	case stringFastAtSymbol:
		return smt.StringAt(
			smt.StringConst(value.fast.id, value.fast.name),
			smt.IntSymbol{ID: value.fast.sourceID, Name: value.fast.sourceName},
		)
	case stringFastSubstringSymbols:
		return smt.StringSubstring(
			smt.StringConst(value.fast.id, value.fast.name),
			smt.IntSymbol{ID: value.fast.sourceID, Name: value.fast.sourceName},
			smt.IntSymbol{ID: value.fast.replacementID, Name: value.fast.replacementName},
		)
	case stringFastReplace:
		return smt.StringReplace(
			smt.StringConst(value.fast.id, value.fast.name),
			smt.StringVal(value.fast.value),
			smt.StringVal(value.fast.suffix),
		)
	case stringFastReplaceAll:
		return smt.StringReplaceAll(
			smt.StringConst(value.fast.id, value.fast.name),
			smt.StringVal(value.fast.value),
			smt.StringVal(value.fast.suffix),
		)
	case stringFastReplaceSymbols:
		input := smt.StringConst(value.fast.id, value.fast.name)
		source := smt.StringConst(value.fast.sourceID, value.fast.sourceName)
		replacement := smt.StringConst(value.fast.replacementID, value.fast.replacementName)
		if value.fast.length != 0 {
			return smt.StringReplaceAll(input, source, replacement)
		}
		return smt.StringReplace(input, source, replacement)
	default:
		panic("gosmt: invalid erased string expression")
	}
}

func emptyIntegerSequenceFast() integerSequenceFast {
	return integerSequenceFast{
		compact: smt.EmptyCompactIntegerSequence(),
		valid:   true,
	}
}

func unitIntegerSequence(
	contextID int,
	term smt.Term[smt.IntSort],
	fast integerFast,
) IntSequenceExpr {
	materialized := materializeInteger(term, fast)
	if value, ok := smt.ExactIntegerConstant(materialized); ok {
		return intSequenceExprValue{
			contextID: contextID,
			fast: integerSequenceFast{
				compact: smt.UnitCompactIntegerSequence(value),
				valid:   true,
			},
		}
	}
	return intSequenceExprValue{
		contextID: contextID,
		term:      smt.SequenceUnit[smt.IntSort](materialized),
	}
}

func concatIntegerSequences(values []IntSequenceExpr) IntSequenceExpr {
	if len(values) == 0 {
		panic("gosmt: integer sequence concatenation requires at least one value")
	}
	contextID := values[0].contextID
	allCompact := true
	compact := smt.EmptyCompactIntegerSequence()
	for _, value := range values {
		if value.contextID != contextID {
			panic("gosmt: erased integer sequence context mismatch")
		}
		if !value.fast.valid {
			allCompact = false
			break
		}
		compact = smt.AppendCompactIntegerSequence(compact, value.fast.compact)
	}
	if allCompact {
		return intSequenceExprValue{
			contextID: contextID,
			fast:      integerSequenceFast{compact: compact, valid: true},
		}
	}
	terms := make([]smt.Term[smt.SequenceSort[smt.IntSort]], len(values))
	for index, value := range values {
		terms[index] = materializeIntegerSequence(value.term, value.fast)
	}
	return intSequenceExprValue{
		contextID: contextID,
		term:      smt.SequenceConcat[smt.IntSort](terms...),
	}
}

func materializeIntegerSequence(
	term smt.Term[smt.SequenceSort[smt.IntSort]],
	fast integerSequenceFast,
) smt.Term[smt.SequenceSort[smt.IntSort]] {
	if fast.valid {
		return fast.compact
	}
	return term
}

func symbolIntegerSequenceFast(id int) integerSequenceFast {
	return integerSequenceFast{symbolID: id, symbol: true}
}

func fastEvaluateIntegerSequence(
	model smt.Model,
	term smt.Term[smt.SequenceSort[smt.IntSort]],
	fast integerSequenceFast,
) (smt.IntegerSequenceValue, bool) {
	if fast.symbol {
		return smt.IntegerSequenceSymbolModelValue(model, fast.symbolID)
	}
	return smt.IntegerSequenceModelValue(
		model, materializeIntegerSequence(term, fast),
	)
}

func materializeCompactString(value smt.CompactStringTerm) smt.Term[smt.StringSort] {
	return smt.MaterializeCompactStringTerm(value)
}

func fastEvaluateString(model smt.Model, value stringExprValue) (string, bool) {
	if value.fast.kind == stringFastAtSymbol || value.fast.kind == stringFastSubstringSymbols {
		input, inputOK := smt.CompactStringModelValue(model, smt.CompactStringSymbolTerm(value.fast.id, value.fast.name))
		offset, offsetOK := smt.IntegerModelValue(model, smt.IntSymbol{ID: value.fast.sourceID, Name: value.fast.sourceName})
		if !inputOK || !offsetOK {
			return "", false
		}
		offsetValue, fits := offset.Int64()
		if !fits {
			return "", true
		}
		if value.fast.kind == stringFastAtSymbol {
			return smt.StringModelValue(model, smt.StringAt(smt.StringVal(input), smt.Integer{Value: offsetValue}))
		}
		length, lengthOK := smt.IntegerModelValue(model, smt.IntSymbol{ID: value.fast.replacementID, Name: value.fast.replacementName})
		if !lengthOK {
			return "", false
		}
		lengthValue, fits := length.Int64()
		if !fits {
			return "", true
		}
		return smt.StringModelValue(model, smt.StringSubstring(
			smt.StringVal(input), smt.Integer{Value: offsetValue}, smt.Integer{Value: lengthValue},
		))
	}
	if value.fast.kind == stringFastReplaceSymbols {
		input, inputOK := smt.CompactStringModelValue(model, smt.CompactStringSymbolTerm(value.fast.id, value.fast.name))
		source, sourceOK := smt.CompactStringModelValue(model, smt.CompactStringSymbolTerm(value.fast.sourceID, value.fast.sourceName))
		replacement, replacementOK := smt.CompactStringModelValue(model, smt.CompactStringSymbolTerm(value.fast.replacementID, value.fast.replacementName))
		if !inputOK || !sourceOK || !replacementOK {
			return "", false
		}
		if source == "" {
			return input, true
		}
		count := 1
		if value.fast.length != 0 {
			count = -1
		}
		return strings.Replace(input, source, replacement, count), true
	}
	if compact, ok := compactString(value); ok {
		return smt.CompactStringModelValue(model, compact)
	}
	return smt.StringModelValue(model, materializeString(value))
}

func fastEvaluateBoolean(model smt.Model, term smt.Term[smt.BoolSort], fast booleanFast) (bool, bool) {
	if fast.kind == booleanFastStringRelation {
		return smt.CompactStringRelationValue(model, fast.stringRelation)
	}
	if fast.kind == booleanFastStringBooleanFormula {
		return smt.CompactStringBooleanValue(model, fast.stringBooleanFormula)
	}
	if fast.kind == booleanFastStringWordEquation {
		return smt.CompactStringWordEquationValue(model, fast.stringWordEquation)
	}
	if fast.kind == booleanFastStringIndexedEquality {
		return smt.BoolValue(model, fast.stringIndexedEquality)
	}
	if fast.kind == booleanFastStringReplaceEquality {
		return smt.BoolValue(model, fast.stringReplaceEquality)
	}
	if fast.kind == booleanFastGroundIndexedStringFormula {
		return smt.BoolValue(model, fast.groundIndexedStringFormula)
	}
	if fast.kind == booleanFastStringIndexOfEquality {
		return smt.BoolValue(model, fast.stringIndexOfEquality)
	}
	if fast.kind == booleanFastGroundStringEvaluationFormula {
		return smt.BoolValue(model, fast.groundStringEvaluation)
	}
	return smt.BoolValue(model, materializeBoolean(term, fast))
}

func fastStringValue(context int, value string) StringExpr {
	return stringExprValue{contextID: context, fast: stringFast{kind: stringFastLiteral, value: value}}
}

func fastStringConst(context int, name string, id int) StringExpr {
	return stringExprValue{contextID: context, fast: stringFast{kind: stringFastSymbol, id: id, name: name}}
}

func fastConcatString(values []StringExpr) StringExpr {
	if len(values) == 0 {
		panic("gosmt: string concatenation requires at least one value")
	}
	context := values[0].contextID
	total, allLiterals := 0, true
	for _, value := range values {
		if value.contextID != context {
			panic("gosmt: erased string context mismatch")
		}
		allLiterals = allLiterals && value.fast.kind == stringFastLiteral
		total += len(value.fast.value)
	}
	if allLiterals {
		var result strings.Builder
		result.Grow(total)
		for _, value := range values {
			result.WriteString(value.fast.value)
		}
		return fastStringValue(context, result.String())
	}
	if pattern, ok := compactStringPattern(values); ok && pattern.Count > 1 {
		return stringExprValue{
			contextID: context,
			fast:      stringFast{kind: stringFastPattern, pattern: pattern},
		}
	}
	prefix, suffix := "", ""
	symbolID, symbolName := 0, ""
	foundSymbol, compact := false, true
	for _, value := range values {
		switch value.fast.kind {
		case stringFastLiteral:
			if foundSymbol {
				suffix += value.fast.value
			} else {
				prefix += value.fast.value
			}
		case stringFastSymbol:
			if foundSymbol {
				compact = false
				break
			}
			symbolID, symbolName, foundSymbol = value.fast.id, value.fast.name, true
		default:
			compact = false
		}
		if !compact {
			break
		}
	}
	if compact && foundSymbol {
		return stringExprValue{
			contextID: context,
			fast: stringFast{
				kind: stringFastSingleSymbolConcat, id: symbolID, name: symbolName,
				value: prefix, suffix: suffix,
			},
		}
	}
	terms := make([]smt.Term[smt.StringSort], len(values))
	for index, value := range values {
		terms[index] = materializeString(value)
	}
	return stringExprValue{contextID: context, term: smt.StringConcat(terms...)}
}

func compactStringPattern(values []StringExpr) (smt.CompactStringPattern, bool) {
	var pattern smt.CompactStringPattern
	literal := ""
	for _, value := range values {
		switch value.fast.kind {
		case stringFastLiteral:
			literal += value.fast.value
		case stringFastSymbol:
			if pattern.Count == len(pattern.SymbolIDs) {
				return smt.CompactStringPattern{}, false
			}
			pattern.Delimiters[pattern.Count] = literal
			pattern.SymbolIDs[pattern.Count] = value.fast.id
			pattern.SymbolNames[pattern.Count] = value.fast.name
			pattern.Count++
			literal = ""
		default:
			return smt.CompactStringPattern{}, false
		}
	}
	if pattern.Count == 0 {
		return smt.CompactStringPattern{}, false
	}
	pattern.Delimiters[pattern.Count] = literal
	return pattern, true
}

func fastStringRelation(kind uint8, left, right StringExpr) BoolExpr {
	if left.contextID != right.contextID {
		panic("gosmt: erased string context mismatch")
	}
	if kind == smt.CompactStringEqual {
		if replacement, ok := compactStringReplaceEquality(left, right); ok {
			return boolExprValue{
				contextID: left.contextID,
				fast: booleanFast{
					kind:                  booleanFastStringReplaceEquality,
					stringReplaceEquality: replacement,
				},
			}
		}
		if replacement, ok := compactStringReplaceEquality(right, left); ok {
			return boolExprValue{
				contextID: left.contextID,
				fast: booleanFast{
					kind:                  booleanFastStringReplaceEquality,
					stringReplaceEquality: replacement,
				},
			}
		}
		if indexed, ok := compactIndexedStringEquality(left, right); ok {
			return boolExprValue{
				contextID: left.contextID,
				fast: booleanFast{
					kind:                  booleanFastStringIndexedEquality,
					stringIndexedEquality: indexed,
				},
			}
		}
		if indexed, ok := compactIndexedStringEquality(right, left); ok {
			return boolExprValue{
				contextID: left.contextID,
				fast: booleanFast{
					kind:                  booleanFastStringIndexedEquality,
					stringIndexedEquality: indexed,
				},
			}
		}
		if left.fast.kind == stringFastPattern && right.fast.kind == stringFastLiteral {
			return fastStringWordEquation(left.contextID, left.fast.pattern, right.fast.value)
		}
		if right.fast.kind == stringFastPattern && left.fast.kind == stringFastLiteral {
			return fastStringWordEquation(left.contextID, right.fast.pattern, left.fast.value)
		}
		if left.fast.kind == stringFastSingleSymbolConcat && right.fast.kind == stringFastLiteral {
			return fastStringWordEquation(
				left.contextID,
				singleSymbolStringPattern(left.fast),
				right.fast.value,
			)
		}
		if right.fast.kind == stringFastSingleSymbolConcat && left.fast.kind == stringFastLiteral {
			return fastStringWordEquation(
				left.contextID,
				singleSymbolStringPattern(right.fast),
				left.fast.value,
			)
		}
	}
	leftCompact, leftOK := compactString(left)
	rightCompact, rightOK := compactString(right)
	if leftOK && rightOK {
		if leftCompact.Kind == 0 && rightCompact.Kind == 0 {
			result := false
			switch kind {
			case smt.CompactStringEqual:
				result = leftCompact.Value == rightCompact.Value
			case smt.CompactStringContains:
				result = strings.Contains(leftCompact.Value, rightCompact.Value)
			case smt.CompactStringPrefix:
				result = strings.HasPrefix(leftCompact.Value, rightCompact.Value)
			case smt.CompactStringSuffix:
				result = strings.HasSuffix(leftCompact.Value, rightCompact.Value)
			case smt.CompactStringLess:
				result = smt.CompareStringValues(leftCompact.Value, rightCompact.Value) < 0
			case smt.CompactStringLessEqual:
				result = smt.CompareStringValues(leftCompact.Value, rightCompact.Value) <= 0
			}
			return boolExprValue{contextID: left.contextID, term: smt.Bool{Value: result}}
		}
		relation := smt.CompactStringRelation{Kind: kind, Left: leftCompact, Right: rightCompact}
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastStringRelation, stringRelation: relation}}
	}
	leftTerm, rightTerm := materializeString(left), materializeString(right)
	var term smt.Term[smt.BoolSort]
	switch kind {
	case smt.CompactStringEqual:
		term = smt.Equal{Left: leftTerm, Right: rightTerm}
	case smt.CompactStringContains:
		term = smt.StringContains(leftTerm, rightTerm)
	case smt.CompactStringPrefix:
		term = smt.StringHasPrefix(leftTerm, rightTerm)
	case smt.CompactStringSuffix:
		term = smt.StringHasSuffix(leftTerm, rightTerm)
	case smt.CompactStringLess:
		term = smt.StringLess(leftTerm, rightTerm)
	case smt.CompactStringLessEqual:
		term = smt.StringLessEqual(leftTerm, rightTerm)
	}
	return fastBooleanAtom(left.contextID, term)
}

func compactStringReplaceEquality(derived, target StringExpr) (smt.CompactStringReplaceEquality, bool) {
	if derived.fast.kind == stringFastReplaceSymbols &&
		(target.fast.kind == stringFastLiteral || target.fast.kind == stringFastSymbol) {
		result := smt.CompactStringReplaceEquality{
			SymbolID: derived.fast.id, SymbolName: derived.fast.name,
			SourceID: derived.fast.sourceID, SourceName: derived.fast.sourceName, SourceSymbol: true,
			ReplacementID: derived.fast.replacementID, ReplacementName: derived.fast.replacementName, ReplacementSymbol: true,
			All: derived.fast.length != 0,
		}
		if target.fast.kind == stringFastSymbol {
			result.TargetID, result.TargetName, result.TargetSymbol = target.fast.id, target.fast.name, true
		} else {
			result.Target = target.fast.value
		}
		return result, true
	}
	if derived.fast.kind != stringFastReplace && derived.fast.kind != stringFastReplaceAll ||
		target.fast.kind != stringFastLiteral {
		return smt.CompactStringReplaceEquality{}, false
	}
	return smt.CompactStringReplaceEquality{
		SymbolID:    derived.fast.id,
		SymbolName:  derived.fast.name,
		Source:      derived.fast.value,
		Replacement: derived.fast.suffix,
		Target:      target.fast.value,
		All:         derived.fast.kind == stringFastReplaceAll,
	}, true
}

func compactIndexedStringEquality(derived, target StringExpr) (smt.CompactStringIndexedEquality, bool) {
	if target.fast.kind != stringFastLiteral {
		return smt.CompactStringIndexedEquality{}, false
	}
	switch derived.fast.kind {
	case stringFastAtSymbol:
		return smt.CompactStringIndexedEquality{
			Kind: smt.CompactStringAtEquality, SymbolID: derived.fast.id, SymbolName: derived.fast.name,
			OffsetID: derived.fast.sourceID, OffsetName: derived.fast.sourceName, OffsetSymbol: true,
			Target: target.fast.value,
		}, true
	case stringFastSubstringSymbols:
		return smt.CompactStringIndexedEquality{
			Kind: smt.CompactStringSubstringEquality, SymbolID: derived.fast.id, SymbolName: derived.fast.name,
			OffsetID: derived.fast.sourceID, OffsetName: derived.fast.sourceName, OffsetSymbol: true,
			LengthID: derived.fast.replacementID, LengthName: derived.fast.replacementName, LengthSymbol: true,
			Target: target.fast.value,
		}, true
	case stringFastAt:
		return smt.CompactStringIndexedEquality{
			Kind:       smt.CompactStringAtEquality,
			SymbolID:   derived.fast.id,
			SymbolName: derived.fast.name,
			Offset:     derived.fast.offset,
			Target:     target.fast.value,
		}, true
	case stringFastSubstring:
		return smt.CompactStringIndexedEquality{
			Kind:       smt.CompactStringSubstringEquality,
			SymbolID:   derived.fast.id,
			SymbolName: derived.fast.name,
			Offset:     derived.fast.offset,
			Length:     derived.fast.length,
			Target:     target.fast.value,
		}, true
	default:
		return smt.CompactStringIndexedEquality{}, false
	}
}

func singleSymbolStringPattern(value stringFast) smt.CompactStringPattern {
	return smt.CompactStringPattern{
		Count:       1,
		SymbolIDs:   [4]int{value.id},
		SymbolNames: [4]string{value.name},
		Delimiters:  [5]string{value.value, value.suffix},
	}
}

func fastStringWordEquation(context int, pattern smt.CompactStringPattern, target string) BoolExpr {
	return boolExprValue{
		contextID: context,
		fast: booleanFast{
			kind: booleanFastStringWordEquation,
			stringWordEquation: smt.CompactStringWordEquation{
				Pattern: pattern,
				Target:  target,
			},
		},
	}
}

func constantIntExpr(value IntExpr) (int64, bool) {
	if value.fast.kind != integerFastNone {
		return 0, false
	}
	exact, ok := smt.ExactIntegerConstant(value.term)
	if !ok {
		return 0, false
	}
	return exact.Int64()
}

func fastAtString(value StringExpr, index IntExpr) StringExpr {
	if value.contextID != index.contextID {
		panic("gosmt: erased string/index context mismatch")
	}
	if value.fast.kind == stringFastLiteral {
		if position, ok := constantIntExpr(index); ok {
			runes := []rune(value.fast.value)
			if position < 0 || position >= int64(len(runes)) {
				return fastStringValue(value.contextID, "")
			}
			return fastStringValue(value.contextID, string(runes[position]))
		}
	}
	if value.fast.kind == stringFastSymbol {
		if position, ok := constantIntExpr(index); ok {
			return stringExprValue{
				contextID: value.contextID,
				fast: stringFast{
					kind:   stringFastAt,
					id:     value.fast.id,
					name:   value.fast.name,
					offset: position,
				},
			}
		}
		if id, name, ok := directIntegerExprSymbol(index); ok {
			return stringExprValue{
				contextID: value.contextID,
				fast: stringFast{
					kind: stringFastAtSymbol, id: value.fast.id, name: value.fast.name,
					sourceID: id, sourceName: name,
				},
			}
		}
	}
	return stringExprValue{contextID: value.contextID, term: smt.StringAt(materializeString(value), materializeInteger(index.term, index.fast))}
}

func fastSubstring(value StringExpr, offset, length IntExpr) StringExpr {
	if value.contextID != offset.contextID || value.contextID != length.contextID {
		panic("gosmt: erased string/range context mismatch")
	}
	if value.fast.kind == stringFastLiteral {
		start, startOK := constantIntExpr(offset)
		count, countOK := constantIntExpr(length)
		if startOK && countOK {
			runes := []rune(value.fast.value)
			if start < 0 || start >= int64(len(runes)) || count <= 0 {
				return fastStringValue(value.contextID, "")
			}
			end := start + count
			if end < start || end > int64(len(runes)) {
				end = int64(len(runes))
			}
			return fastStringValue(value.contextID, string(runes[start:end]))
		}
	}
	if value.fast.kind == stringFastSymbol {
		start, startOK := constantIntExpr(offset)
		count, countOK := constantIntExpr(length)
		if startOK && countOK {
			return stringExprValue{
				contextID: value.contextID,
				fast: stringFast{
					kind:   stringFastSubstring,
					id:     value.fast.id,
					name:   value.fast.name,
					offset: start,
					length: count,
				},
			}
		}
		offsetID, offsetName, offsetSymbol := directIntegerExprSymbol(offset)
		lengthID, lengthName, lengthSymbol := directIntegerExprSymbol(length)
		if offsetSymbol && lengthSymbol {
			return stringExprValue{
				contextID: value.contextID,
				fast: stringFast{
					kind: stringFastSubstringSymbols, id: value.fast.id, name: value.fast.name,
					sourceID: offsetID, sourceName: offsetName,
					replacementID: lengthID, replacementName: lengthName,
				},
			}
		}
	}
	return stringExprValue{contextID: value.contextID, term: smt.StringSubstring(materializeString(value), materializeInteger(offset.term, offset.fast), materializeInteger(length.term, length.fast))}
}

func directIntegerExprSymbol(value IntExpr) (int, string, bool) {
	return smt.IntegerSymbol(materializeInteger(value.term, value.fast))
}

func fastIndexOfString(value, substring StringExpr, offset IntExpr) IntExpr {
	if value.contextID != substring.contextID || value.contextID != offset.contextID {
		panic("gosmt: erased string/index context mismatch")
	}
	if value.fast.kind == stringFastLiteral && substring.fast.kind == stringFastLiteral {
		if start, ok := constantIntExpr(offset); ok {
			return intExprValue{contextID: value.contextID, term: smt.Integer{Value: indexOfRunes(value.fast.value, substring.fast.value, start)}}
		}
	}
	if value.fast.kind == stringFastSymbol && substring.fast.kind == stringFastSymbol {
		offsetValue, offsetOK := constantIntExpr(offset)
		offsetID, _, offsetSymbol := directIntegerExprSymbol(offset)
		if offsetOK || offsetSymbol {
			storedOffset := int(offsetValue)
			if offsetSymbol {
				storedOffset = offsetID
			}
			return intExprValue{
				contextID: value.contextID,
				fast: integerFast{
					kind:  integerFastStringIndexOfSymbols,
					width: storedOffset, symbolID: value.fast.id, name: value.fast.name,
					string: smt.CompactStringSymbolTerm(substring.fast.id, substring.fast.name),
					signed: offsetSymbol,
				},
			}
		}
	}
	return intExprValue{contextID: value.contextID, term: smt.StringIndexOf(materializeString(value), materializeString(substring), materializeInteger(offset.term, offset.fast))}
}

func fastReplaceString(value, source, replacement StringExpr) StringExpr {
	if value.contextID != source.contextID || value.contextID != replacement.contextID {
		panic("gosmt: erased string replacement context mismatch")
	}
	if value.fast.kind == stringFastLiteral && source.fast.kind == stringFastLiteral && replacement.fast.kind == stringFastLiteral {
		return fastStringValue(value.contextID, strings.Replace(value.fast.value, source.fast.value, replacement.fast.value, 1))
	}
	if value.fast.kind == stringFastSymbol &&
		source.fast.kind == stringFastLiteral &&
		replacement.fast.kind == stringFastLiteral {
		return stringExprValue{
			contextID: value.contextID,
			fast: stringFast{
				kind:   stringFastReplace,
				id:     value.fast.id,
				name:   value.fast.name,
				value:  source.fast.value,
				suffix: replacement.fast.value,
			},
		}
	}
	if value.fast.kind == stringFastSymbol &&
		source.fast.kind == stringFastSymbol &&
		replacement.fast.kind == stringFastSymbol {
		return stringExprValue{
			contextID: value.contextID,
			fast: stringFast{
				kind:            stringFastReplaceSymbols,
				id:              value.fast.id,
				name:            value.fast.name,
				sourceID:        source.fast.id,
				sourceName:      source.fast.name,
				replacementID:   replacement.fast.id,
				replacementName: replacement.fast.name,
			},
		}
	}
	return stringExprValue{contextID: value.contextID, term: smt.StringReplace(materializeString(value), materializeString(source), materializeString(replacement))}
}

func fastReplaceAllString(value, source, replacement StringExpr) StringExpr {
	if value.contextID != source.contextID || value.contextID != replacement.contextID {
		panic("gosmt: erased string replacement context mismatch")
	}
	if value.fast.kind == stringFastLiteral && source.fast.kind == stringFastLiteral && replacement.fast.kind == stringFastLiteral {
		if source.fast.value == "" {
			return value
		}
		return fastStringValue(value.contextID, strings.ReplaceAll(value.fast.value, source.fast.value, replacement.fast.value))
	}
	if value.fast.kind == stringFastSymbol &&
		source.fast.kind == stringFastLiteral &&
		replacement.fast.kind == stringFastLiteral {
		return stringExprValue{
			contextID: value.contextID,
			fast: stringFast{
				kind:   stringFastReplaceAll,
				id:     value.fast.id,
				name:   value.fast.name,
				value:  source.fast.value,
				suffix: replacement.fast.value,
			},
		}
	}
	if value.fast.kind == stringFastSymbol &&
		source.fast.kind == stringFastSymbol &&
		replacement.fast.kind == stringFastSymbol {
		return stringExprValue{
			contextID: value.contextID,
			fast: stringFast{
				kind:          stringFastReplaceSymbols,
				id:            value.fast.id,
				name:          value.fast.name,
				sourceID:      source.fast.id,
				sourceName:    source.fast.name,
				replacementID: replacement.fast.id, replacementName: replacement.fast.name,
				length: 1,
			},
		}
	}
	return stringExprValue{contextID: value.contextID, term: smt.StringReplaceAll(materializeString(value), materializeString(source), materializeString(replacement))}
}

func fastStringToInt(value StringExpr) IntExpr {
	if value.fast.kind == stringFastLiteral {
		text := value.fast.value
		valid := text != ""
		for index := 0; index < len(text); index++ {
			valid = valid && text[index] >= '0' && text[index] <= '9'
		}
		if valid {
			if small, err := strconv.ParseInt(text, 10, 64); err == nil {
				return intExprValue{contextID: value.contextID, term: smt.Integer{Value: small}}
			}
			if integer, err := smt.ParseIntegerValue(text); err == nil {
				return intExprValue{contextID: value.contextID, term: smt.IntegerTerm(integer)}
			}
		}
		return intExprValue{contextID: value.contextID, term: smt.Integer{Value: -1}}
	}
	return intExprValue{contextID: value.contextID, term: smt.StringToInt(materializeString(value))}
}

func fastIntToString(value IntExpr) StringExpr {
	if value.fast.kind == integerFastNone {
		if integer, ok := smt.ExactIntegerConstant(value.term); ok {
			if smt.CompareIntegerValue(integer, smt.NewIntegerValue(0)) < 0 {
				return fastStringValue(value.contextID, "")
			}
			return fastStringValue(value.contextID, integer.String())
		}
	}
	return stringExprValue{contextID: value.contextID, term: smt.IntToString(materializeInteger(value.term, value.fast))}
}

func fastStringToCode(value StringExpr) IntExpr {
	if value.fast.kind == stringFastLiteral {
		codes := smt.DecodeStringCodePoints(value.fast.value)
		code := int64(-1)
		if len(codes) == 1 {
			code = int64(codes[0])
		}
		return intExprValue{contextID: value.contextID, term: smt.Integer{Value: code}}
	}
	return intExprValue{contextID: value.contextID, term: smt.StringToCode(materializeString(value))}
}

func fastCodeToString(value IntExpr) StringExpr {
	if value.fast.kind == integerFastNone {
		if integer, ok := smt.ExactIntegerConstant(value.term); ok {
			if code, fits := integer.Int64(); fits {
				if encoded, valid := smt.EncodeStringCodePoint(code); valid {
					return fastStringValue(value.contextID, encoded)
				}
			}
			return fastStringValue(value.contextID, "")
		}
	}
	return stringExprValue{contextID: value.contextID, term: smt.StringFromCode(materializeInteger(value.term, value.fast))}
}

func fastStringIsDigit(value StringExpr) BoolExpr {
	if value.fast.kind == stringFastLiteral {
		text := value.fast.value
		return boolExprValue{contextID: value.contextID, term: smt.Bool{Value: len(text) == 1 && text[0] >= '0' && text[0] <= '9'}}
	}
	return fastBooleanAtom(value.contextID, smt.StringIsDigit(materializeString(value)))
}

func indexOfRunes(value, substring string, offset int64) int64 {
	text, part := []rune(value), []rune(substring)
	if offset < 0 || offset > int64(len(text)) {
		return -1
	}
	if len(part) == 0 {
		return offset
	}
	for index := int(offset); index+len(part) <= len(text); index++ {
		matches := true
		for partIndex := range part {
			if text[index+partIndex] != part[partIndex] {
				matches = false
				break
			}
		}
		if matches {
			return int64(index)
		}
	}
	return -1
}

const (
	uninterpretedFastNone = iota
	uninterpretedFastSymbol
	uninterpretedFastUnaryApplication
	uninterpretedFastBinaryApplication
)

type uninterpretedFast struct {
	kind         uint8
	sortID       int
	symbolID     int
	functionID   int
	firstSortID  int
	secondSortID int
	firstID      int
	secondID     int
	symbolName   string
	functionName string
	secondName   string
}

type uninterpretedUnaryFunctionFast struct {
	valid    bool
	domainID int
	rangeID  int
	id       int
	name     string
}

type uninterpretedBinaryFunctionFast struct {
	valid    bool
	firstID  int
	secondID int
	rangeID  int
	id       int
	name     string
}

func fastUninterpretedSymbol(context, sort, id int, name string) UninterpretedExpr {
	return uninterpretedExprValue{contextID: context, fast: uninterpretedFast{kind: uninterpretedFastSymbol, sortID: sort, symbolID: id, symbolName: name}}
}

func fastUninterpretedUnaryFunction(context, domain, codomain, id int, name string) UnaryFunc {
	return unaryFuncValue{contextID: context, fast: uninterpretedUnaryFunctionFast{valid: true, domainID: domain, rangeID: codomain, id: id, name: name}}
}

func fastUninterpretedBinaryFunction(context, first, second, codomain, id int, name string) BinaryFunc {
	return binaryFuncValue{contextID: context, fast: uninterpretedBinaryFunctionFast{valid: true, firstID: first, secondID: second, rangeID: codomain, id: id, name: name}}
}

func fastApplyUninterpreted(function UnaryFunc, argument UninterpretedExpr) UninterpretedExpr {
	if function.contextID != argument.contextID {
		panic("gosmt: erased uninterpreted application context mismatch")
	}
	if function.fast.valid {
		if argument.fast.kind == uninterpretedFastSymbol {
			return uninterpretedExprValue{contextID: function.contextID, fast: uninterpretedFast{
				kind: uninterpretedFastUnaryApplication, sortID: function.fast.rangeID, functionID: function.fast.id,
				firstSortID: function.fast.domainID, firstID: argument.fast.symbolID,
				functionName: function.fast.name, symbolName: argument.fast.symbolName,
			}}
		}
	}
	core := function.function
	if core == nil {
		core = smt.DeclareUnaryFunction(function.fast.domainID, function.fast.rangeID, function.fast.id, function.fast.name)
	}
	return uninterpretedExprValue{contextID: function.contextID, term: smt.ApplyUnary(core, materializeUninterpreted(argument))}
}

func fastApplyBinaryUninterpreted(function BinaryFunc, left, right UninterpretedExpr) UninterpretedExpr {
	if function.contextID != left.contextID || function.contextID != right.contextID {
		panic("gosmt: erased binary application context mismatch")
	}
	if function.fast.valid && left.fast.kind == uninterpretedFastSymbol && right.fast.kind == uninterpretedFastSymbol {
		return uninterpretedExprValue{contextID: function.contextID, fast: uninterpretedFast{
			kind: uninterpretedFastBinaryApplication, sortID: function.fast.rangeID, functionID: function.fast.id,
			firstSortID: function.fast.firstID, secondSortID: function.fast.secondID,
			firstID: left.fast.symbolID, secondID: right.fast.symbolID,
			functionName: function.fast.name, symbolName: left.fast.symbolName, secondName: right.fast.symbolName,
		}}
	}
	core := function.function
	if core == nil {
		core = smt.DeclareBinaryFunction(function.fast.firstID, function.fast.secondID, function.fast.rangeID, function.fast.id, function.fast.name)
	}
	return uninterpretedExprValue{contextID: function.contextID, term: smt.ApplyBinary(core, materializeUninterpreted(left), materializeUninterpreted(right))}
}

func fastEqUninterpreted(left, right UninterpretedExpr) BoolExpr {
	if left.contextID != right.contextID {
		panic("gosmt: erased uninterpreted equality context mismatch")
	}
	leftCompact, leftOK := compactUninterpretedTerm(left.fast)
	rightCompact, rightOK := compactUninterpretedTerm(right.fast)
	if leftOK && rightOK {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastUninterpretedEUFRelation, uninterpretedEUFRelation: smt.UninterpretedEUFRelation{Left: leftCompact, Right: rightCompact}}}
	}
	return fastBooleanAtom(left.contextID, smt.Equal{Left: materializeUninterpreted(left), Right: materializeUninterpreted(right)})
}

func compactUninterpretedTerm(value uninterpretedFast) (smt.UninterpretedEUFTerm, bool) {
	switch value.kind {
	case uninterpretedFastSymbol:
		return smt.UninterpretedEUFTerm{Kind: 1, SortID: value.sortID, SymbolID: value.symbolID}, true
	case uninterpretedFastUnaryApplication:
		return smt.UninterpretedEUFTerm{Kind: 2, SortID: value.sortID, FunctionID: value.functionID, FirstSortID: value.firstSortID, FirstID: value.firstID}, true
	case uninterpretedFastBinaryApplication:
		return smt.UninterpretedEUFTerm{Kind: 3, SortID: value.sortID, FunctionID: value.functionID, FirstSortID: value.firstSortID, SecondSortID: value.secondSortID, FirstID: value.firstID, SecondID: value.secondID}, true
	default:
		return smt.UninterpretedEUFTerm{}, false
	}
}

func materializeUninterpreted(value UninterpretedExpr) smt.Term[smt.UninterpretedSort] {
	if value.term != nil {
		return value.term
	}
	switch value.fast.kind {
	case uninterpretedFastSymbol:
		return smt.UninterpretedConstant(value.fast.sortID, value.fast.symbolID, value.fast.symbolName)
	case uninterpretedFastUnaryApplication:
		function := smt.DeclareUnaryFunction(value.fast.firstSortID, value.fast.sortID, value.fast.functionID, value.fast.functionName)
		argument := smt.UninterpretedConstant(value.fast.firstSortID, value.fast.firstID, value.fast.symbolName)
		return smt.ApplyUnary(function, argument)
	case uninterpretedFastBinaryApplication:
		function := smt.DeclareBinaryFunction(value.fast.firstSortID, value.fast.secondSortID, value.fast.sortID, value.fast.functionID, value.fast.functionName)
		first := smt.UninterpretedConstant(value.fast.firstSortID, value.fast.firstID, value.fast.symbolName)
		second := smt.UninterpretedConstant(value.fast.secondSortID, value.fast.secondID, value.fast.secondName)
		return smt.ApplyBinary(function, first, second)
	}
	panic("gosmt: invalid erased uninterpreted expression")
}

const (
	bitVectorFastNone = iota
	bitVectorFastValue
	bitVectorFastSymbol
	bitVectorFastMaskedSymbol
	bitVectorFastAppliedSymbol
	bitVectorFastUnaryApplication
	bitVectorFastArrayStoreRead
)

type bitVectorFast struct {
	kind        uint8
	width       int
	id          int
	name        string
	value       smt.BitVectorValue
	mask        smt.BitVectorValue
	operation   uint8
	operand     smt.BitVectorValue
	sourceWidth int
	parameterA  int
	parameterB  int
	functionID  int
	firstID     int
	firstName   string
	firstWidth  int
	function    smt.SortedUnaryFunction[smt.BitVecSort, smt.BitVecSort]
}

const (
	bitVecArrayFastNone = iota
	bitVecArrayFastSymbol
	bitVecArrayFastStore
	bitVecArrayFastStore2
)

type bitVecArrayFast struct {
	kind          uint8
	indexWidth    uint8
	elementWidth  uint8
	symbolID      int
	symbolName    string
	index         uint64
	value         uint64
	secondIndex   uint64
	secondValue   uint64
	indexSymbolID int
	symbolicIndex bool
}

func fastBitVectorArraySymbol(context, indexWidth, elementWidth, id int, name string) BitVecArrayExpr {
	if indexWidth <= 64 && elementWidth <= 64 {
		return bitVecArrayExprValue{contextID: context, fast: bitVecArrayFast{kind: bitVecArrayFastSymbol, indexWidth: uint8(indexWidth), elementWidth: uint8(elementWidth), symbolID: id, symbolName: name}}
	}
	return bitVecArrayExprValue{contextID: context, term: smt.BitVectorArrayConst(indexWidth, elementWidth, id, name)}
}

func fastBitVectorUint64(value bitVectorFast) (uint64, bool) {
	if value.kind != bitVectorFastValue {
		return 0, false
	}
	return value.value.Uint64()
}

func storeFastBitVectorArray(array bitVecArrayFast, index, value bitVectorFast) (bitVecArrayFast, bool) {
	indexValue, indexOK := fastBitVectorUint64(index)
	storedValue, valueOK := fastBitVectorUint64(value)
	if (array.kind != bitVecArrayFastSymbol && array.kind != bitVecArrayFastStore) || !valueOK || (!indexOK && index.kind != bitVectorFastSymbol) {
		return bitVecArrayFast{}, false
	}
	if array.kind == bitVecArrayFastStore {
		if array.symbolicIndex || !indexOK {
			return bitVecArrayFast{}, false
		}
		if array.index == indexValue {
			array.value = storedValue
			return array, true
		}
		array.kind, array.secondIndex, array.secondValue = bitVecArrayFastStore2, indexValue, storedValue
		return array, true
	}
	array.kind, array.index, array.value = bitVecArrayFastStore, indexValue, storedValue
	if !indexOK {
		array.indexSymbolID, array.symbolicIndex = index.id, true
	}
	return array, true
}

func selectFastBitVectorArray(array bitVecArrayFast, index bitVectorFast) (uint64, int, bool) {
	indexValue, ok := fastBitVectorUint64(index)
	if !ok || array.kind != bitVecArrayFastStore || array.index != indexValue {
		return 0, 0, false
	}
	return array.value, int(array.elementWidth), true
}

func selectSymbolicBitVectorArray(context int, array bitVecArrayFast, index bitVectorFast) (BitVecExpr, bool) {
	if array.kind != bitVecArrayFastStore || !array.symbolicIndex || index.kind != bitVectorFastSymbol {
		return BitVecExpr{}, false
	}
	return bitVecExprValue{contextID: context, fast: bitVectorFast{
		kind: bitVectorFastArrayStoreRead, width: int(array.elementWidth), id: array.symbolID,
		firstID: array.indexSymbolID, firstWidth: int(array.indexWidth), functionID: index.id, operand: smt.NewBitVectorUint64(int(array.elementWidth), array.value),
	}}, true
}

func materializeBitVectorArray(term smt.Term[smt.ArraySort[smt.BitVecSort, smt.BitVecSort]], fast bitVecArrayFast) smt.Term[smt.ArraySort[smt.BitVecSort, smt.BitVecSort]] {
	if fast.kind == bitVecArrayFastNone {
		return term
	}
	base := smt.BitVectorArrayConst(int(fast.indexWidth), int(fast.elementWidth), fast.symbolID, fast.symbolName)
	if fast.kind == bitVecArrayFastStore || fast.kind == bitVecArrayFastStore2 {
		var index smt.Term[smt.BitVecSort] = smt.BitVecVal(int(fast.indexWidth), fast.index)
		if fast.symbolicIndex {
			index = smt.BitVecConst(int(fast.indexWidth), fast.indexSymbolID, "")
		}
		base = smt.Store(base, index, smt.BitVecVal(int(fast.elementWidth), fast.value))
		if fast.kind == bitVecArrayFastStore2 {
			base = smt.Store(base, smt.BitVecVal(int(fast.indexWidth), fast.secondIndex), smt.BitVecVal(int(fast.elementWidth), fast.secondValue))
		}
		return base
	}
	return base
}

func fastEqBitVectorArray(context int, left, right bitVecArrayFast) (BoolExpr, bool) {
	if left.kind == bitVecArrayFastSymbol && right.kind == bitVecArrayFastSymbol && left.indexWidth == right.indexWidth && left.elementWidth == right.elementWidth {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorArrayEquality, bitVectorArrayEquality: smt.BitVectorArrayEqualityRelation{
			LeftID: left.symbolID, RightID: right.symbolID, IndexWidth: int(left.indexWidth), ElementWidth: int(left.elementWidth),
		}}}, true
	}
	if left.kind == bitVecArrayFastNone || right.kind == bitVecArrayFastNone || left.symbolID != right.symbolID || left.indexWidth != right.indexWidth || left.elementWidth != right.elementWidth || left.symbolicIndex || right.symbolicIndex {
		return BoolExpr{}, false
	}
	count := func(value bitVecArrayFast) int {
		if value.kind == bitVecArrayFastStore2 {
			return 2
		}
		if value.kind == bitVecArrayFastStore {
			return 1
		}
		return 0
	}
	leftCount, rightCount := count(left), count(right)
	if leftCount != rightCount {
		return BoolExpr{}, false
	}
	equal := true
	if leftCount >= 1 {
		firstMatches := left.index == right.index && left.value == right.value
		if leftCount == 2 {
			firstMatches = firstMatches || left.index == right.secondIndex && left.value == right.secondValue
		}
		equal = equal && firstMatches
	}
	if leftCount == 2 {
		secondMatches := left.secondIndex == right.index && left.secondValue == right.value || left.secondIndex == right.secondIndex && left.secondValue == right.secondValue
		equal = equal && secondMatches
	}
	return boolExprValue{contextID: context, term: smt.Bool{Value: equal}}, true
}

const (
	arrayFastNone = iota
	arrayFastIntSymbol
	arrayFastIntStore
	arrayFastIntStore2
	arrayFastIntConstant
)

type arrayFast struct {
	kind          uint8
	symbolID      int
	symbolName    string
	index         smt.IntegerValue
	value         smt.IntegerValue
	secondIndex   smt.IntegerValue
	secondValue   smt.IntegerValue
	indexSymbolID int
	symbolicIndex bool
}

func fastIntArraySymbol(context, id int, name string) ArrayExpr[smt.IntSort, smt.IntSort] {
	return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: arrayFast{kind: arrayFastIntSymbol, symbolID: id, symbolName: name}}
}

func fastConstIntArray(context int, term smt.Term[smt.IntSort]) ArrayExpr[smt.IntSort, smt.IntSort] {
	if value, ok := smt.ExactIntegerConstant(term); ok {
		return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: arrayFast{kind: arrayFastIntConstant, value: value}}
	}
	return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, term: smt.ConstArray[smt.IntSort, smt.IntSort](term)}
}

func materializeArray[I any, E any](term smt.Term[smt.ArraySort[I, E]], fast arrayFast) smt.Term[smt.ArraySort[I, E]] {
	if fast.kind == arrayFastNone {
		return term
	}
	base := smt.ArrayConst[smt.IntSort, smt.IntSort](fast.symbolID, fast.symbolName)
	if fast.kind == arrayFastIntConstant {
		base = smt.ConstArray[smt.IntSort, smt.IntSort](smt.IntegerTerm(fast.value))
	} else if fast.kind == arrayFastIntStore {
		var index smt.Term[smt.IntSort] = smt.IntegerTerm(fast.index)
		if fast.symbolicIndex {
			index = smt.IntSymbol{ID: fast.indexSymbolID}
		}
		base = smt.Store(base, index, smt.IntegerTerm(fast.value))
	} else if fast.kind == arrayFastIntStore2 {
		base = smt.Store(base, smt.IntegerTerm(fast.index), smt.IntegerTerm(fast.value))
		base = smt.Store(base, smt.IntegerTerm(fast.secondIndex), smt.IntegerTerm(fast.secondValue))
	}
	return any(base).(smt.Term[smt.ArraySort[I, E]])
}

func storeIntArray(context int, term smt.Term[smt.ArraySort[smt.IntSort, smt.IntSort]], fast arrayFast, indexTerm, valueTerm smt.Term[smt.IntSort]) ArrayExpr[smt.IntSort, smt.IntSort] {
	index, indexOK := smt.ExactIntegerConstant(indexTerm)
	value, valueOK := smt.ExactIntegerConstant(valueTerm)
	if indexOK && valueOK && (fast.kind == arrayFastIntSymbol || fast.kind == arrayFastIntStore && !fast.symbolicIndex && smt.CompareIntegerValue(index, fast.index) == 0) {
		return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: arrayFast{kind: arrayFastIntStore, symbolID: fast.symbolID, symbolName: fast.symbolName, index: index, value: value}}
	}
	if indexOK && valueOK && fast.kind == arrayFastIntStore && !fast.symbolicIndex {
		return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: arrayFast{kind: arrayFastIntStore2, symbolID: fast.symbolID, symbolName: fast.symbolName, index: fast.index, value: fast.value, secondIndex: index, secondValue: value}}
	}
	if indexOK && valueOK && fast.kind == arrayFastIntStore2 {
		if smt.CompareIntegerValue(index, fast.secondIndex) == 0 {
			fast.secondValue = value
			return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: fast}
		}
		if smt.CompareIntegerValue(index, fast.index) == 0 {
			return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: arrayFast{kind: arrayFastIntStore2, symbolID: fast.symbolID, symbolName: fast.symbolName, index: fast.secondIndex, value: fast.secondValue, secondIndex: index, secondValue: value}}
		}
	}
	if symbolID, ok := smt.IntegerVariableID(indexTerm); ok && valueOK && fast.kind == arrayFastIntSymbol {
		return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, fast: arrayFast{kind: arrayFastIntStore, symbolID: fast.symbolID, symbolName: fast.symbolName, indexSymbolID: symbolID, symbolicIndex: true, value: value}}
	}
	return arrayExprValue[smt.IntSort, smt.IntSort]{contextID: context, term: smt.Store(materializeArray(term, fast), indexTerm, valueTerm)}
}

func selectIntArray(context int, term smt.Term[smt.ArraySort[smt.IntSort, smt.IntSort]], fast arrayFast, indexTerm smt.Term[smt.IntSort]) IntExpr {
	if index, ok := smt.ExactIntegerConstant(indexTerm); ok {
		if fast.kind == arrayFastIntConstant {
			return intExprValue{contextID: context, term: smt.IntegerTerm(fast.value)}
		}
		if fast.kind == arrayFastIntStore2 {
			if smt.CompareIntegerValue(index, fast.secondIndex) == 0 {
				return intExprValue{contextID: context, term: smt.IntegerTerm(fast.secondValue)}
			}
			if smt.CompareIntegerValue(index, fast.index) == 0 {
				return intExprValue{contextID: context, term: smt.IntegerTerm(fast.value)}
			}
		}
		if fast.kind == arrayFastIntStore && smt.CompareIntegerValue(index, fast.index) == 0 {
			return intExprValue{contextID: context, term: smt.IntegerTerm(fast.value)}
		}
		if fast.kind == arrayFastIntSymbol {
			return intExprValue{contextID: context, term: smt.IntegerArrayRead(fast.symbolID, index)}
		}
	}
	if symbolID, ok := smt.IntegerVariableID(indexTerm); ok && fast.kind == arrayFastIntStore && fast.symbolicIndex {
		return intExprValue{contextID: context, term: smt.SymbolicIntegerArrayStoreRead(fast.symbolID, fast.indexSymbolID, symbolID, fast.value)}
	}
	return intExprValue{contextID: context, term: smt.Select(materializeArray(term, fast), indexTerm)}
}

func fastEqArray[I any, E any](context int, leftTerm smt.Term[smt.ArraySort[I, E]], leftFast arrayFast, rightTerm smt.Term[smt.ArraySort[I, E]], rightFast arrayFast) BoolExpr {
	if leftFast.kind == arrayFastIntSymbol && rightFast.kind == arrayFastIntSymbol {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastArrayEquality, arrayEquality: smt.ArrayEqualityRelation{LeftID: leftFast.symbolID, RightID: rightFast.symbolID}}}
	}
	if leftFast.kind == arrayFastIntSymbol && rightFast.kind == arrayFastIntConstant {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastArrayConstantEquality, arrayConstantEquality: smt.ArrayConstantEqualityRelation{ArrayID: leftFast.symbolID, Default: rightFast.value}}}
	}
	if rightFast.kind == arrayFastIntSymbol && leftFast.kind == arrayFastIntConstant {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastArrayConstantEquality, arrayConstantEquality: smt.ArrayConstantEqualityRelation{ArrayID: rightFast.symbolID, Default: leftFast.value}}}
	}
	if equal, known := exactArrayFastEqual(leftFast, rightFast); known {
		return boolExprValue{contextID: context, term: smt.Bool{Value: equal}}
	}
	if leftFast.kind == arrayFastIntStore && rightFast.kind == arrayFastIntStore && !leftFast.symbolicIndex && !rightFast.symbolicIndex {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastArrayStoreEquality, arrayStoreEquality: smt.ArrayStoreEqualityRelation{
			LeftID: leftFast.symbolID, RightID: rightFast.symbolID, LeftIndex: leftFast.index, RightIndex: rightFast.index, LeftValue: leftFast.value, RightValue: rightFast.value,
		}}}
	}
	return fastBooleanAtom(context, smt.Equal{Left: materializeArray(leftTerm, leftFast), Right: materializeArray(rightTerm, rightFast)})
}

func exactArrayFastEqual(left, right arrayFast) (bool, bool) {
	if left.symbolID != right.symbolID || left.kind == arrayFastNone || right.kind == arrayFastNone || left.symbolicIndex || right.symbolicIndex {
		return false, false
	}
	var indices [4]smt.IntegerValue
	count := 0
	add := func(value smt.IntegerValue) {
		for position := 0; position < count; position++ {
			if smt.CompareIntegerValue(indices[position], value) == 0 {
				return
			}
		}
		indices[count] = value
		count++
	}
	if left.kind == arrayFastIntStore || left.kind == arrayFastIntStore2 {
		add(left.index)
	}
	if left.kind == arrayFastIntStore2 {
		add(left.secondIndex)
	}
	if right.kind == arrayFastIntStore || right.kind == arrayFastIntStore2 {
		add(right.index)
	}
	if right.kind == arrayFastIntStore2 {
		add(right.secondIndex)
	}
	for _, index := range indices[:count] {
		leftValue, leftSet := exactArrayFastRead(left, index)
		rightValue, rightSet := exactArrayFastRead(right, index)
		if !leftSet || !rightSet {
			return false, false
		}
		if smt.CompareIntegerValue(leftValue, rightValue) != 0 {
			return false, true
		}
	}
	return true, true
}

func exactArrayFastRead(array arrayFast, index smt.IntegerValue) (smt.IntegerValue, bool) {
	if array.kind == arrayFastIntStore2 && smt.CompareIntegerValue(array.secondIndex, index) == 0 {
		return array.secondValue, true
	}
	if (array.kind == arrayFastIntStore || array.kind == arrayFastIntStore2) && smt.CompareIntegerValue(array.index, index) == 0 {
		return array.value, true
	}
	return smt.IntegerValue{}, false
}

func fastBitVectorValue(context, width int, value uint64) BitVecExpr {
	return bitVecExprValue{contextID: context, fast: bitVectorFast{kind: bitVectorFastValue, width: width, value: smt.NewBitVectorUint64(width, value)}}
}

func fastBitVectorSymbol(context, width, id int, name string) BitVecExpr {
	return bitVecExprValue{contextID: context, fast: bitVectorFast{kind: bitVectorFastSymbol, width: width, id: id, name: name}}
}

func fastNotBitVector(value BitVecExpr) BitVecExpr {
	return bitVecExprValue{contextID: value.contextID, term: smt.BitVecNot(materializeBitVector(value.term, value.fast))}
}

func fastAndBitVector(left, right BitVecExpr) BitVecExpr {
	context := bitVectorContext(left, right)
	if left.fast.kind == bitVectorFastSymbol && right.fast.kind == bitVectorFastValue {
		return bitVecExprValue{contextID: context, fast: bitVectorFast{kind: bitVectorFastMaskedSymbol, width: left.fast.width, id: left.fast.id, name: left.fast.name, mask: right.fast.value}}
	}
	if right.fast.kind == bitVectorFastSymbol && left.fast.kind == bitVectorFastValue {
		return bitVecExprValue{contextID: context, fast: bitVectorFast{kind: bitVectorFastMaskedSymbol, width: right.fast.width, id: right.fast.id, name: right.fast.name, mask: left.fast.value}}
	}
	return bitVecExprValue{contextID: context, term: smt.BitVecAnd(materializeBitVector(left.term, left.fast), materializeBitVector(right.term, right.fast))}
}

func binaryBitVector(left, right BitVecExpr, operation uint8) BitVecExpr {
	context := bitVectorContext(left, right)
	if left.fast.kind == bitVectorFastSymbol && right.fast.kind == bitVectorFastValue && operation >= 4 {
		compactOperation := operation - 3
		return bitVecExprValue{contextID: context, fast: bitVectorFast{kind: bitVectorFastAppliedSymbol, width: left.fast.width, id: left.fast.id, name: left.fast.name, operation: compactOperation, operand: right.fast.value}}
	}
	leftTerm, rightTerm := materializeBitVector(left.term, left.fast), materializeBitVector(right.term, right.fast)
	var term smt.Term[smt.BitVecSort]
	switch operation {
	case 2:
		term = smt.BitVecOr(leftTerm, rightTerm)
	case 3:
		term = smt.BitVecXor(leftTerm, rightTerm)
	case 4:
		term = smt.BitVecAdd(leftTerm, rightTerm)
	case 5:
		term = smt.BitVecSub(leftTerm, rightTerm)
	case 6:
		term = smt.BitVecMul(leftTerm, rightTerm)
	case 7:
		term = smt.BitVecSHL(leftTerm, rightTerm)
	case 8:
		term = smt.BitVecLSHR(leftTerm, rightTerm)
	case 9:
		term = smt.BitVecASHR(leftTerm, rightTerm)
	case 10:
		term = smt.BitVecUDiv(leftTerm, rightTerm)
	case 11:
		term = smt.BitVecURem(leftTerm, rightTerm)
	case 12:
		term = smt.BitVecSDiv(leftTerm, rightTerm)
	default:
		term = smt.BitVecSRem(leftTerm, rightTerm)
	}
	return bitVecExprValue{contextID: context, term: term}
}

func fastEqBitVector(left, right BitVecExpr) BoolExpr {
	context := bitVectorContext(left, right)
	if left.fast.kind == bitVectorFastValue && right.fast.kind == bitVectorFastValue {
		return boolExprValue{contextID: context, term: smt.Bool{Value: smt.EqualBitVectorValue(left.fast.value, right.fast.value)}}
	}
	if relation, ok := compactBitVectorArrayStoreReadValue(left.fast, right.fast); ok {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorArrayStoreReadValue, bitVectorArrayStoreReadValue: relation}}
	}
	if relation, ok := compactBitVectorArrayStoreReadValue(right.fast, left.fast); ok {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorArrayStoreReadValue, bitVectorArrayStoreReadValue: relation}}
	}
	if relation, ok := compactBitVectorEUFRelation(left.fast, right.fast); ok {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorEUFRelation, bitVectorEUFRelation: relation}}
	}
	if relation, ok := compactBitVectorRelation(left.fast, right.fast); ok {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorRelation, bitVectorRelation: relation}}
	}
	if relation, ok := compactBitVectorRelation(right.fast, left.fast); ok {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorRelation, bitVectorRelation: relation}}
	}
	return fastBooleanAtom(context, smt.Equal{Left: materializeBitVector(left.term, left.fast), Right: materializeBitVector(right.term, right.fast)})
}

func compactBitVectorArrayStoreReadValue(read, constant bitVectorFast) (smt.BitVectorArrayStoreReadValueRelation, bool) {
	if read.kind != bitVectorFastArrayStoreRead || constant.kind != bitVectorFastValue {
		return smt.BitVectorArrayStoreReadValueRelation{}, false
	}
	return smt.BitVectorArrayStoreReadValueRelation{
		ArrayID: read.id, StoreIndexID: read.firstID, ReadIndexID: read.functionID,
		IndexWidth: read.firstWidth, ElementWidth: read.width, StoredValue: read.operand, ComparedValue: constant.value,
	}, true
}

func compactBitVectorEUFRelation(left, right bitVectorFast) (smt.BitVectorEUFRelation, bool) {
	leftTerm, leftOK := compactBitVectorEUFTerm(left)
	rightTerm, rightOK := compactBitVectorEUFTerm(right)
	if !leftOK || !rightOK || leftTerm.Width != rightTerm.Width {
		return smt.BitVectorEUFRelation{}, false
	}
	return smt.BitVectorEUFRelation{Left: leftTerm, Right: rightTerm}, true
}

func compactBitVectorEUFTerm(value bitVectorFast) (smt.BitVectorEUFTerm, bool) {
	switch value.kind {
	case bitVectorFastSymbol:
		return smt.BitVectorEUFTerm{Kind: 1, Width: value.width, SymbolID: value.id}, true
	case bitVectorFastUnaryApplication:
		return smt.BitVectorEUFTerm{Kind: 2, Width: value.width, FunctionID: value.functionID, FirstID: value.firstID, FirstWidth: value.firstWidth}, true
	default:
		return smt.BitVectorEUFTerm{}, false
	}
}

func applyBitVectorFunction(context int, function smt.SortedUnaryFunction[smt.BitVecSort, smt.BitVecSort], argument BitVecExpr) BitVecExpr {
	if context != argument.contextID {
		panic("gosmt: erased bit-vector function context mismatch")
	}
	if argument.fast.kind == bitVectorFastSymbol {
		_, rangeWidth, functionID := smt.BitVecUnaryFunctionInfo(function)
		return bitVecExprValue{contextID: context, fast: bitVectorFast{kind: bitVectorFastUnaryApplication, width: rangeWidth, functionID: functionID, firstID: argument.fast.id, firstName: argument.fast.name, firstWidth: argument.fast.width, function: function}}
	}
	return bitVecExprValue{contextID: context, term: smt.ApplyBitVecUnary(function, materializeBitVector(argument.term, argument.fast))}
}

func fastOrderBitVector(left, right BitVecExpr, order uint8) BoolExpr {
	context := bitVectorContext(left, right)
	if left.fast.kind == bitVectorFastSymbol && right.fast.kind == bitVectorFastValue {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorRelation, bitVectorRelation: smt.BitVectorRelation{
			Width: left.fast.width, SymbolID: left.fast.id, Value: right.fast.value, Order: order,
		}}}
	}
	leftTerm, rightTerm := materializeBitVector(left.term, left.fast), materializeBitVector(right.term, right.fast)
	var term smt.Term[smt.BoolSort]
	switch order {
	case 1:
		term = smt.BitVecULT(leftTerm, rightTerm)
	case 2:
		term = smt.BitVecULE(leftTerm, rightTerm)
	case 3:
		term = smt.BitVecSLT(leftTerm, rightTerm)
	default:
		term = smt.BitVecSLE(leftTerm, rightTerm)
	}
	return fastBooleanAtom(context, term)
}

func subtractInteger(left, right IntExpr) IntExpr {
	if left.contextID != right.contextID {
		panic("gosmt: erased integer expression context mismatch")
	}
	return intExprValue{contextID: left.contextID, term: smt.Subtract{Left: materializeInteger(left.term, left.fast), Right: materializeInteger(right.term, right.fast)}}
}

func compareInteger(left, right IntExpr, strict bool) BoolExpr {
	if left.contextID != right.contextID {
		panic("gosmt: erased integer expression context mismatch")
	}
	if left.fast.kind == integerFastStringLength && right.fast.kind == integerFastStringLength {
		order := uint8(2)
		if strict {
			order = 1
		}
		return fastBooleanAtom(left.contextID, smt.CompactStringLengthRelation{
			Left: left.fast.string, Right: right.fast.string, Order: order,
		})
	}
	if relation, ok := compactStringLengthComparison(left, right, strict); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{
			kind: booleanFastStringRelation, stringRelation: relation,
		}}
	}
	application, constant, applicationOnLeft := left, right, true
	if !application.fast.eufValid {
		application, constant, applicationOnLeft = right, left, false
	}
	if application.fast.eufValid {
		if bound, ok := fastIntegerConstant(constant); ok {
			if application.fast.eufArity == 3 {
				return boolExprValue{contextID: left.contextID, fast: booleanFast{
					kind: booleanFastIntegerTernaryComparison,
					integerTernaryComparison: smt.IntegerTernaryComparison{
						FunctionID:        application.fast.functionID,
						FirstArgumentID:   application.fast.argumentID,
						SecondArgumentID:  application.fast.secondArgumentID,
						ThirdArgumentID:   application.fast.thirdArgumentID,
						Bound:             bound,
						ApplicationOnLeft: applicationOnLeft,
						Strict:            strict,
					},
				}}
			}
			if application.fast.eufArity == 2 {
				return boolExprValue{contextID: left.contextID, fast: booleanFast{
					kind: booleanFastIntegerBinaryComparison,
					integerBinaryComparison: smt.IntegerBinaryComparison{
						FunctionID:       application.fast.functionID,
						FirstArgumentID:  application.fast.argumentID,
						SecondArgumentID: application.fast.secondArgumentID,
						Bound:            bound, ApplicationOnLeft: applicationOnLeft,
						Strict: strict,
					},
				}}
			}
			return boolExprValue{contextID: left.contextID, fast: booleanFast{
				kind: booleanFastIntegerUnaryComparison,
				integerUnaryComparison: smt.IntegerUnaryComparison{
					FunctionID: application.fast.functionID,
					ArgumentID: application.fast.argumentID,
					Bound:      bound, ApplicationOnLeft: applicationOnLeft,
					Strict: strict,
				},
			}}
		}
	}
	leftTerm, rightTerm := materializeInteger(left.term, left.fast), materializeInteger(right.term, right.fast)
	if constraint, ok := compactIntegerDifference(leftTerm, rightTerm, strict); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastIntegerDifference, integerDifference: constraint}}
	}
	term := smt.Term[smt.BoolSort](smt.LessEqual{Left: leftTerm, Right: rightTerm})
	if strict {
		term = smt.Less{Left: leftTerm, Right: rightTerm}
	}
	return boolExprValue{contextID: left.contextID, term: term}
}

func fastIntegerConstant(value IntExpr) (smt.IntegerValue, bool) {
	if value.fast.kind != integerFastNone || value.fast.eufValid {
		return smt.IntegerValue{}, false
	}
	return smt.ExactIntegerConstant(value.term)
}

func compactStringLengthComparison(left, right IntExpr, strict bool) (smt.CompactStringRelation, bool) {
	length, constant, lengthOnLeft := left, right, true
	if length.fast.kind != integerFastStringLength {
		length, constant, lengthOnLeft = right, left, false
	}
	if length.fast.kind != integerFastStringLength || constant.fast.kind != integerFastNone {
		return smt.CompactStringRelation{}, false
	}
	value, ok := smt.ExactIntegerConstant(constant.term)
	if !ok {
		return smt.CompactStringRelation{}, false
	}
	integer, fits := value.Int64()
	if !fits {
		return smt.CompactStringRelation{}, false
	}
	relation := smt.CompactStringRelation{
		Kind:    smt.CompactStringLengthLessEqual,
		Left:    length.fast.string,
		Integer: integer,
	}
	if strict {
		relation.Kind = smt.CompactStringLengthLess
	}
	if !lengthOnLeft {
		relation.Negated = true
		if strict {
			relation.Kind = smt.CompactStringLengthLessEqual
		} else {
			relation.Kind = smt.CompactStringLengthLess
		}
	}
	return relation, true
}

func compactIntegerDifference(left, right smt.Term[smt.IntSort], strict bool) (smt.IntegerDifferenceConstraint, bool) {
	if positive, positiveOK := smt.IntegerVariableID(left); positiveOK {
		if negative, negativeOK := smt.IntegerVariableID(right); negativeOK {
			return smt.IntegerDifferenceConstraint{PositiveID: positive, NegativeID: negative, HasPositive: true, HasNegative: true, Strict: strict}, true
		}
	}
	if difference, ok := left.(smt.Subtract); ok {
		positive, positiveOK := smt.IntegerVariableID(difference.Left)
		negative, negativeOK := smt.IntegerVariableID(difference.Right)
		constant, constantOK := smt.ExactIntegerConstant(right)
		if positiveOK && negativeOK && constantOK {
			if bound, fits := constant.Int64(); fits {
				return smt.IntegerDifferenceConstraint{PositiveID: positive, NegativeID: negative, HasPositive: true, HasNegative: true, Bound: bound, Strict: strict}, true
			}
			return smt.IntegerDifferenceConstraint{PositiveID: positive, NegativeID: negative, HasPositive: true, HasNegative: true, WideBound: constant, Wide: true, Strict: strict}, true
		}
	}
	if symbol, ok := smt.IntegerVariableID(left); ok {
		if constant, constantOK := smt.ExactIntegerConstant(right); constantOK {
			if bound, fits := constant.Int64(); fits {
				return smt.IntegerDifferenceConstraint{PositiveID: symbol, HasPositive: true, Bound: bound, Strict: strict}, true
			}
			return smt.IntegerDifferenceConstraint{PositiveID: symbol, HasPositive: true, WideBound: constant, Wide: true, Strict: strict}, true
		}
	}
	if constant, ok := smt.ExactIntegerConstant(left); ok {
		if symbol, symbolOK := smt.IntegerVariableID(right); symbolOK {
			bound, fits := constant.Int64()
			if !fits || bound == -1<<63 {
				return smt.IntegerDifferenceConstraint{}, false
			}
			return smt.IntegerDifferenceConstraint{NegativeID: symbol, HasNegative: true, Bound: -bound, Strict: strict}, true
		}
	}
	return smt.IntegerDifferenceConstraint{}, false
}

func overflowBitVector(left, right BitVecExpr, predicate uint8) BoolExpr {
	context := bitVectorContext(left, right)
	if left.fast.kind == bitVectorFastSymbol && right.fast.kind == bitVectorFastValue {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastBitVectorRelation, bitVectorRelation: smt.BitVectorRelation{
			Width: left.fast.width, SymbolID: left.fast.id, Operand: right.fast.value, Predicate: predicate,
		}}}
	}
	leftTerm, rightTerm := materializeBitVector(left.term, left.fast), materializeBitVector(right.term, right.fast)
	var term smt.Term[smt.BoolSort]
	switch predicate {
	case 1:
		term = smt.BitVecUAddOverflow(leftTerm, rightTerm)
	case 2:
		term = smt.BitVecSAddOverflow(leftTerm, rightTerm)
	case 3:
		term = smt.BitVecUSubOverflow(leftTerm, rightTerm)
	case 4:
		term = smt.BitVecSSubOverflow(leftTerm, rightTerm)
	case 5:
		term = smt.BitVecUMulOverflow(leftTerm, rightTerm)
	case 6:
		term = smt.BitVecSMulOverflow(leftTerm, rightTerm)
	default:
		term = smt.BitVecSDivOverflow(leftTerm, rightTerm)
	}
	return fastBooleanAtom(context, term)
}

func negOverflowBitVector(value BitVecExpr) BoolExpr {
	if value.fast.kind == bitVectorFastSymbol {
		return boolExprValue{contextID: value.contextID, fast: booleanFast{kind: booleanFastBitVectorRelation, bitVectorRelation: smt.BitVectorRelation{
			Width: value.fast.width, SymbolID: value.fast.id, Predicate: 8,
		}}}
	}
	return fastBooleanAtom(value.contextID, smt.BitVecNegOverflow(materializeBitVector(value.term, value.fast)))
}

func compactBitVectorRelation(expression, constant bitVectorFast) (smt.BitVectorRelation, bool) {
	if constant.kind != bitVectorFastValue {
		return smt.BitVectorRelation{}, false
	}
	switch expression.kind {
	case bitVectorFastSymbol:
		return smt.BitVectorRelation{Width: expression.width, SymbolID: expression.id, Value: constant.value}, true
	case bitVectorFastMaskedSymbol:
		return smt.BitVectorRelation{Width: expression.width, SymbolID: expression.id, Value: constant.value, Mask: expression.mask, Masked: true}, true
	case bitVectorFastAppliedSymbol:
		return smt.BitVectorRelation{Width: expression.width, SymbolID: expression.id, Value: constant.value, Operation: expression.operation, Operand: expression.operand, ParameterA: expression.parameterA, ParameterB: expression.parameterB}, true
	}
	return smt.BitVectorRelation{}, false
}

func materializeBitVector(term smt.Term[smt.BitVecSort], fast bitVectorFast) smt.Term[smt.BitVecSort] {
	switch fast.kind {
	case bitVectorFastValue:
		return smt.BitVectorTerm(fast.value)
	case bitVectorFastSymbol:
		return smt.BitVecConst(fast.width, fast.id, fast.name)
	case bitVectorFastMaskedSymbol:
		return smt.BitVecAnd(smt.BitVecConst(fast.width, fast.id, fast.name), smt.BitVectorTerm(fast.mask))
	case bitVectorFastAppliedSymbol:
		sourceWidth := fast.width
		if fast.sourceWidth != 0 {
			sourceWidth = fast.sourceWidth
		}
		symbol, operand := smt.BitVecConst(sourceWidth, fast.id, fast.name), smt.BitVectorTerm(fast.operand)
		switch fast.operation {
		case 1:
			return smt.BitVecAdd(symbol, operand)
		case 2:
			return smt.BitVecSub(symbol, operand)
		case 3:
			return smt.BitVecMul(symbol, operand)
		case 4:
			return smt.BitVecSHL(symbol, operand)
		case 5:
			return smt.BitVecLSHR(symbol, operand)
		case 6:
			return smt.BitVecASHR(symbol, operand)
		case 7:
			return smt.BitVecUDiv(symbol, operand)
		case 8:
			return smt.BitVecURem(symbol, operand)
		case 9:
			return smt.BitVecSDiv(symbol, operand)
		case 10:
			return smt.BitVecSRem(symbol, operand)
		case 11:
			return smt.BitVecExtract(fast.parameterA, fast.parameterB, symbol)
		case 12:
			return smt.BitVecZeroExtend(fast.parameterA, symbol)
		case 13:
			return smt.BitVecSignExtend(fast.parameterA, symbol)
		case 14:
			return smt.BitVecRotateLeft(fast.parameterA, symbol)
		case 15:
			return smt.BitVecRotateRight(fast.parameterA, symbol)
		default:
			return smt.BitVecRepeat(fast.parameterA, symbol)
		}
	case bitVectorFastUnaryApplication:
		return smt.ApplyBitVecUnary(fast.function, smt.BitVecConst(fast.firstWidth, fast.firstID, fast.firstName))
	default:
		return term
	}
}

func concatBitVector(firstWidth, secondWidth int, first, second BitVecExpr) BitVecExpr {
	context := bitVectorContext(first, second)
	return bitVecExprValue{contextID: context, term: smt.BitVecConcat(firstWidth, secondWidth, materializeBitVector(first.term, first.fast), materializeBitVector(second.term, second.fast))}
}

func extractBitVector(high, low int, value BitVecExpr) BitVecExpr {
	if low < 0 || high < low || value.fast.kind != bitVectorFastNone && high >= value.fast.width {
		panic("gosmt: invalid bit-vector extraction range")
	}
	if value.fast.kind == bitVectorFastSymbol {
		return bitVecExprValue{contextID: value.contextID, fast: bitVectorFast{kind: bitVectorFastAppliedSymbol, width: high - low + 1, sourceWidth: value.fast.width, id: value.fast.id, name: value.fast.name, operation: 11, parameterA: high, parameterB: low}}
	}
	return bitVecExprValue{contextID: value.contextID, term: smt.BitVecExtract(high, low, materializeBitVector(value.term, value.fast))}
}

func extendBitVector(additional int, value BitVecExpr, signed bool) BitVecExpr {
	if additional < 0 {
		panic("gosmt: negative bit-vector extension")
	}
	if value.fast.kind == bitVectorFastSymbol {
		operation := uint8(12)
		if signed {
			operation = 13
		}
		return bitVecExprValue{contextID: value.contextID, fast: bitVectorFast{kind: bitVectorFastAppliedSymbol, width: value.fast.width + additional, sourceWidth: value.fast.width, id: value.fast.id, name: value.fast.name, operation: operation, parameterA: additional}}
	}
	operand := materializeBitVector(value.term, value.fast)
	term := smt.BitVecZeroExtend(additional, operand)
	if signed {
		term = smt.BitVecSignExtend(additional, operand)
	}
	return bitVecExprValue{contextID: value.contextID, term: term}
}

func rotateBitVector(amount int, value BitVecExpr, left bool) BitVecExpr {
	if amount < 0 {
		panic("gosmt: negative bit-vector rotation")
	}
	if value.fast.kind == bitVectorFastSymbol {
		operation := uint8(15)
		if left {
			operation = 14
		}
		return bitVecExprValue{contextID: value.contextID, fast: bitVectorFast{kind: bitVectorFastAppliedSymbol, width: value.fast.width, sourceWidth: value.fast.width, id: value.fast.id, name: value.fast.name, operation: operation, parameterA: amount}}
	}
	operand := materializeBitVector(value.term, value.fast)
	term := smt.BitVecRotateRight(amount, operand)
	if left {
		term = smt.BitVecRotateLeft(amount, operand)
	}
	return bitVecExprValue{contextID: value.contextID, term: term}
}

func repeatBitVector(count int, value BitVecExpr) BitVecExpr {
	if count <= 0 {
		panic("gosmt: bit-vector repeat count must be positive")
	}
	if value.fast.kind == bitVectorFastSymbol {
		return bitVecExprValue{contextID: value.contextID, fast: bitVectorFast{kind: bitVectorFastAppliedSymbol, width: value.fast.width * count, sourceWidth: value.fast.width, id: value.fast.id, name: value.fast.name, operation: 16, parameterA: count}}
	}
	return bitVecExprValue{contextID: value.contextID, term: smt.BitVecRepeat(count, materializeBitVector(value.term, value.fast))}
}

func bitVectorContext(left, right BitVecExpr) int {
	if left.contextID != right.contextID {
		panic("gosmt: erased bit-vector expression context mismatch")
	}
	return left.contextID
}

func fastBooleanAtom(context int, term smt.Term[smt.BoolSort]) BoolExpr {
	return boolExprValue{contextID: context, term: term, fast: booleanFast{kind: booleanFastAtom}}
}

type realCoefficient struct {
	symbol int
	value  smt.Rational
}

type realFast struct {
	valid            bool
	eufValid         bool
	eufArity         uint8
	functionID       int
	argumentID       int
	secondArgumentID int
	count            uint8
	inline           [4]realCoefficient
	overflow         []realCoefficient
	constant         smt.Rational
}

type realFunctionFast struct {
	valid bool
	id    int
	name  string
}

type realBinaryFunctionFast struct {
	valid bool
	id    int
	name  string
}

func fastRealFunction(context, id int, name string) RealFunc {
	return realFuncValue{contextID: context, fast: realFunctionFast{valid: true, id: id, name: name}}
}

func applyRealFunction(function RealFunc, argument RealExpr) RealExpr {
	if function.contextID != argument.contextID {
		panic("gosmt: erased real function context mismatch")
	}
	if function.fast.valid && argument.fast.valid && argument.fast.constant.Sign() == 0 && argument.fast.count == 1 {
		coefficient := argument.fast.coefficients()[0]
		if smt.CompareRational(coefficient.value, smt.NewRational(1, 1)) == 0 {
			return realExprValue{contextID: function.contextID, fast: realFast{eufValid: true, eufArity: 1, functionID: function.fast.id, argumentID: coefficient.symbol}}
		}
	}
	core := function.function
	if function.fast.valid {
		core = smt.DeclareRealUnaryFunction(function.fast.id, function.fast.name)
	}
	return realExprValue{contextID: function.contextID, term: smt.ApplySortedUnary(core, materializeReal(argument.term, argument.fast))}
}

func fastRealBinaryFunction(context, id int, name string) RealBinaryFunc {
	return realBinaryFuncValue{contextID: context, fast: realBinaryFunctionFast{valid: true, id: id, name: name}}
}

func applyRealBinaryFunction(function RealBinaryFunc, first, second RealExpr) RealExpr {
	context := realPairContext(first, second)
	if function.contextID != context {
		panic("gosmt: erased real binary function context mismatch")
	}
	firstID, firstOK := fastRealSymbolID(first.fast)
	secondID, secondOK := fastRealSymbolID(second.fast)
	if function.fast.valid && firstOK && secondOK {
		return realExprValue{contextID: context, fast: realFast{
			eufValid: true, eufArity: 2, functionID: function.fast.id,
			argumentID: firstID, secondArgumentID: secondID,
		}}
	}
	core := function.function
	if function.fast.valid {
		core = smt.DeclareRealBinaryFunction(function.fast.id, function.fast.name)
	}
	return realExprValue{contextID: context, term: smt.ApplySortedBinary(core, materializeReal(first.term, first.fast), materializeReal(second.term, second.fast))}
}

func fastEqReal(left, right RealExpr) BoolExpr {
	context := realPairContext(left, right)
	if left.fast.eufValid && right.fast.eufValid && left.fast.eufArity == 1 && right.fast.eufArity == 1 {
		return fastBooleanAtom(context, smt.RealUnaryEquality{
			LeftFunctionID: left.fast.functionID, LeftArgumentID: left.fast.argumentID,
			RightFunctionID: right.fast.functionID, RightArgumentID: right.fast.argumentID,
		})
	}
	if leftID, leftOK := fastRealSymbolID(left.fast); leftOK {
		if rightID, rightOK := fastRealSymbolID(right.fast); rightOK {
			return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastRealSymbolEquality, symbolEquality: smt.RealSymbolEquality{LeftID: leftID, RightID: rightID}}}
		}
	}
	return fastBooleanAtom(context, smt.Equal{
		Left:  materializeReal(left.term, left.fast),
		Right: materializeReal(right.term, right.fast),
	})
}

func fastRealSymbolID(value realFast) (int, bool) {
	if !value.valid || value.constant.Sign() != 0 || value.count != 1 {
		return 0, false
	}
	coefficient := value.coefficients()[0]
	return coefficient.symbol, smt.CompareRational(coefficient.value, smt.NewRational(1, 1)) == 0
}

func fastRealConstant(value realFast) (smt.Rational, bool) {
	return value.constant, value.valid && value.count == 0
}

func (value *realFast) coefficients() []realCoefficient {
	if value.overflow != nil {
		return value.overflow[:value.count]
	}
	return value.inline[:value.count]
}

func (value *realFast) add(symbol int, coefficient smt.Rational) {
	for index := range value.coefficients() {
		if value.coefficients()[index].symbol == symbol {
			value.coefficients()[index].value = smt.AddRational(value.coefficients()[index].value, coefficient)
			return
		}
	}
	if int(value.count) < len(value.inline) && value.overflow == nil {
		value.inline[value.count] = realCoefficient{symbol: symbol, value: coefficient}
		value.count++
		return
	}
	if value.overflow == nil {
		value.overflow = make([]realCoefficient, value.count, int(value.count)*2)
		copy(value.overflow, value.inline[:value.count])
	}
	value.overflow = append(value.overflow, realCoefficient{symbol: symbol, value: coefficient})
	value.count++
}

func (value *realFast) accumulate(other realFast, multiplier smt.Rational) {
	value.constant = smt.AddRational(value.constant, smt.MultiplyRational(other.constant, multiplier))
	for _, coefficient := range other.coefficients() {
		value.add(coefficient.symbol, smt.MultiplyRational(coefficient.value, multiplier))
	}
}

func fastRealSymbol(context, id int) RealExpr {
	fast := realFast{valid: true, count: 1}
	fast.inline[0] = realCoefficient{symbol: id, value: smt.NewRational(1, 1)}
	return realExprValue{contextID: context, fast: fast}
}

func fastRealValue(context int, value smt.Rational) RealExpr {
	return realExprValue{contextID: context, fast: realFast{valid: true, constant: value}}
}

func fastAddReal(values []RealExpr) RealExpr {
	context := realContext(values)
	fast := realFast{valid: true}
	for _, value := range values {
		if !value.fast.valid {
			_, terms := realTerms(values)
			return realExprValue{contextID: context, term: smt.RealAdd{Values: terms}}
		}
		fast.accumulate(value.fast, smt.NewRational(1, 1))
	}
	return realExprValue{contextID: context, fast: fast}
}

func fastSubReal(left, right RealExpr) RealExpr {
	context := realPairContext(left, right)
	if left.fast.valid && right.fast.valid {
		fast := realFast{valid: true}
		fast.accumulate(left.fast, smt.NewRational(1, 1))
		fast.accumulate(right.fast, smt.NewRational(-1, 1))
		return realExprValue{contextID: context, fast: fast}
	}
	return realExprValue{contextID: context, term: smt.RealSubtract{Left: materializeReal(left.term, left.fast), Right: materializeReal(right.term, right.fast)}}
}

func fastScaleReal(coefficient smt.Rational, value RealExpr) RealExpr {
	if value.fast.valid {
		fast := realFast{valid: true}
		fast.accumulate(value.fast, coefficient)
		return realExprValue{contextID: value.contextID, fast: fast}
	}
	return realExprValue{contextID: value.contextID, term: smt.RealScale{Coefficient: coefficient, Value: value.term}}
}

func fastRealRelation(left, right RealExpr, strict bool) BoolExpr {
	context := realPairContext(left, right)
	if left.fast.eufValid {
		if bound, ok := fastRealConstant(right.fast); ok {
			if left.fast.eufArity == 2 {
				return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastRealBinaryComparison, binaryComparison: smt.RealBinaryComparison{
					FunctionID: left.fast.functionID, FirstArgumentID: left.fast.argumentID, SecondArgumentID: left.fast.secondArgumentID,
					Bound: bound, ApplicationOnLeft: true, Strict: strict,
				}}}
			}
			return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastRealUnaryComparison, unaryComparison: smt.RealUnaryComparison{
				FunctionID: left.fast.functionID, ArgumentID: left.fast.argumentID,
				Bound: bound, ApplicationOnLeft: true, Strict: strict,
			}}}
		}
	}
	if right.fast.eufValid {
		if bound, ok := fastRealConstant(left.fast); ok {
			if right.fast.eufArity == 2 {
				return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastRealBinaryComparison, binaryComparison: smt.RealBinaryComparison{
					FunctionID: right.fast.functionID, FirstArgumentID: right.fast.argumentID, SecondArgumentID: right.fast.secondArgumentID,
					Bound: bound, ApplicationOnLeft: false, Strict: strict,
				}}}
			}
			return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastRealUnaryComparison, unaryComparison: smt.RealUnaryComparison{
				FunctionID: right.fast.functionID, ArgumentID: right.fast.argumentID,
				Bound: bound, ApplicationOnLeft: false, Strict: strict,
			}}}
		}
	}
	if left.fast.valid && right.fast.valid {
		fast := realFast{valid: true}
		fast.accumulate(left.fast, smt.NewRational(1, 1))
		fast.accumulate(right.fast, smt.NewRational(-1, 1))
		constraint := smt.LinearRealConstraint{Count: int(fast.count), Constant: fast.constant, Strict: strict}
		for index, coefficient := range fast.coefficients() {
			if index < len(constraint.Symbols) {
				constraint.Symbols[index] = coefficient.symbol
				constraint.Coefficients[index] = coefficient.value
				continue
			}
			if constraint.OverflowSymbols == nil {
				constraint.OverflowSymbols = make([]int, fast.count)
				constraint.OverflowCoefficients = make([]smt.Rational, fast.count)
				for inline := 0; inline < len(constraint.Symbols); inline++ {
					constraint.OverflowSymbols[inline] = constraint.Symbols[inline]
					constraint.OverflowCoefficients[inline] = constraint.Coefficients[inline]
				}
			}
			constraint.OverflowSymbols[index] = coefficient.symbol
			constraint.OverflowCoefficients[index] = coefficient.value
		}
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastRealConstraint, real: constraint}}
	}
	leftTerm := materializeReal(left.term, left.fast)
	rightTerm := materializeReal(right.term, right.fast)
	if strict {
		return boolExprValue{contextID: context, term: smt.RealLess{Left: leftTerm, Right: rightTerm}}
	}
	return boolExprValue{contextID: context, term: smt.RealLessEqual{Left: leftTerm, Right: rightTerm}}
}

func realContext(values []RealExpr) int {
	if len(values) == 0 {
		return 0
	}
	context := values[0].contextID
	for _, value := range values[1:] {
		if value.contextID != context {
			panic("gosmt: erased real expression context mismatch")
		}
	}
	return context
}

func realPairContext(left, right RealExpr) int {
	if left.contextID != right.contextID {
		panic("gosmt: erased real expression context mismatch")
	}
	return left.contextID
}

func materializeReal(term smt.Term[smt.RealSort], fast realFast) smt.Term[smt.RealSort] {
	if fast.eufValid {
		if fast.eufArity == 2 {
			function := smt.DeclareRealBinaryFunction(fast.functionID, "")
			return smt.ApplySortedBinary(function, smt.RealSymbol{ID: fast.argumentID}, smt.RealSymbol{ID: fast.secondArgumentID})
		}
		function := smt.DeclareRealUnaryFunction(fast.functionID, "")
		return smt.ApplySortedUnary(function, smt.RealSymbol{ID: fast.argumentID})
	}
	if !fast.valid {
		return term
	}
	terms := make([]smt.Term[smt.RealSort], 0, int(fast.count)+1)
	if fast.constant.Sign() != 0 || fast.count == 0 {
		terms = append(terms, smt.Real{Value: fast.constant})
	}
	for _, coefficient := range fast.coefficients() {
		symbol := smt.Term[smt.RealSort](smt.RealSymbol{ID: coefficient.symbol})
		if smt.CompareRational(coefficient.value, smt.NewRational(1, 1)) == 0 {
			terms = append(terms, symbol)
		} else {
			terms = append(terms, smt.RealScale{Coefficient: coefficient.value, Value: symbol})
		}
	}
	if len(terms) == 1 {
		return terms[0]
	}
	return smt.RealAdd{Values: terms}
}

func fastBooleanVariable(context, id int) BoolExpr {
	fast := booleanFast{kind: booleanFastLiteral, count: 1}
	fast.inline[0] = id + 1
	return boolExprValue{contextID: context, fast: fast}
}

func fastNot(value BoolExpr) BoolExpr {
	if constant, ok := value.term.(smt.Bool); ok && value.fast.kind == booleanFastNone {
		return boolExprValue{contextID: value.contextID, term: smt.Bool{Value: !constant.Value}}
	}
	if _, ok := value.term.(smt.Less); ok &&
		value.fast.kind == booleanFastNone {
		value.fast.kind = booleanFastAtom
		value.fast.negated = true
		return value
	}
	if _, ok := value.term.(smt.LessEqual); ok &&
		value.fast.kind == booleanFastNone {
		value.fast.kind = booleanFastAtom
		value.fast.negated = true
		return value
	}
	if negation, ok := value.term.(smt.Not); ok &&
		value.fast.kind == booleanFastNone {
		return boolExprValue{
			contextID: value.contextID,
			term:      negation.Value,
		}
	}
	if value.fast.kind == booleanFastLiteral {
		value.fast.inline[0] = -value.fast.inline[0]
		return value
	}
	if value.fast.kind == booleanFastAtom {
		value.fast.negated = !value.fast.negated
		return value
	}
	if value.fast.kind == booleanFastBitVectorRelation {
		value.fast.bitVectorRelation.Negated = !value.fast.bitVectorRelation.Negated
		return value
	}
	if value.fast.kind == booleanFastBitVectorEUFRelation {
		value.fast.bitVectorEUFRelation.Negated = !value.fast.bitVectorEUFRelation.Negated
		return value
	}
	if value.fast.kind == booleanFastBitVectorIntegerRelation {
		value.fast.bitVectorIntegerRelation.Negated = !value.fast.bitVectorIntegerRelation.Negated
		return value
	}
	if value.fast.kind == booleanFastIntegerSymbolEquality {
		value.fast.integerSymbolNegated = !value.fast.integerSymbolNegated
		return value
	}
	if value.fast.kind == booleanFastArrayEquality {
		value.fast.arrayEquality.Negated = !value.fast.arrayEquality.Negated
		return value
	}
	if value.fast.kind == booleanFastArrayReadEquality {
		value.fast.arrayReadEquality.Negated = !value.fast.arrayReadEquality.Negated
		return value
	}
	if value.fast.kind == booleanFastArrayStoreEquality {
		value.fast.arrayStoreEquality.Negated = !value.fast.arrayStoreEquality.Negated
		return value
	}
	if value.fast.kind == booleanFastArrayConstantEquality {
		value.fast.arrayConstantEquality.Negated = !value.fast.arrayConstantEquality.Negated
		return value
	}
	if value.fast.kind == booleanFastArrayReadValue {
		value.fast.arrayReadValue.Negated = !value.fast.arrayReadValue.Negated
		return value
	}
	if value.fast.kind == booleanFastArrayStoreReadValue {
		value.fast.arrayStoreReadValue.Negated = !value.fast.arrayStoreReadValue.Negated
		return value
	}
	if value.fast.kind == booleanFastBitVectorArrayStoreReadValue {
		value.fast.bitVectorArrayStoreReadValue.Negated = !value.fast.bitVectorArrayStoreReadValue.Negated
		return value
	}
	if value.fast.kind == booleanFastBitVectorArrayEquality {
		value.fast.bitVectorArrayEquality.Negated = !value.fast.bitVectorArrayEquality.Negated
		return value
	}
	if value.fast.kind == booleanFastIntegerLinearEquality {
		value.fast.kind = booleanFastIntegerLinearDisequality
		return value
	}
	if value.fast.kind == booleanFastIntegerLinearDisequality {
		value.fast.kind = booleanFastIntegerLinearEquality
		return value
	}
	if value.fast.kind == booleanFastUninterpretedEUFRelation {
		value.fast.uninterpretedEUFRelation.Negated = !value.fast.uninterpretedEUFRelation.Negated
		return value
	}
	if value.fast.kind == booleanFastStringRelation {
		value.fast.stringRelation.Negated = !value.fast.stringRelation.Negated
		return value
	}
	if value.fast.kind == booleanFastStringBooleanFormula {
		if formula, ok := smt.CompactStringBooleanNotFormula(value.fast.stringBooleanFormula); ok {
			value.fast.stringBooleanFormula = formula
			return value
		}
	}
	if value.fast.kind == booleanFastNone && value.term != nil {
		value.fast.kind = booleanFastAtom
		value.fast.negated = true
		return value
	}
	return boolExprValue{contextID: value.contextID, term: smt.Not{Value: materializeBoolean(value.term, value.fast)}}
}

func fastOr(values []BoolExpr) BoolExpr {
	context := booleanContext(values)
	if formula, ok := combineCompactStringBooleanValues(values, false); ok {
		return boolExprValue{contextID: context, fast: booleanFast{
			kind: booleanFastStringBooleanFormula, stringBooleanFormula: formula,
		}}
	}
	if len(values) == 2 && values[0].fast.kind == booleanFastIntegerLinearEquality && values[1].fast.kind == booleanFastIntegerLinearEquality {
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastIntegerLinearChoice, integerLinearChoice: smt.IntegerLinearChoice{
			First: values[0].fast.integerLinearEquality, Second: values[1].fast.integerLinearEquality,
		}}}
	}
	fast := booleanFast{kind: booleanFastClause, count: uint8(len(values))}
	if len(values) > len(fast.inline) {
		fast.overflow = make([]int, len(values))
	}
	for index, value := range values {
		if value.fast.kind != booleanFastLiteral || len(values) > 255 {
			_, terms := booleanTerms(values)
			return boolExprValue{contextID: context, term: smt.Or{Values: terms}}
		}
		if fast.overflow != nil {
			fast.overflow[index] = value.fast.inline[0]
		} else {
			fast.inline[index] = value.fast.inline[0]
		}
	}
	return boolExprValue{contextID: context, fast: fast}
}

func fastAnd(values []BoolExpr) BoolExpr {
	context := booleanContext(values)
	allConstants, result := len(values) > 0, true
	for _, value := range values {
		constant, ok := value.term.(smt.Bool)
		if !ok || value.fast.kind != booleanFastNone {
			allConstants = false
			break
		}
		result = result && constant.Value
	}
	if allConstants {
		return boolExprValue{contextID: context, term: smt.Bool{Value: result}}
	}
	groundEvaluation := &smt.CompactGroundStringEvaluationFormula{}
	allGroundEvaluation := len(values) > 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastStringRelation:
			relation := value.fast.stringRelation
			if relation.Kind != smt.CompactStringEqual || relation.Negated ||
				groundEvaluation.StringAssignmentCount == uint8(len(groundEvaluation.StringAssignments)) {
				allGroundEvaluation = false
				break
			}
			groundEvaluation.StringAssignments[groundEvaluation.StringAssignmentCount] = relation
			groundEvaluation.StringAssignmentCount++
		case booleanFastIntegerLinearEquality:
			if groundEvaluation.IntegerAssignmentCount == uint8(len(groundEvaluation.IntegerAssignments)) {
				allGroundEvaluation = false
				break
			}
			groundEvaluation.IntegerAssignments[groundEvaluation.IntegerAssignmentCount] = value.fast.integerLinearEquality
			groundEvaluation.IntegerAssignmentCount++
		case booleanFastStringIndexOfEquality:
			if groundEvaluation.IndexOfCount == uint8(len(groundEvaluation.IndexOf)) {
				allGroundEvaluation = false
				break
			}
			groundEvaluation.IndexOf[groundEvaluation.IndexOfCount] = value.fast.stringIndexOfEquality
			groundEvaluation.IndexOfCount++
		default:
			allGroundEvaluation = false
		}
		if !allGroundEvaluation {
			break
		}
	}
	if allGroundEvaluation && groundEvaluation.StringAssignmentCount != 0 &&
		groundEvaluation.IndexOfCount != 0 {
		return boolExprValue{contextID: context, fast: booleanFast{
			kind: booleanFastGroundStringEvaluationFormula, groundStringEvaluation: groundEvaluation,
		}}
	}
	indexed := &smt.CompactGroundIndexedStringFormula{}
	allGroundIndexed := len(values) > 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastIntegerLinearEquality:
			if indexed.AssignmentCount == uint8(len(indexed.Assignments)) {
				allGroundIndexed = false
				break
			}
			indexed.Assignments[indexed.AssignmentCount] = value.fast.integerLinearEquality
			indexed.AssignmentCount++
		case booleanFastStringIndexedEquality:
			if indexed.EqualityCount == uint8(len(indexed.Equalities)) {
				allGroundIndexed = false
				break
			}
			indexed.Equalities[indexed.EqualityCount] = value.fast.stringIndexedEquality
			indexed.EqualityCount++
		default:
			allGroundIndexed = false
		}
		if !allGroundIndexed {
			break
		}
	}
	if allGroundIndexed && indexed.AssignmentCount != 0 && indexed.EqualityCount != 0 {
		return boolExprValue{contextID: context, fast: booleanFast{
			kind: booleanFastGroundIndexedStringFormula, groundIndexedStringFormula: indexed,
		}}
	}
	if formula, ok := combineCompactStringBooleanValues(values, true); ok {
		return boolExprValue{contextID: context, fast: booleanFast{
			kind: booleanFastStringBooleanFormula, stringBooleanFormula: formula,
		}}
	}
	if cnf, ok := compactBooleanCNF(values); ok {
		return boolExprValue{contextID: context, term: cnf}
	}
	allStrings := len(values) > 0
	for _, value := range values {
		allStrings = allStrings && value.fast.kind == booleanFastStringRelation
	}
	if allStrings {
		var system smt.CompactStringSystem
		for _, value := range values {
			system = smt.AppendCompactStringRelation(system, value.fast.stringRelation)
		}
		return boolExprValue{contextID: context, term: smt.CompactStringAssertions(system)}
	}
	differenceCount, relationCount := 0, 0
	allCompactIntegerCongruence := len(values) > 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastIntegerDifference:
			differenceCount++
		case booleanFastIntegerSymbolEquality:
			if value.fast.integerSymbolNegated {
				allCompactIntegerCongruence = false
			} else {
				differenceCount += 2
			}
		case booleanFastUninterpretedEUFRelation:
			relationCount++
		default:
			allCompactIntegerCongruence = false
		}
	}
	if allCompactIntegerCongruence && differenceCount != 0 && relationCount != 0 {
		system := smt.CompactIntegerEUFSystem{
			DifferenceCount: differenceCount,
			RelationCount:   relationCount,
		}
		if differenceCount > len(system.Differences) {
			system.OverflowDifferences = make([]smt.IntegerDifferenceConstraint, differenceCount)
		}
		if relationCount > len(system.Relations) {
			system.OverflowRelations = make([]smt.UninterpretedEUFRelation, relationCount)
		}
		differenceIndex, relationIndex := 0, 0
		for _, value := range values {
			if value.fast.kind == booleanFastIntegerDifference {
				if system.OverflowDifferences != nil {
					system.OverflowDifferences[differenceIndex] = value.fast.integerDifference
				} else {
					system.Differences[differenceIndex] = value.fast.integerDifference
				}
				differenceIndex++
			} else if value.fast.kind == booleanFastIntegerSymbolEquality {
				for _, constraint := range [...]smt.IntegerDifferenceConstraint{
					{
						PositiveID:  value.fast.integerSymbolLeft,
						NegativeID:  value.fast.integerSymbolRight,
						HasPositive: true, HasNegative: true,
					},
					{
						PositiveID:  value.fast.integerSymbolRight,
						NegativeID:  value.fast.integerSymbolLeft,
						HasPositive: true, HasNegative: true,
					},
				} {
					if system.OverflowDifferences != nil {
						system.OverflowDifferences[differenceIndex] = constraint
					} else {
						system.Differences[differenceIndex] = constraint
					}
					differenceIndex++
				}
			} else {
				if system.OverflowRelations != nil {
					system.OverflowRelations[relationIndex] = value.fast.uninterpretedEUFRelation
				} else {
					system.Relations[relationIndex] = value.fast.uninterpretedEUFRelation
				}
				relationIndex++
			}
		}
		return boolExprValue{contextID: context, term: system}
	}
	allUninterpretedEUF := len(values) > 0
	for _, value := range values {
		allUninterpretedEUF = allUninterpretedEUF && value.fast.kind == booleanFastUninterpretedEUFRelation
	}
	if allUninterpretedEUF {
		conjunction := smt.UninterpretedEUFConjunction{Count: len(values)}
		if len(values) > len(conjunction.Inline) {
			conjunction.Overflow = make([]smt.UninterpretedEUFRelation, len(values))
		}
		for index, value := range values {
			if conjunction.Overflow != nil {
				conjunction.Overflow[index] = value.fast.uninterpretedEUFRelation
			} else {
				conjunction.Inline[index] = value.fast.uninterpretedEUFRelation
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	equalityCount, divModCount, allDivMod := 0, 0, len(values) > 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastIntegerLinearEquality:
			equalityCount++
		case booleanFastIntegerDivModRelation:
			divModCount++
		default:
			allDivMod = false
		}
	}
	if allDivMod && divModCount > 0 && equalityCount <= 4 && divModCount <= 4 {
		system := smt.IntegerDivModSystem{EqualityCount: equalityCount, RelationCount: divModCount}
		equalityIndex, relationIndex := 0, 0
		for _, value := range values {
			if value.fast.kind == booleanFastIntegerLinearEquality {
				system.Equalities[equalityIndex] = value.fast.integerLinearEquality
				equalityIndex++
			} else {
				system.Relations[relationIndex] = value.fast.integerDivModRelation
				relationIndex++
			}
		}
		return boolExprValue{contextID: context, fast: booleanFast{kind: booleanFastIntegerDivModSystem, integerDivModSystem: system}}
	}
	if len(values) == 3 {
		var differences [2]smt.IntegerDifferenceConstraint
		differenceCount := 0
		var read smt.ArrayStoreReadValueRelation
		readFound := false
		for _, value := range values {
			if value.fast.kind == booleanFastIntegerDifference && differenceCount < len(differences) {
				differences[differenceCount] = value.fast.integerDifference
				differenceCount++
			} else if value.fast.kind == booleanFastArrayStoreReadValue && !readFound {
				read, readFound = value.fast.arrayStoreReadValue, true
			}
		}
		if differenceCount == 2 && readFound {
			return boolExprValue{contextID: context, term: smt.ArrayIntegerEqualityExchange{First: differences[0], Second: differences[1], Read: read}}
		}
	}
	if len(values) == 2 {
		var symbolEquality booleanFast
		var storeRead smt.ArrayStoreReadValueRelation
		symbolReadMatched := false
		if values[0].fast.kind == booleanFastIntegerSymbolEquality && values[1].fast.kind == booleanFastArrayStoreReadValue {
			symbolEquality, storeRead, symbolReadMatched = values[0].fast, values[1].fast.arrayStoreReadValue, true
		}
		if values[1].fast.kind == booleanFastIntegerSymbolEquality && values[0].fast.kind == booleanFastArrayStoreReadValue {
			symbolEquality, storeRead, symbolReadMatched = values[1].fast, values[0].fast.arrayStoreReadValue, true
		}
		if symbolReadMatched && !symbolEquality.integerSymbolNegated {
			return boolExprValue{contextID: context, term: smt.ArrayIntegerSymbolEqualityExchange{LeftID: symbolEquality.integerSymbolLeft, RightID: symbolEquality.integerSymbolRight, Read: storeRead}}
		}
		if values[0].fast.kind == booleanFastBitVectorEUFRelation && values[1].fast.kind == booleanFastBitVectorArrayStoreReadValue {
			return boolExprValue{contextID: context, term: smt.BitVectorArrayEqualityExchange{Equality: values[0].fast.bitVectorEUFRelation, Read: values[1].fast.bitVectorArrayStoreReadValue}}
		}
		if values[1].fast.kind == booleanFastBitVectorEUFRelation && values[0].fast.kind == booleanFastBitVectorArrayStoreReadValue {
			return boolExprValue{contextID: context, term: smt.BitVectorArrayEqualityExchange{Equality: values[1].fast.bitVectorEUFRelation, Read: values[0].fast.bitVectorArrayStoreReadValue}}
		}
		var equality smt.ArrayEqualityRelation
		var read smt.ArrayReadRelation
		matched := false
		if values[0].fast.kind == booleanFastArrayEquality && values[1].fast.kind == booleanFastArrayReadEquality {
			equality, read = values[0].fast.arrayEquality, values[1].fast.arrayReadEquality
			matched = true
		}
		if values[1].fast.kind == booleanFastArrayEquality && values[0].fast.kind == booleanFastArrayReadEquality {
			equality, read = values[1].fast.arrayEquality, values[0].fast.arrayReadEquality
			matched = true
		}
		if matched {
			return boolExprValue{contextID: context, term: smt.ArrayCongruenceConjunction{Equality: equality, Read: read}}
		}
		if values[0].fast.kind == booleanFastArrayEquality && values[1].fast.kind == booleanFastArrayReadValue {
			return boolExprValue{contextID: context, term: smt.ArrayExtensionalReadConjunction{Equality: values[0].fast.arrayEquality, Read: values[1].fast.arrayReadValue}}
		}
		if values[1].fast.kind == booleanFastArrayEquality && values[0].fast.kind == booleanFastArrayReadValue {
			return boolExprValue{contextID: context, term: smt.ArrayExtensionalReadConjunction{Equality: values[1].fast.arrayEquality, Read: values[0].fast.arrayReadValue}}
		}
		if values[0].fast.kind == booleanFastArrayStoreEquality && values[1].fast.kind == booleanFastArrayReadEquality {
			return boolExprValue{contextID: context, term: smt.ArrayStoreBridgeReadConjunction{Store: values[0].fast.arrayStoreEquality, Read: values[1].fast.arrayReadEquality}}
		}
		if values[1].fast.kind == booleanFastArrayStoreEquality && values[0].fast.kind == booleanFastArrayReadEquality {
			return boolExprValue{contextID: context, term: smt.ArrayStoreBridgeReadConjunction{Store: values[1].fast.arrayStoreEquality, Read: values[0].fast.arrayReadEquality}}
		}
		if values[0].fast.kind == booleanFastArrayConstantEquality && values[1].fast.kind == booleanFastArrayReadValue {
			return boolExprValue{contextID: context, term: smt.ArrayConstantReadConjunction{Equality: values[0].fast.arrayConstantEquality, Read: values[1].fast.arrayReadValue}}
		}
		if values[1].fast.kind == booleanFastArrayConstantEquality && values[0].fast.kind == booleanFastArrayReadValue {
			return boolExprValue{contextID: context, term: smt.ArrayConstantReadConjunction{Equality: values[1].fast.arrayConstantEquality, Read: values[0].fast.arrayReadValue}}
		}
	}
	bitVectorCount, integerCount, mixed := 0, 0, len(values) > 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastBitVectorRelation:
			bitVectorCount++
		case booleanFastBitVectorIntegerRelation:
			integerCount++
		default:
			mixed = false
		}
	}
	if mixed && bitVectorCount > 0 && integerCount > 0 && bitVectorCount <= 4 && integerCount <= 4 {
		conjunction := smt.BitVectorMixedConjunction{BitVectorCount: bitVectorCount, IntegerCount: integerCount}
		bitVectorIndex, integerIndex := 0, 0
		for _, value := range values {
			if value.fast.kind == booleanFastBitVectorRelation {
				conjunction.BitVectors[bitVectorIndex] = value.fast.bitVectorRelation
				bitVectorIndex++
			} else {
				conjunction.Integers[integerIndex] = value.fast.bitVectorIntegerRelation
				integerIndex++
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	allIntegerDifferences := len(values) > 0
	for _, value := range values {
		allIntegerDifferences = allIntegerDifferences && value.fast.kind == booleanFastIntegerDifference
	}
	if allIntegerDifferences {
		system := smt.IntegerDifferenceSystem{Count: len(values)}
		if len(values) > len(system.Inline) {
			system.Overflow = make([]smt.IntegerDifferenceConstraint, len(values))
		}
		for index, value := range values {
			constraint := value.fast.integerDifference
			if system.Overflow != nil {
				system.Overflow[index] = constraint
			} else {
				system.Inline[index] = constraint
			}
		}
		return boolExprValue{contextID: context, term: system}
	}
	allBitVectorRelations := len(values) > 0
	for _, value := range values {
		allBitVectorRelations = allBitVectorRelations && value.fast.kind == booleanFastBitVectorRelation
	}
	if allBitVectorRelations {
		conjunction := smt.BitVectorConjunction{Count: len(values)}
		if len(values) > len(conjunction.Inline) {
			conjunction.Overflow = make([]smt.BitVectorRelation, len(values))
		}
		for index, value := range values {
			if conjunction.Overflow != nil {
				conjunction.Overflow[index] = value.fast.bitVectorRelation
			} else {
				conjunction.Inline[index] = value.fast.bitVectorRelation
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	allBitVectorEUFRelations := len(values) > 0
	for _, value := range values {
		allBitVectorEUFRelations = allBitVectorEUFRelations && value.fast.kind == booleanFastBitVectorEUFRelation
	}
	if allBitVectorEUFRelations {
		conjunction := smt.BitVectorEUFConjunction{Count: len(values)}
		if len(values) > len(conjunction.Inline) {
			conjunction.Overflow = make([]smt.BitVectorEUFRelation, len(values))
		}
		for index, value := range values {
			if conjunction.Overflow != nil {
				conjunction.Overflow[index] = value.fast.bitVectorEUFRelation
			} else {
				conjunction.Inline[index] = value.fast.bitVectorEUFRelation
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	allCompactRealTheory := len(values) > 0
	symbolEqualityCount := 0
	comparisonCount := 0
	binaryComparisonCount := 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastRealSymbolEquality:
			symbolEqualityCount++
		case booleanFastRealUnaryComparison:
			comparisonCount++
		case booleanFastRealBinaryComparison:
			binaryComparisonCount++
		default:
			allCompactRealTheory = false
		}
	}
	if allCompactRealTheory && symbolEqualityCount != 0 && comparisonCount+binaryComparisonCount != 0 {
		conjunction := smt.TheoryConjunction{SymbolEqualityCount: symbolEqualityCount, UnaryComparisonCount: comparisonCount, BinaryComparisonCount: binaryComparisonCount}
		if symbolEqualityCount > len(conjunction.SymbolEqualities) {
			conjunction.OverflowSymbolEqualities = make([]smt.RealSymbolEquality, symbolEqualityCount)
		}
		if comparisonCount > len(conjunction.UnaryComparisons) {
			conjunction.OverflowUnaryComparisons = make([]smt.RealUnaryComparison, comparisonCount)
		}
		if binaryComparisonCount > len(conjunction.BinaryComparisons) {
			conjunction.OverflowBinaryComparisons = make([]smt.RealBinaryComparison, binaryComparisonCount)
		}
		equality, comparison, binaryComparison := 0, 0, 0
		for _, value := range values {
			switch value.fast.kind {
			case booleanFastRealSymbolEquality:
				if conjunction.OverflowSymbolEqualities != nil {
					conjunction.OverflowSymbolEqualities[equality] = value.fast.symbolEquality
				} else {
					conjunction.SymbolEqualities[equality] = value.fast.symbolEquality
				}
				equality++
			case booleanFastRealUnaryComparison:
				if conjunction.OverflowUnaryComparisons != nil {
					conjunction.OverflowUnaryComparisons[comparison] = value.fast.unaryComparison
				} else {
					conjunction.UnaryComparisons[comparison] = value.fast.unaryComparison
				}
				comparison++
			case booleanFastRealBinaryComparison:
				if conjunction.OverflowBinaryComparisons != nil {
					conjunction.OverflowBinaryComparisons[binaryComparison] = value.fast.binaryComparison
				} else {
					conjunction.BinaryComparisons[binaryComparison] = value.fast.binaryComparison
				}
				binaryComparison++
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	allCompactIntegerTheory := len(values) > 0
	integerEqualityCount, integerUnaryCount, integerBinaryCount, integerTernaryCount := 0, 0, 0, 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastIntegerSymbolEquality:
			integerEqualityCount++
		case booleanFastIntegerUnaryComparison:
			integerUnaryCount++
		case booleanFastIntegerBinaryComparison:
			integerBinaryCount++
		case booleanFastIntegerTernaryComparison:
			integerTernaryCount++
		default:
			allCompactIntegerTheory = false
		}
	}
	if allCompactIntegerTheory && integerEqualityCount != 0 &&
		integerUnaryCount+integerBinaryCount+integerTernaryCount != 0 {
		system := smt.CompactIntegerEUFSystem{
			EqualityCount:          integerEqualityCount,
			UnaryComparisonCount:   integerUnaryCount,
			BinaryComparisonCount:  integerBinaryCount,
			TernaryComparisonCount: integerTernaryCount,
		}
		if integerEqualityCount > len(system.EqualityLeft) {
			system.OverflowEqualityLeft = make([]int, integerEqualityCount)
			system.OverflowEqualityRight = make([]int, integerEqualityCount)
		}
		if integerUnaryCount > len(system.UnaryComparisons) {
			system.OverflowUnaryComparisons = make([]smt.IntegerUnaryComparison, integerUnaryCount)
		}
		if integerBinaryCount > len(system.BinaryComparisons) {
			system.OverflowBinaryComparisons = make([]smt.IntegerBinaryComparison, integerBinaryCount)
		}
		if integerTernaryCount > len(system.TernaryComparisons) {
			system.OverflowTernaryComparisons = make([]smt.IntegerTernaryComparison, integerTernaryCount)
		}
		equality, unary, binary, ternary := 0, 0, 0, 0
		for _, value := range values {
			switch value.fast.kind {
			case booleanFastIntegerSymbolEquality:
				if value.fast.integerSymbolNegated {
					allCompactIntegerTheory = false
					break
				}
				if system.OverflowEqualityLeft != nil {
					system.OverflowEqualityLeft[equality] = value.fast.integerSymbolLeft
					system.OverflowEqualityRight[equality] = value.fast.integerSymbolRight
				} else {
					system.EqualityLeft[equality] = value.fast.integerSymbolLeft
					system.EqualityRight[equality] = value.fast.integerSymbolRight
				}
				equality++
			case booleanFastIntegerUnaryComparison:
				if system.OverflowUnaryComparisons != nil {
					system.OverflowUnaryComparisons[unary] = value.fast.integerUnaryComparison
				} else {
					system.UnaryComparisons[unary] = value.fast.integerUnaryComparison
				}
				unary++
			case booleanFastIntegerBinaryComparison:
				if system.OverflowBinaryComparisons != nil {
					system.OverflowBinaryComparisons[binary] = value.fast.integerBinaryComparison
				} else {
					system.BinaryComparisons[binary] = value.fast.integerBinaryComparison
				}
				binary++
			case booleanFastIntegerTernaryComparison:
				if system.OverflowTernaryComparisons != nil {
					system.OverflowTernaryComparisons[ternary] = value.fast.integerTernaryComparison
				} else {
					system.TernaryComparisons[ternary] = value.fast.integerTernaryComparison
				}
				ternary++
			}
		}
		if allCompactIntegerTheory {
			return boolExprValue{contextID: context, term: system}
		}
	}
	allRealConstraints := len(values) > 0
	for _, value := range values {
		allRealConstraints = allRealConstraints && value.fast.kind == booleanFastRealConstraint
	}
	if allRealConstraints {
		system := smt.LinearRealSystem{Count: len(values)}
		if len(values) > len(system.Inline) {
			system.Overflow = make([]smt.LinearRealConstraint, len(values))
		}
		for index, value := range values {
			if system.Overflow != nil {
				system.Overflow[index] = value.fast.real
			} else {
				system.Inline[index] = value.fast.real
			}
		}
		return boolExprValue{contextID: context, term: system}
	}
	allAtoms := len(values) > 0
	for _, value := range values {
		allAtoms = allAtoms && value.fast.kind == booleanFastAtom
	}
	if allAtoms {
		conjunction := smt.BooleanConjunction{Count: len(values)}
		if len(values) > len(conjunction.InlineTerms) {
			conjunction.OverflowTerms = make([]smt.Term[smt.BoolSort], len(values))
			conjunction.OverflowNegated = make([]bool, len(values))
		}
		for index, value := range values {
			if conjunction.OverflowTerms != nil {
				conjunction.OverflowTerms[index] = value.term
				conjunction.OverflowNegated[index] = value.fast.negated
			} else {
				conjunction.InlineTerms[index] = value.term
				conjunction.InlineNegated[index] = value.fast.negated
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	allTheoryAtoms := len(values) > 0
	atomCount := 0
	realCount := 0
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastAtom:
			atomCount++
		case booleanFastRealConstraint:
			realCount++
		default:
			allTheoryAtoms = false
		}
	}
	if allTheoryAtoms && atomCount != 0 && realCount != 0 {
		conjunction := smt.TheoryConjunction{AtomCount: atomCount, RealCount: realCount}
		if atomCount > len(conjunction.Atoms) {
			conjunction.OverflowAtoms = make([]smt.Term[smt.BoolSort], atomCount)
			conjunction.OverflowNegated = make([]bool, atomCount)
		}
		if realCount > len(conjunction.Reals) {
			conjunction.OverflowReals = make([]smt.LinearRealConstraint, realCount)
		}
		atom := 0
		real := 0
		for _, value := range values {
			if value.fast.kind == booleanFastAtom {
				if conjunction.OverflowAtoms != nil {
					conjunction.OverflowAtoms[atom] = value.term
					conjunction.OverflowNegated[atom] = value.fast.negated
				} else {
					conjunction.Atoms[atom] = value.term
					conjunction.AtomNegated[atom] = value.fast.negated
				}
				atom++
			} else {
				if conjunction.OverflowReals != nil {
					conjunction.OverflowReals[real] = value.fast.real
				} else {
					conjunction.Reals[real] = value.fast.real
				}
				real++
			}
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	if len(values) <= len((smt.BooleanConjunction{}).InlineTerms) {
		conjunction := smt.BooleanConjunction{Count: len(values)}
		for index, value := range values {
			conjunction.InlineTerms[index] = materializeBoolean(value.term, value.fast)
		}
		return boolExprValue{contextID: context, term: conjunction}
	}
	total := 0
	for _, value := range values {
		if value.fast.kind != booleanFastClause {
			_, terms := booleanTerms(values)
			return boolExprValue{contextID: context, term: smt.And{Values: terms}}
		}
		total += int(value.fast.count)
	}
	literals := make([]int, 0, total)
	ends := make([]int, 0, len(values))
	for _, value := range values {
		literals = append(literals, fastLiterals(value.fast)...)
		ends = append(ends, len(literals))
	}
	return boolExprValue{contextID: context, term: smt.BooleanCNF{Literals: literals, ClauseEnds: ends}}
}

func combineCompactStringBooleanValues(values []BoolExpr, conjunction bool) (smt.CompactStringBooleanFormula, bool) {
	if len(values) == 0 {
		return smt.CompactStringBooleanFormula{}, false
	}
	result, ok := compactStringBooleanValue(values[0])
	if !ok {
		return smt.CompactStringBooleanFormula{}, false
	}
	for _, value := range values[1:] {
		next, nextOK := compactStringBooleanValue(value)
		if !nextOK {
			return smt.CompactStringBooleanFormula{}, false
		}
		if conjunction {
			result, ok = smt.CompactStringBooleanAndFormula(result, next)
		} else {
			result, ok = smt.CompactStringBooleanOrFormula(result, next)
		}
		if !ok {
			return smt.CompactStringBooleanFormula{}, false
		}
	}
	return result, true
}

func compactStringBooleanValue(value BoolExpr) (smt.CompactStringBooleanFormula, bool) {
	if value.fast.kind == booleanFastStringBooleanFormula {
		return value.fast.stringBooleanFormula, true
	}
	if value.fast.kind == booleanFastNone {
		if constant, ok := value.term.(smt.Bool); ok {
			return smt.CompactStringBooleanConstant(constant.Value), true
		}
	}
	return smt.CompactStringBooleanFormula{}, false
}

func compactBooleanCNF(values []BoolExpr) (smt.BooleanInlineCNF, bool) {
	var cnf smt.BooleanInlineCNF
	if len(values) == 0 || len(values) > len(cnf.ClauseEnds) {
		return cnf, false
	}
	for _, value := range values {
		switch value.fast.kind {
		case booleanFastLiteral:
			if cnf.LiteralCount == len(cnf.Literals) {
				return smt.BooleanInlineCNF{}, false
			}
			if literal := value.fast.inline[0]; literal < -64 || literal > 64 || literal == 0 {
				return smt.BooleanInlineCNF{}, false
			}
			cnf.Literals[cnf.LiteralCount] = value.fast.inline[0]
			cnf.LiteralCount++
		case booleanFastClause:
			literals := fastLiterals(value.fast)
			if len(literals) == 0 || cnf.LiteralCount+len(literals) > len(cnf.Literals) {
				return smt.BooleanInlineCNF{}, false
			}
			for _, literal := range literals {
				if literal < -64 || literal > 64 || literal == 0 {
					return smt.BooleanInlineCNF{}, false
				}
			}
			copy(cnf.Literals[cnf.LiteralCount:], literals)
			cnf.LiteralCount += len(literals)
		default:
			return smt.BooleanInlineCNF{}, false
		}
		cnf.ClauseEnds[cnf.ClauseCount] = cnf.LiteralCount
		cnf.ClauseCount++
	}
	return cnf, true
}

func booleanContext(values []BoolExpr) int {
	if len(values) == 0 {
		return 0
	}
	context := values[0].contextID
	for _, value := range values[1:] {
		if value.contextID != context {
			panic("gosmt: erased expression context mismatch")
		}
	}
	return context
}

func fastLiterals(fast booleanFast) []int {
	if fast.overflow != nil {
		return fast.overflow
	}
	return fast.inline[:fast.count]
}

func materializeBoolean(term smt.Term[smt.BoolSort], fast booleanFast) smt.Term[smt.BoolSort] {
	switch fast.kind {
	case booleanFastLiteral:
		literal := fast.inline[0]
		if literal > 0 {
			return smt.BooleanVariable{ID: literal - 1}
		}
		return smt.NegatedBooleanVariable{ID: -literal - 1}
	case booleanFastClause:
		return smt.BooleanClause{Literals: append([]int(nil), fastLiterals(fast)...)}
	case booleanFastRealConstraint:
		return fast.real
	case booleanFastRealSymbolEquality:
		return fast.symbolEquality
	case booleanFastRealUnaryComparison:
		return fast.unaryComparison
	case booleanFastRealBinaryComparison:
		return fast.binaryComparison
	case booleanFastIntegerUnaryComparison:
		return fast.integerUnaryComparison
	case booleanFastIntegerBinaryComparison:
		return fast.integerBinaryComparison
	case booleanFastIntegerTernaryComparison:
		return fast.integerTernaryComparison
	case booleanFastBitVectorRelation:
		return fast.bitVectorRelation
	case booleanFastBitVectorEUFRelation:
		return fast.bitVectorEUFRelation
	case booleanFastIntegerDifference:
		return fast.integerDifference
	case booleanFastIntegerSymbolEquality:
		equality := smt.Term[smt.BoolSort](smt.Equal{Left: smt.IntegerVariable(fast.integerSymbolLeft), Right: smt.IntegerVariable(fast.integerSymbolRight)})
		if fast.integerSymbolNegated {
			return smt.Not{Value: equality}
		}
		return equality
	case booleanFastBitVectorIntegerRelation:
		return fast.bitVectorIntegerRelation
	case booleanFastArrayEquality:
		return fast.arrayEquality
	case booleanFastArrayReadEquality:
		return fast.arrayReadEquality
	case booleanFastArrayStoreEquality:
		return fast.arrayStoreEquality
	case booleanFastArrayConstantEquality:
		return fast.arrayConstantEquality
	case booleanFastArrayReadValue:
		return fast.arrayReadValue
	case booleanFastArrayStoreReadValue:
		return fast.arrayStoreReadValue
	case booleanFastBitVectorArrayStoreReadValue:
		return fast.bitVectorArrayStoreReadValue
	case booleanFastBitVectorArrayEquality:
		return fast.bitVectorArrayEquality
	case booleanFastIntegerLinearEquality:
		return fast.integerLinearEquality
	case booleanFastIntegerLinearDisequality:
		return smt.IntegerLinearDisequality{Equality: fast.integerLinearEquality}
	case booleanFastIntegerLinearChoice:
		return fast.integerLinearChoice
	case booleanFastIntegerDivModRelation:
		return fast.integerDivModRelation
	case booleanFastIntegerDivModSystem:
		return fast.integerDivModSystem
	case booleanFastUninterpretedEUFRelation:
		return fast.uninterpretedEUFRelation
	case booleanFastStringRelation:
		var system smt.CompactStringSystem
		system = smt.AppendCompactStringRelation(system, fast.stringRelation)
		return smt.CompactStringAssertions(system)
	case booleanFastStringBooleanFormula:
		return fast.stringBooleanFormula
	case booleanFastStringWordEquation:
		return fast.stringWordEquation
	case booleanFastStringIndexedEquality:
		return fast.stringIndexedEquality
	case booleanFastStringReplaceEquality:
		return fast.stringReplaceEquality
	case booleanFastGroundIndexedStringFormula:
		return fast.groundIndexedStringFormula
	case booleanFastStringIndexOfEquality:
		return fast.stringIndexOfEquality
	case booleanFastGroundStringEvaluationFormula:
		return fast.groundStringEvaluation
	case booleanFastAtom:
		if fast.negated {
			return smt.Not{Value: term}
		}
		return term
	default:
		return term
	}
}

func fastEqInteger(left, right IntExpr) BoolExpr {
	if left.contextID != right.contextID {
		panic("gosmt: erased integer expression context mismatch")
	}
	if left.fast.eufValid || right.fast.eufValid {
		if leftCompact, leftOK := compactIntegerEUFTerm(left); leftOK {
			if rightCompact, rightOK := compactIntegerEUFTerm(right); rightOK {
				return boolExprValue{contextID: left.contextID, fast: booleanFast{
					kind: booleanFastUninterpretedEUFRelation,
					uninterpretedEUFRelation: smt.UninterpretedEUFRelation{
						Left: leftCompact, Right: rightCompact,
					},
				}}
			}
		}
	}
	if left.fast.kind == integerFastStringLength && right.fast.kind == integerFastStringLength {
		return fastBooleanAtom(left.contextID, smt.CompactStringLengthRelation{
			Left: left.fast.string, Right: right.fast.string,
		})
	}
	indexOf, expected := left, right
	if indexOf.fast.kind != integerFastStringIndexOfSymbols {
		indexOf, expected = right, left
	}
	if indexOf.fast.kind == integerFastStringIndexOfSymbols {
		relation := smt.CompactStringIndexOfEquality{
			TextID: indexOf.fast.symbolID, TextName: indexOf.fast.name,
			NeedleID: indexOf.fast.string.ID, NeedleName: indexOf.fast.string.Name,
			Offset: int64(indexOf.fast.width), OffsetID: indexOf.fast.width,
			OffsetSymbol: indexOf.fast.signed,
		}
		if resultID, resultName, ok := directIntegerExprSymbol(expected); ok {
			relation.ResultID, relation.ResultName, relation.ResultSymbol = resultID, resultName, true
			return boolExprValue{contextID: left.contextID, fast: booleanFast{
				kind:                  booleanFastStringIndexOfEquality,
				stringIndexOfEquality: relation,
			}}
		}
		if value, ok := smt.ExactIntegerConstant(materializeInteger(expected.term, expected.fast)); ok {
			if result, fits := value.Int64(); fits {
				relation.Result = result
				return boolExprValue{contextID: left.contextID, fast: booleanFast{
					kind: booleanFastStringIndexOfEquality, stringIndexOfEquality: relation,
				}}
			}
		}
	}
	if left.fast.kind == integerFastNone && right.fast.kind == integerFastNone {
		leftValue, leftOK := smt.ExactIntegerConstant(left.term)
		rightValue, rightOK := smt.ExactIntegerConstant(right.term)
		if leftOK && rightOK {
			return boolExprValue{contextID: left.contextID, term: smt.Bool{Value: smt.CompareIntegerValue(leftValue, rightValue) == 0}}
		}
	}
	length, constant := left, right
	if length.fast.kind != integerFastStringLength {
		length, constant = right, left
	}
	if length.fast.kind == integerFastStringLength && constant.fast.kind == integerFastNone {
		if value, ok := smt.ExactIntegerConstant(constant.term); ok {
			if integer, fits := value.Int64(); fits {
				relation := smt.CompactStringRelation{Kind: smt.CompactStringLengthEqual, Left: length.fast.string, Integer: integer}
				return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastStringRelation, stringRelation: relation}}
			}
		}
	}
	if relation, ok := compactFastBitVectorIntegerEquality(left, right); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastBitVectorIntegerRelation, bitVectorIntegerRelation: relation}}
	}
	leftTerm, rightTerm := materializeInteger(left.term, left.fast), materializeInteger(right.term, right.fast)
	if first, firstOK := smt.ExactIntegerConstant(leftTerm); firstOK {
		if second, secondOK := smt.ExactIntegerConstant(rightTerm); secondOK {
			return boolExprValue{contextID: left.contextID, term: smt.Bool{Value: smt.CompareIntegerValue(first, second) == 0}}
		}
	}
	if leftID, leftOK := smt.IntegerVariableID(leftTerm); leftOK {
		if rightID, rightOK := smt.IntegerVariableID(rightTerm); rightOK {
			return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastIntegerSymbolEquality, integerSymbolLeft: leftID, integerSymbolRight: rightID}}
		}
	}
	if relation, ok := smt.CompactBitVectorIntegerEquality(leftTerm, rightTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastBitVectorIntegerRelation, bitVectorIntegerRelation: relation}}
	}
	if relation, ok := smt.CompactIntegerArrayReadEquality(leftTerm, rightTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastArrayReadEquality, arrayReadEquality: relation}}
	}
	if relation, ok := smt.CompactIntegerArrayReadValueEquality(leftTerm, rightTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastArrayReadValue, arrayReadValue: relation}}
	}
	if relation, ok := smt.CompactIntegerArrayStoreReadValueEquality(leftTerm, rightTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastArrayStoreReadValue, arrayStoreReadValue: relation}}
	}
	if relation, ok := smt.CompactIntegerDivModEquality(leftTerm, rightTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastIntegerDivModRelation, integerDivModRelation: relation}}
	}
	if relation, ok := smt.CompactIntegerDivModEquality(rightTerm, leftTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastIntegerDivModRelation, integerDivModRelation: relation}}
	}
	if relation, ok := smt.CompactIntegerLinearEquality(leftTerm, rightTerm); ok {
		return boolExprValue{contextID: left.contextID, fast: booleanFast{kind: booleanFastIntegerLinearEquality, integerLinearEquality: relation}}
	}
	return fastBooleanAtom(left.contextID, smt.Equal{Left: leftTerm, Right: rightTerm})
}

func fastBitVectorToInteger(contextID int, term smt.Term[smt.BitVecSort], fast bitVectorFast, signed bool) IntExpr {
	if term == nil && fast.kind == bitVectorFastSymbol {
		return intExprValue{contextID: contextID, fast: integerFast{kind: integerFastBitVectorConversion, width: fast.width, symbolID: fast.id, name: fast.name, signed: signed}}
	}
	value := materializeBitVector(term, fast)
	if signed {
		return intExprValue{contextID: contextID, term: smt.BitVecToInt(value)}
	}
	return intExprValue{contextID: contextID, term: smt.BitVecToNat(value)}
}

func materializeInteger(term smt.Term[smt.IntSort], fast integerFast) smt.Term[smt.IntSort] {
	if term != nil {
		return term
	}
	if fast.eufValid {
		if fast.eufArity == 3 {
			function := smt.DeclareIntTernaryFunction(fast.functionID, "")
			return smt.ApplySortedTernary(
				function,
				smt.IntegerVariable(fast.argumentID),
				smt.IntegerVariable(fast.secondArgumentID),
				smt.IntegerVariable(fast.thirdArgumentID),
			)
		}
		if fast.eufArity == 2 {
			function := smt.DeclareIntBinaryFunction(fast.functionID, "")
			return smt.ApplySortedBinary(
				function,
				smt.IntegerVariable(fast.argumentID),
				smt.IntegerVariable(fast.secondArgumentID),
			)
		}
		function := smt.DeclareIntUnaryFunction(fast.functionID, "")
		return smt.ApplySortedUnary(function, smt.IntegerVariable(fast.argumentID))
	}
	if fast.kind == integerFastBitVectorConversion {
		value := smt.BitVecConst(fast.width, fast.symbolID, fast.name)
		if fast.signed {
			return smt.BitVecToInt(value)
		}
		return smt.BitVecToNat(value)
	}
	if fast.kind == integerFastStringLength {
		return smt.StringLength(materializeCompactString(fast.string))
	}
	if fast.kind == integerFastStringIndexOfSymbols {
		offset := smt.Term[smt.IntSort](smt.Integer{Value: int64(fast.width)})
		if fast.signed {
			offset = smt.IntSymbol{ID: fast.width}
		}
		return smt.StringIndexOf(
			smt.StringConst(fast.symbolID, fast.name),
			materializeCompactString(fast.string),
			offset,
		)
	}
	panic("gosmt: invalid erased integer expression")
}

func fastIntegerFunction(context, id int, name string) IntFunc {
	return intFuncValue{
		contextID: context,
		fast:      integerFunctionFast{valid: true, id: id, name: name},
	}
}

func applyIntegerFunction(function IntFunc, argument IntExpr) IntExpr {
	if function.contextID != argument.contextID {
		panic("gosmt: erased integer function context mismatch")
	}
	if function.fast.valid {
		if argumentID, _, ok := directIntegerExprSymbol(argument); ok {
			return intExprValue{contextID: function.contextID, fast: integerFast{
				eufValid: true, eufArity: 1, functionID: function.fast.id,
				argumentID: argumentID,
			}}
		}
	}
	core := function.function
	if core == nil {
		core = smt.DeclareIntUnaryFunction(function.fast.id, function.fast.name)
	}
	return intExprValue{
		contextID: function.contextID,
		term:      smt.ApplySortedUnary(core, materializeInteger(argument.term, argument.fast)),
	}
}

func fastIntegerPredicate(context, id int, name string) IntPredicate {
	return intPredicateValue{
		contextID: context,
		fast:      integerPredicateFast{valid: true, id: id, name: name},
	}
}

func applyIntegerPredicate(predicate IntPredicate, argument IntExpr) BoolExpr {
	if predicate.contextID != argument.contextID {
		panic("gosmt: erased integer predicate context mismatch")
	}
	if predicate.fast.valid {
		if argumentID, _, ok := directIntegerExprSymbol(argument); ok {
			relation := smt.UninterpretedEUFRelation{
				Left: smt.UninterpretedEUFTerm{
					Kind: 2, SortID: -3, FunctionID: predicate.fast.id,
					FirstSortID: -2, FirstID: argumentID,
				},
				Right: smt.UninterpretedEUFTerm{
					Kind: 4, SortID: -3, Constant: "true",
				},
			}
			return boolExprValue{contextID: predicate.contextID, fast: booleanFast{
				kind:                     booleanFastUninterpretedEUFRelation,
				uninterpretedEUFRelation: relation,
			}}
		}
	}
	core := predicate.function
	if core == nil {
		core = smt.DeclareIntPredicate(predicate.fast.id, predicate.fast.name)
	}
	return boolExprValue{
		contextID: predicate.contextID,
		term: smt.ApplySortedUnary(
			core, materializeInteger(argument.term, argument.fast),
		),
	}
}

func fastIntegerBinaryFunction(context, id int, name string) IntBinaryFunc {
	return intBinaryFuncValue{
		contextID: context,
		fast:      integerBinaryFunctionFast{valid: true, id: id, name: name},
	}
}

func applyIntegerBinaryFunction(function IntBinaryFunc, first, second IntExpr) IntExpr {
	if function.contextID != first.contextID || function.contextID != second.contextID {
		panic("gosmt: erased binary integer function context mismatch")
	}
	firstID, _, firstOK := directIntegerExprSymbol(first)
	secondID, _, secondOK := directIntegerExprSymbol(second)
	if function.fast.valid && firstOK && secondOK {
		return intExprValue{contextID: function.contextID, fast: integerFast{
			eufValid: true, eufArity: 2, functionID: function.fast.id,
			argumentID: firstID, secondArgumentID: secondID,
		}}
	}
	core := function.function
	if core == nil {
		core = smt.DeclareIntBinaryFunction(function.fast.id, function.fast.name)
	}
	return intExprValue{
		contextID: function.contextID,
		term: smt.ApplySortedBinary(
			core,
			materializeInteger(first.term, first.fast),
			materializeInteger(second.term, second.fast),
		),
	}
}

func fastIntegerBinaryPredicate(context, id int, name string) IntBinaryPredicate {
	return intBinaryPredicateValue{
		contextID: context,
		fast:      integerBinaryPredicateFast{valid: true, id: id, name: name},
	}
}

func applyIntegerBinaryPredicate(
	predicate IntBinaryPredicate, first, second IntExpr,
) BoolExpr {
	if predicate.contextID != first.contextID ||
		predicate.contextID != second.contextID {
		panic("gosmt: erased binary integer predicate context mismatch")
	}
	firstID, _, firstOK := directIntegerExprSymbol(first)
	secondID, _, secondOK := directIntegerExprSymbol(second)
	if predicate.fast.valid && firstOK && secondOK {
		relation := smt.UninterpretedEUFRelation{
			Left: smt.UninterpretedEUFTerm{
				Kind: 3, SortID: -3, FunctionID: predicate.fast.id,
				FirstSortID: -2, SecondSortID: -2,
				FirstID: firstID, SecondID: secondID,
			},
			Right: smt.UninterpretedEUFTerm{
				Kind: 4, SortID: -3, Constant: "true",
			},
		}
		return boolExprValue{contextID: predicate.contextID, fast: booleanFast{
			kind:                     booleanFastUninterpretedEUFRelation,
			uninterpretedEUFRelation: relation,
		}}
	}
	core := predicate.function
	if core == nil {
		core = smt.DeclareIntBinaryPredicate(predicate.fast.id, predicate.fast.name)
	}
	return boolExprValue{
		contextID: predicate.contextID,
		term: smt.ApplySortedBinary(
			core,
			materializeInteger(first.term, first.fast),
			materializeInteger(second.term, second.fast),
		),
	}
}

func fastIntegerTernaryFunction(context, id int, name string) IntTernaryFunc {
	return intTernaryFuncValue{
		contextID: context,
		fast:      integerTernaryFunctionFast{valid: true, id: id, name: name},
	}
}

func applyIntegerTernaryFunction(
	function IntTernaryFunc, first, second, third IntExpr,
) IntExpr {
	if function.contextID != first.contextID ||
		function.contextID != second.contextID ||
		function.contextID != third.contextID {
		panic("gosmt: erased ternary integer function context mismatch")
	}
	firstID, _, firstOK := directIntegerExprSymbol(first)
	secondID, _, secondOK := directIntegerExprSymbol(second)
	thirdID, _, thirdOK := directIntegerExprSymbol(third)
	if function.fast.valid && firstOK && secondOK && thirdOK {
		return intExprValue{contextID: function.contextID, fast: integerFast{
			eufValid: true, eufArity: 3, functionID: function.fast.id,
			argumentID: firstID, secondArgumentID: secondID, thirdArgumentID: thirdID,
		}}
	}
	core := function.function
	if core == nil {
		core = smt.DeclareIntTernaryFunction(function.fast.id, function.fast.name)
	}
	return intExprValue{
		contextID: function.contextID,
		term: smt.ApplySortedTernary(
			core,
			materializeInteger(first.term, first.fast),
			materializeInteger(second.term, second.fast),
			materializeInteger(third.term, third.fast),
		),
	}
}

func compactIntegerEUFTerm(value IntExpr) (smt.UninterpretedEUFTerm, bool) {
	if value.fast.eufValid {
		if value.fast.eufArity == 3 {
			return smt.UninterpretedEUFTerm{}, false
		}
		if value.fast.eufArity == 2 {
			return smt.UninterpretedEUFTerm{
				Kind: 3, SortID: -2, FunctionID: value.fast.functionID,
				FirstSortID: -2, SecondSortID: -2,
				FirstID: value.fast.argumentID, SecondID: value.fast.secondArgumentID,
			}, true
		}
		return smt.UninterpretedEUFTerm{
			Kind: 2, SortID: -2, FunctionID: value.fast.functionID,
			FirstSortID: -2, FirstID: value.fast.argumentID,
		}, true
	}
	if id, _, ok := smt.IntegerSymbol(value.term); ok {
		return smt.UninterpretedEUFTerm{Kind: 1, SortID: -2, SymbolID: id}, true
	}
	return smt.UninterpretedEUFTerm{}, false
}

func compactFastBitVectorIntegerEquality(left, right IntExpr) (smt.BitVectorIntegerRelation, bool) {
	conversion, constant, reverse := left, right, false
	if conversion.fast.kind != integerFastBitVectorConversion {
		conversion, constant, reverse = right, left, true
	}
	if conversion.fast.kind != integerFastBitVectorConversion || constant.fast.kind != integerFastNone {
		return smt.BitVectorIntegerRelation{}, false
	}
	value, ok := smt.ExactIntegerConstant(constant.term)
	if !ok {
		return smt.BitVectorIntegerRelation{}, false
	}
	return smt.BitVectorIntegerRelation{SymbolID: conversion.fast.symbolID, Width: conversion.fast.width, Signed: conversion.fast.signed, Constant: value, Reverse: reverse}, true
}

func cachedCheckResult(context int, core smt.Solver) Result {
	return smt.MemoizedContextView(core, &resultViewKey, context, buildCachedCheckResult).(Result)
}

func buildCachedCheckResult(context int, checked smt.CheckResult) any {
	var result Result
	switch checked := checked.(type) {
	case smt.Satisfiable:
		result = Sat{Value: modelValue{contextID: context, core: checked.Value}}
	case smt.Unsatisfiable:
		result = Unsat{Context: contextValue{iD: context}, Proof: checked.Value}
	case smt.Unknown:
		result = Unknown{Context: contextValue{iD: context}, Proof: checked.Context, Reason: checked.Reason}
	}
	return result
}

func booleanTerms(values []BoolExpr) (int, []smt.Term[smt.BoolSort]) {
	if len(values) == 0 {
		return 0, nil
	}
	terms := make([]smt.Term[smt.BoolSort], len(values))
	context := -1
	for index, value := range values {
		item := value
		if context < 0 {
			context = item.contextID
		}
		if context != item.contextID {
			panic("gosmt: erased expression context mismatch")
		}
		terms[index] = materializeBoolean(item.term, item.fast)
	}
	return context, terms
}

func assumptionTerms(context int, values []BoolExpr) []smt.Term[smt.BoolSort] {
	terms := make([]smt.Term[smt.BoolSort], len(values))
	for index, value := range values {
		item := value
		if context != item.contextID {
			panic("gosmt: erased assumption context mismatch")
		}
		terms[index] = materializeBoolean(item.term, item.fast)
	}
	return terms
}

func integerTerms(values []IntExpr) (int, []smt.Term[smt.IntSort]) {
	if len(values) == 0 {
		return 0, nil
	}
	terms := make([]smt.Term[smt.IntSort], len(values))
	context := -1
	for index, value := range values {
		item := value
		if context < 0 {
			context = item.contextID
		}
		if context != item.contextID {
			panic("gosmt: erased integer expression context mismatch")
		}
		terms[index] = materializeInteger(item.term, item.fast)
	}
	return context, terms
}

func realTerms(values []RealExpr) (int, []smt.Term[smt.RealSort]) {
	if len(values) == 0 {
		return 0, nil
	}
	terms := make([]smt.Term[smt.RealSort], len(values))
	context := -1
	for index, value := range values {
		item := value
		if context < 0 {
			context = item.contextID
		}
		if context != item.contextID {
			panic("gosmt: erased real expression context mismatch")
		}
		terms[index] = materializeReal(item.term, item.fast)
	}
	return context, terms
}
