package gosmt

import (
	"fmt"
	"math/big"
	"math/rand"
	"os"
	"os/exec"
	"sort"
	"strings"
	"testing"

	smt "goforge.dev/goplus/std/smt"
	"goforge.dev/goplus/std/smtlib"
)

func TestBooleanResultsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	a := smt.BoolSymbol{ID: 1, Name: "a"}
	b := smt.BoolSymbol{ID: 2, Name: "b"}
	cases := []smt.Term[smt.BoolSort]{
		smt.Bool{Value: true},
		smt.Bool{Value: false},
		smt.And{Values: []smt.Term[smt.BoolSort]{a, smt.Not{Value: a}}},
		smt.Or{Values: []smt.Term[smt.BoolSort]{a, smt.Not{Value: a}}},
		smt.Implies{Left: a, Right: b},
		smt.Iff{Left: a, Right: smt.Not{Value: a}},
		smt.If[smt.BoolSort]{Condition: a, Then: b, Else: smt.Not{Value: b}},
	}
	for index, formula := range cases {
		context := NewContext(91)
		ours := Check(Assert(index+1, NewSolver(context), boolExprValue{contextID: 91, term: formula}))
		oursStatus := "sat"
		if _, unsat := ours.(Unsat); unsat {
			oursStatus = "unsat"
		}
		z3Status := runZ3Boolean(t, z3, formula)
		if oursStatus != z3Status {
			t.Fatalf("case %d: gosmt=%s z3=%s", index, oursStatus, z3Status)
		}
	}
}

func TestBooleanPigeonholeAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	const pigeons, holes = 5, 4
	context := NewContext(94)
	variables := make([][]BoolExpr, pigeons)
	clauses := make([]BoolExpr, 0, 75)
	var script strings.Builder
	script.WriteString("(set-logic QF_UF)\n")
	name := func(pigeon, hole int) string { return fmt.Sprintf("p%d_%d", pigeon, hole) }
	for pigeon := 0; pigeon < pigeons; pigeon++ {
		variables[pigeon] = make([]BoolExpr, holes)
		for hole := 0; hole < holes; hole++ {
			variables[pigeon][hole] = BoolConst(context, name(pigeon, hole), pigeon*holes+hole+1)
			fmt.Fprintf(&script, "(declare-const %s Bool)\n", name(pigeon, hole))
		}
		clauses = append(clauses, Or(variables[pigeon]...))
		script.WriteString("(assert (or")
		for hole := 0; hole < holes; hole++ {
			fmt.Fprintf(&script, " %s", name(pigeon, hole))
		}
		script.WriteString("))\n")
		for left := 0; left < holes; left++ {
			for right := left + 1; right < holes; right++ {
				clauses = append(clauses, Or(Not(variables[pigeon][left]), Not(variables[pigeon][right])))
				fmt.Fprintf(&script, "(assert (or (not %s) (not %s)))\n", name(pigeon, left), name(pigeon, right))
			}
		}
	}
	for hole := 0; hole < holes; hole++ {
		for left := 0; left < pigeons; left++ {
			for right := left + 1; right < pigeons; right++ {
				clauses = append(clauses, Or(Not(variables[left][hole]), Not(variables[right][hole])))
				fmt.Fprintf(&script, "(assert (or (not %s) (not %s)))\n", name(left, hole), name(right, hole))
			}
		}
	}
	if result := Check(Assert(1, NewSolver(context), And(clauses...))); func() bool { _, ok := result.(Unsat); return ok }() == false {
		t.Fatalf("gosmt result=%T", result)
	}
	script.WriteString("(check-sat)\n")
	command := exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(script.String())
	output, err := command.CombinedOutput()
	if err != nil {
		t.Fatalf("run Z3: %v\n%s", err, output)
	}
	if want := strings.TrimSpace(string(output)); want != "unsat" {
		t.Fatalf("z3=%s", want)
	}
}

func TestIntegerDifferenceResultsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	context := NewContext(92)
	x := IntConst(context, "x", 1)
	y := IntConst(context, "y", 2)
	cases := []struct {
		formula BoolExpr
		script  string
	}{
		{
			formula: And(Le(Sub(x, y), IntVal(context, 3)), Le(y, IntVal(context, 2)), Le(IntVal(context, 4), x)),
			script:  "(assert (and (<= (- x y) 3) (<= y 2) (<= 4 x)))",
		},
		{
			formula: And(Le(Sub(x, y), IntVal(context, -1)), Le(Sub(y, x), IntVal(context, -1))),
			script:  "(assert (and (<= (- x y) -1) (<= (- y x) -1)))",
		},
		{
			formula: Lt(x, x),
			script:  "(assert (< x x))",
		},
	}
	for index, test := range cases {
		ours := Check(Assert(index+1, NewSolver(context), test.formula))
		oursStatus := "sat"
		if _, unsat := ours.(Unsat); unsat {
			oursStatus = "unsat"
		}
		script := "(set-logic QF_IDL)\n(declare-const x Int)\n(declare-const y Int)\n" + test.script + "\n(check-sat)\n"
		cmd := exec.Command(z3, "-in", "-smt2")
		cmd.Stdin = strings.NewReader(script)
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("case %d: run Z3: %v\n%s", index, err, out)
		}
		if z3Status := strings.TrimSpace(string(out)); oursStatus != z3Status {
			t.Fatalf("case %d: gosmt=%s z3=%s", index, oursStatus, z3Status)
		}
	}
}

func TestArbitraryPrecisionIntegerDifferenceAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42494749444c))
	base := new(big.Int).Lsh(big.NewInt(1), 100)
	for example := 0; example < 64; example++ {
		offset := big.NewInt(int64(random.Intn(100000)))
		bound := new(big.Int).Add(base, offset)
		var assertion string
		if example%2 == 0 {
			assertion = fmt.Sprintf("(assert (and (<= %s x) (<= x %s)))", bound, new(big.Int).Add(new(big.Int).Set(bound), big.NewInt(3)))
		} else {
			assertion = fmt.Sprintf("(assert (and (<= (- x y) %s) (< (+ y %s) x)))", bound, bound)
		}
		script := "(set-logic QF_IDL)\n(declare-const x Int)\n(declare-const y Int)\n" + assertion + "\n(check-sat)"
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestGroundEUFResultsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	context := NewContext(93)
	a := UninterpretedConst(1, context, "a", 1)
	b := UninterpretedConst(1, context, "b", 2)
	c := UninterpretedConst(1, context, "c", 3)
	f := DeclareUnary(1, 1, context, "f", 1)
	tests := []struct {
		name    string
		formula BoolExpr
		asserts string
	}{
		{
			name:    "congruence contradiction",
			formula: And(EqUninterpreted(a, b), Not(EqUninterpreted(ApplyUninterpreted(f, a), ApplyUninterpreted(f, b)))),
			asserts: "(assert (= a b))\n(assert (not (= (f a) (f b))))",
		},
		{
			name:    "non-injective function",
			formula: And(Not(EqUninterpreted(a, b)), EqUninterpreted(ApplyUninterpreted(f, a), ApplyUninterpreted(f, b))),
			asserts: "(assert (not (= a b)))\n(assert (= (f a) (f b)))",
		},
		{
			name: "transitive nested congruence",
			formula: And(
				EqUninterpreted(a, b),
				EqUninterpreted(b, c),
				Not(EqUninterpreted(ApplyUninterpreted(f, ApplyUninterpreted(f, a)), ApplyUninterpreted(f, ApplyUninterpreted(f, c)))),
			),
			asserts: "(assert (= a b))\n(assert (= b c))\n(assert (not (= (f (f a)) (f (f c)))))",
		},
	}
	for index, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			result := Check(Assert(index+1, NewSolver(context), test.formula))
			ours := "sat"
			if _, unsat := result.(Unsat); unsat {
				ours = "unsat"
			}
			script := "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(declare-const b U)\n(declare-const c U)\n(declare-fun f (U) U)\n" + test.asserts + "\n(check-sat)\n"
			command := exec.Command(z3, "-in", "-smt2")
			command.Stdin = strings.NewReader(script)
			output, err := command.CombinedOutput()
			if err != nil {
				t.Fatalf("run Z3: %v\n%s", err, output)
			}
			if want := strings.TrimSpace(string(output)); ours != want {
				t.Fatalf("gosmt=%s z3=%s", ours, want)
			}
		})
	}
}

func TestGroundBinaryEUFResultsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	context := NewContext(94)
	a := UninterpretedConst(1, context, "a", 1)
	aPrime := UninterpretedConst(1, context, "a2", 2)
	b := UninterpretedConst(2, context, "b", 3)
	bPrime := UninterpretedConst(2, context, "b2", 4)
	combine := DeclareBinary(1, 2, 3, context, "combine", 5)
	formula := And(
		EqUninterpreted(a, aPrime),
		EqUninterpreted(b, bPrime),
		Not(EqUninterpreted(
			ApplyBinaryUninterpreted(combine, a, b),
			ApplyBinaryUninterpreted(combine, aPrime, bPrime),
		)),
	)
	ours := "sat"
	if _, unsat := Check(Assert(1, NewSolver(context), formula)).(Unsat); unsat {
		ours = "unsat"
	}
	script := `(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-sort R 0)
(declare-const a A)
(declare-const a2 A)
(declare-const b B)
(declare-const b2 B)
(declare-fun combine (A B) R)
(assert (= a a2))
(assert (= b b2))
(assert (not (= (combine a b) (combine a2 b2))))
(check-sat)`
	command := exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(script)
	output, err := command.CombinedOutput()
	if err != nil {
		t.Fatalf("run Z3: %v\n%s", err, output)
	}
	if want := strings.TrimSpace(string(output)); ours != want {
		t.Fatalf("gosmt=%s z3=%s", ours, want)
	}
}

func TestRealSortedFunctionBoundaryAgainstPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	congruence := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)`
	if got := smtLIBExecutionStatuses(t, ExecuteSMTLib(congruence)); fmt.Sprint(got) != "[unsat]" {
		t.Fatalf("congruence statuses=%v", got)
	}
	command := exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(congruence)
	output, err := command.CombinedOutput()
	if err != nil || strings.TrimSpace(string(output)) != "unsat" {
		t.Fatalf("Z3 congruence: %v %s", err, output)
	}

	shared := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (<= x y))
(assert (<= y x))
(assert (not (= (f x) (f y))))
(check-sat)`
	if got := smtLIBExecutionStatuses(t, ExecuteSMTLib(shared)); fmt.Sprint(got) != "[unsat]" {
		t.Fatalf("shared statuses=%v", got)
	}
	command = exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(shared)
	output, err = command.CombinedOutput()
	if err != nil || strings.TrimSpace(string(output)) != "unsat" {
		t.Fatalf("Z3 shared case: %v %s", err, output)
	}

	purifiedCases := []string{
		`(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (= x y))
(assert (<= (f x) 0))
(assert (< 0 (f y)))
(check-sat)`,
		`(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
(assert (= x y))
(assert (<= (f (+ x 1)) 0))
(assert (< 0 (f (+ y 1))))
(check-sat)`,
	}
	for index, script := range purifiedCases {
		if got := smtLIBExecutionStatuses(t, ExecuteSMTLib(script)); fmt.Sprint(got) != "[unsat]" {
			t.Fatalf("purified %d statuses=%v", index, got)
		}
		command = exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err = command.CombinedOutput()
		if err != nil || strings.TrimSpace(string(output)) != "unsat" {
			t.Fatalf("Z3 purified %d: %v %s", index, err, output)
		}
	}

	binary := `(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun combine (Real Real) Real)
(assert (= x y))
(assert (<= (combine (+ x 1) y) 0))
(assert (< 0 (combine (+ y 1) x)))
(check-sat)`
	if got := smtLIBExecutionStatuses(t, ExecuteSMTLib(binary)); fmt.Sprint(got) != "[unsat]" {
		t.Fatalf("binary purified statuses=%v", got)
	}
	command = exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(binary)
	output, err = command.CombinedOutput()
	if err != nil || strings.TrimSpace(string(output)) != "unsat" {
		t.Fatalf("Z3 binary purified: %v %s", err, output)
	}
}

func TestRandomPurifiedRealApplicationsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x55464c5241))
	for example := 0; example < 64; example++ {
		offset := random.Intn(11)
		upper := 4 + random.Intn(11)
		wantUnsat := random.Intn(2) == 0
		lower := upper - 1 - random.Intn(4)
		if wantUnsat {
			lower = upper + random.Intn(4)
		}
		equality := "(assert (= x y))"
		if example%2 != 0 {
			equality = "(assert (<= x y))\n(assert (<= y x))"
		}
		script := fmt.Sprintf(`(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-fun f (Real) Real)
%s
(assert (<= (f (+ x %s)) %s))
(assert (< %s (f (+ y %s))))
(check-sat)`, equality, fmt.Sprint(offset), fmt.Sprint(upper), fmt.Sprint(lower), fmt.Sprint(offset))
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorCoreAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x51464256))
	operators := []string{"bvand", "bvor", "bvxor", "bvadd"}
	for example := 0; example < 64; example++ {
		left := uint8(random.Intn(256))
		right := uint8(random.Intn(256))
		operator := operators[random.Intn(len(operators))]
		var expected uint8
		switch operator {
		case "bvand":
			expected = left & right
		case "bvor":
			expected = left | right
		case "bvxor":
			expected = left ^ right
		case "bvadd":
			expected = left + right
		}
		if example%2 != 0 {
			expected++
		}
		script := fmt.Sprintf("(set-logic QF_BV)\n(assert (= (%s #x%02x #x%02x) #x%02x))\n(check-sat)", operator, left, right, expected)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorOrderingAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4256434d50))
	operators := []string{"bvult", "bvule", "bvslt", "bvsle"}
	for example := 0; example < 64; example++ {
		left, right := uint8(random.Intn(256)), uint8(random.Intn(256))
		operator := operators[random.Intn(len(operators))]
		assertion := fmt.Sprintf("(%s #x%02x #x%02x)", operator, left, right)
		if example%2 != 0 {
			assertion = "(not " + assertion + ")"
		}
		script := "(set-logic QF_BV)\n(assert " + assertion + ")\n(check-sat)"
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorIntegerConversionsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4256494e54434f4e))
	integerLiteral := func(value int64) string {
		if value < 0 {
			return fmt.Sprintf("(- %d)", -value)
		}
		return fmt.Sprint(value)
	}
	for example := 0; example < 64; example++ {
		value := uint8(random.Intn(256))
		var assertion string
		switch example % 3 {
		case 0:
			expected := int(value)
			if example%2 != 0 {
				expected++
			}
			assertion = fmt.Sprintf("(= (ubv_to_int #x%02x) %d)", value, expected)
		case 1:
			expected := int(int8(value))
			if example%2 != 0 {
				expected++
			}
			assertion = fmt.Sprintf("(= (sbv_to_int #x%02x) %s)", value, integerLiteral(int64(expected)))
		case 2:
			integer := int64(random.Intn(1<<20)) - 1<<19
			expected := uint8(integer)
			if example%2 != 0 {
				expected++
			}
			assertion = fmt.Sprintf("(= ((_ int_to_bv 8) %s) #x%02x)", integerLiteral(integer), expected)
		}
		script := "(set-logic ALL)\n(assert " + assertion + ")\n(check-sat)"
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundIntegerArraysAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x51464152524159))
	for example := 0; example < 64; example++ {
		index := random.Intn(1000)
		value := random.Intn(2001) - 1000
		expected := value
		if example%2 != 0 {
			expected++
		}
		valueText, expectedText := fmt.Sprint(value), fmt.Sprint(expected)
		if value < 0 {
			valueText = fmt.Sprintf("(- %d)", -value)
		}
		if expected < 0 {
			expectedText = fmt.Sprintf("(- %d)", -expected)
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (= (select (store a %d %s) %d) %s))
(check-sat)`, index, valueText, index, expectedText)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundBitVectorArraysAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4155464256415252))
	for example := 0; example < 64; example++ {
		index := random.Intn(16)
		value := random.Intn(256)
		expected := value
		if example%2 != 0 {
			expected = (expected + 1) & 0xff
		}
		script := fmt.Sprintf(`(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= (select (store a #x%x #x%02x) #x%x) #x%02x))
(check-sat)`, index, value, index, expected)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundBitVectorArrayCongruenceAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x425641434f4e4752))
	for example := 0; example < 64; example++ {
		leftIndex := random.Intn(16)
		rightIndex := leftIndex
		if example%2 != 0 {
			rightIndex = (rightIndex + 1) & 0xf
		}
		script := fmt.Sprintf(`(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= a b))
(assert (not (= (select a #x%x) (select b #x%x))))
(check-sat)`, leftIndex, rightIndex)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundBitVectorArraySymbolicIndicesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42564153594d4944))
	for example := 0; example < 64; example++ {
		value := random.Intn(256)
		compared := value
		if example%2 != 0 {
			compared = (compared + 1) & 0xff
		}
		script := fmt.Sprintf(`(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(assert (= i j))
(assert (= (select (store a i #x%02x) j) #x%02x))
(check-sat)`, value, compared)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundBitVectorArrayStoreExtensionalityAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42564153544f5245))
	for example := 0; example < 64; example++ {
		firstIndex := random.Intn(16)
		secondIndex := (firstIndex + 1 + random.Intn(15)) & 0xf
		firstValue, secondValue := random.Intn(256), random.Intn(256)
		rightSecondValue := secondValue
		if example%2 != 0 {
			rightSecondValue = (rightSecondValue + 1) & 0xff
		}
		script := fmt.Sprintf(`(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= (store (store a #x%x #x%02x) #x%x #x%02x)
           (store (store a #x%x #x%02x) #x%x #x%02x)))
(check-sat)`, firstIndex, firstValue, secondIndex, secondValue, secondIndex, rightSecondValue, firstIndex, firstValue)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundArrayCongruenceAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x415252434f4e47))
	for example := 0; example < 64; example++ {
		leftIndex := random.Intn(1000)
		rightIndex := leftIndex
		if example%2 != 0 {
			rightIndex++
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= a b))
(assert (not (= (select a %d) (select b %d))))
(check-sat)`, leftIndex, rightIndex)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundArraySymbolicIndicesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x415252494e444558))
	for example := 0; example < 64; example++ {
		value := random.Intn(2001) - 1000
		valueText := fmt.Sprint(value)
		if value < 0 {
			valueText = fmt.Sprintf("(- %d)", -value)
		}
		indexRelation := "(assert (= i j))"
		if example%2 != 0 {
			indexRelation = "(assert (not (= i j)))"
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
%s
(assert (not (= (select (store a i %s) j) %s)))
(check-sat)`, indexRelation, valueText, valueText)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundArrayExtensionalModelsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4152524d4f44454c))
	for example := 0; example < 64; example++ {
		index := random.Intn(1000)
		left := random.Intn(2001) - 1000
		right := left
		relation := "(assert (not (= a b)))"
		if example%2 != 0 {
			right++
			relation = "(assert (= a b))"
		}
		integerText := func(value int) string {
			if value < 0 {
				return fmt.Sprintf("(- %d)", -value)
			}
			return fmt.Sprint(value)
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
%s
(assert (= (select a %d) %s))
(assert (= (select b %d) %s))
(check-sat)`, relation, index, integerText(left), index, integerText(right))
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundArrayStoreExtensionalityAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x53544f5245415252))
	for example := 0; example < 64; example++ {
		firstIndex := random.Intn(1000)
		secondIndex := firstIndex + 1 + random.Intn(1000)
		firstValue := random.Intn(2001) - 1000
		secondValue := firstValue + 1 + random.Intn(1000)
		integerText := func(value int) string {
			if value < 0 {
				return fmt.Sprintf("(- %d)", -value)
			}
			return fmt.Sprint(value)
		}
		var assertion string
		switch example % 4 {
		case 0:
			assertion = fmt.Sprintf("(assert (not (= (store a %d (select a %d)) a)))", firstIndex, firstIndex)
		case 1:
			assertion = fmt.Sprintf("(assert (not (= (store (store a %d %s) %d %s) (store (store a %d %s) %d %s))))", firstIndex, integerText(firstValue), secondIndex, integerText(secondValue), secondIndex, integerText(secondValue), firstIndex, integerText(firstValue))
		case 2:
			assertion = fmt.Sprintf("(assert (not (= (store a %d %s) (store a %d %s))))", firstIndex, integerText(firstValue), firstIndex, integerText(secondValue))
		default:
			assertion = fmt.Sprintf("(assert (= (store (store a %d %s) %d %s) (store a %d %s)))", firstIndex, integerText(firstValue), firstIndex, integerText(secondValue), firstIndex, integerText(secondValue))
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
%s
(check-sat)`, assertion)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundArrayCrossBaseEqualityAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x43524f5353415252))
	for example := 0; example < 64; example++ {
		updated := random.Intn(1000)
		outside := updated + 1 + random.Intn(1000)
		value := random.Intn(2001) - 1000
		other := value + 1 + random.Intn(1000)
		integerText := func(value int) string {
			if value < 0 {
				return fmt.Sprintf("(- %d)", -value)
			}
			return fmt.Sprint(value)
		}
		var assertions string
		switch example % 4 {
		case 0:
			assertions = fmt.Sprintf("(assert (= (store a %d %s) (store b %d %s)))\n(assert (not (= (select a %d) (select b %d))))", updated, integerText(value), updated, integerText(value), outside, outside)
		case 1:
			assertions = fmt.Sprintf("(assert (= (store a %d %s) (store b %d %s)))\n(assert (= (select a %d) %s))\n(assert (= (select b %d) %s))", updated, integerText(value), updated, integerText(value), updated, integerText(value), updated, integerText(other))
		case 2:
			assertions = fmt.Sprintf("(assert (= (store a %d %s) b))\n(assert (not (= (select b %d) %s)))", updated, integerText(value), updated, integerText(value))
		default:
			assertions = fmt.Sprintf("(assert (= (store (store a %d %s) %d %s) (store (store b %d %s) %d %s)))", updated, integerText(value), outside, integerText(other), outside, integerText(other), updated, integerText(value))
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
%s
(check-sat)`, assertions)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundArrayConstantBaseEqualityAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x434f4e5354415252))
	for example := 0; example < 64; example++ {
		index := random.Intn(1000)
		value := random.Intn(2001) - 1000
		other := value + 1 + random.Intn(1000)
		integerText := func(value int) string {
			if value < 0 {
				return fmt.Sprintf("(- %d)", -value)
			}
			return fmt.Sprint(value)
		}
		constant := fmt.Sprintf("((as const (Array Int Int)) %s)", integerText(value))
		var assertions string
		switch example % 4 {
		case 0:
			assertions = fmt.Sprintf("(assert (= a %s))\n(assert (not (= (select a %d) %s)))", constant, index, integerText(value))
		case 1:
			assertions = fmt.Sprintf("(assert (= a %s))\n(assert (= a ((as const (Array Int Int)) %s)))", constant, integerText(other))
		case 2:
			assertions = fmt.Sprintf("(assert (= (store a %d %s) (store %s %d %s)))\n(assert (= (select a %d) %s))", index, integerText(value), constant, index, integerText(value), index, integerText(other))
		default:
			assertions = fmt.Sprintf("(assert (= (store a %d %s) %s))", index, integerText(other), constant)
		}
		script := fmt.Sprintf(`(set-logic QF_ALIA)
(declare-const a (Array Int Int))
%s
(check-sat)`, assertions)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomMixedArrayIntegerArithmeticAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x415252415f49444c))
	for example := 0; example < 64; example++ {
		value := random.Intn(2001) - 1000
		valueText := fmt.Sprint(value)
		if value < 0 {
			valueText = fmt.Sprintf("(- %d)", -value)
		}
		bounds := "(assert (<= i j))\n(assert (<= j i))"
		if example%2 != 0 {
			bounds = "(assert (< i j))"
		}
		script := fmt.Sprintf(`(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
%s
(assert (not (= (select (store a i %s) j) %s)))
(check-sat)`, bounds, valueText, valueText)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorSubMulAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42564152495448))
	for example := 0; example < 64; example++ {
		left, right := uint8(random.Intn(256)), uint8(random.Intn(256))
		operator := "bvsub"
		expected := left - right
		if example%2 != 0 {
			operator, expected = "bvmul", left*right
		}
		if example%4 >= 2 {
			expected++
		}
		script := fmt.Sprintf("(set-logic QF_BV)\n(assert (= (%s #x%02x #x%02x) #x%02x))\n(check-sat)", operator, left, right, expected)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorShiftsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42565348494654))
	operators := []string{"bvshl", "bvlshr", "bvashr"}
	for example := 0; example < 64; example++ {
		value, amount := uint8(random.Intn(256)), uint8(random.Intn(16))
		operator := operators[random.Intn(len(operators))]
		var expected uint8
		if amount < 8 {
			switch operator {
			case "bvshl":
				expected = value << amount
			case "bvlshr":
				expected = value >> amount
			case "bvashr":
				expected = uint8(int8(value) >> amount)
			}
		} else if operator == "bvashr" && value&0x80 != 0 {
			expected = 0xff
		}
		if example%2 != 0 {
			expected++
		}
		script := fmt.Sprintf("(set-logic QF_BV)\n(assert (= (%s #x%02x #x%02x) #x%02x))\n(check-sat)", operator, value, amount, expected)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorDivisionAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42564449565245))
	operators := []string{"bvudiv", "bvurem", "bvsdiv", "bvsrem"}
	for example := 0; example < 64; example++ {
		left, right := uint8(random.Intn(256)), uint8(random.Intn(16))
		if example%8 == 0 {
			right = 0
		}
		operator := operators[example%len(operators)]
		var expected uint8
		switch operator {
		case "bvudiv":
			if right == 0 {
				expected = 0xff
			} else {
				expected = left / right
			}
		case "bvurem":
			if right == 0 {
				expected = left
			} else {
				expected = left % right
			}
		case "bvsdiv":
			a, d := int16(int8(left)), int16(int8(right))
			if d == 0 {
				if a < 0 {
					expected = 1
				} else {
					expected = 0xff
				}
			} else {
				expected = uint8(a / d)
			}
		case "bvsrem":
			a, d := int16(int8(left)), int16(int8(right))
			if d == 0 {
				expected = left
			} else {
				expected = uint8(a % d)
			}
		}
		if example%2 != 0 {
			expected++
		}
		script := fmt.Sprintf("(set-logic QF_BV)\n(assert (= (%s #x%02x #x%02x) #x%02x))\n(check-sat)", operator, left, right, expected)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorStructuralOperatorsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42565354525543))
	for example := 0; example < 64; example++ {
		value := uint8(random.Intn(256))
		var expression string
		var expected uint16
		switch example % 4 {
		case 0:
			other := uint8(random.Intn(16))
			expression = fmt.Sprintf("(concat #x%x #x%x)", value&0xf, other)
			expected = uint16(value&0xf)<<4 | uint16(other)
		case 1:
			expression = fmt.Sprintf("((_ extract 7 4) #x%02x)", value)
			expected = uint16(value >> 4)
		case 2:
			expression = fmt.Sprintf("((_ zero_extend 8) #x%02x)", value)
			expected = uint16(value)
		case 3:
			expression = fmt.Sprintf("((_ sign_extend 8) #x%02x)", value)
			expected = uint16(int16(int8(value)))
		}
		if example%2 != 0 {
			expected++
		}
		if example%4 == 0 {
			expected &= 0xff
		}
		if example%4 == 1 {
			expected &= 0x0f
		}
		width := 2
		if example%4 == 1 {
			width = 1
		}
		if example%4 >= 2 {
			width = 4
		}
		script := fmt.Sprintf("(set-logic QF_BV)\n(assert (= %s #x%0*x))\n(check-sat)", expression, width, expected)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorRotateRepeatOperatorsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4256524f54415445))
	for example := 0; example < 64; example++ {
		value := uint8(random.Intn(256))
		amount := random.Intn(32)
		var expression string
		var expected uint16
		width := 2
		switch example % 3 {
		case 0:
			expression = fmt.Sprintf("((_ rotate_left %d) #x%02x)", amount, value)
			shift := amount % 8
			expected = uint16(uint8(value<<shift | value>>(8-shift)))
		case 1:
			expression = fmt.Sprintf("((_ rotate_right %d) #x%02x)", amount, value)
			shift := amount % 8
			expected = uint16(uint8(value>>shift | value<<(8-shift)))
		case 2:
			nibble := value & 0xf
			expression = fmt.Sprintf("((_ repeat 2) #x%x)", nibble)
			expected = uint16(nibble)<<4 | uint16(nibble)
		}
		if example%2 != 0 {
			expected++
		}
		script := fmt.Sprintf("(set-logic QF_BV)\n(assert (= %s #x%0*x))\n(check-sat)", expression, width, expected&0xff)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomBitVectorOverflowPredicatesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x42564f564552464c))
	operators := []string{"bvuaddo", "bvsaddo", "bvusubo", "bvssubo", "bvumulo", "bvsmulo", "bvsdivo", "bvnego"}
	for example := 0; example < 64; example++ {
		left, right := uint8(random.Intn(256)), uint8(random.Intn(256))
		operator := operators[example%len(operators)]
		predicate := fmt.Sprintf("(%s #x%02x #x%02x)", operator, left, right)
		if operator == "bvnego" {
			predicate = fmt.Sprintf("(%s #x%02x)", operator, left)
		}
		if example%2 != 0 {
			predicate = "(not " + predicate + ")"
		}
		script := "(set-logic QF_BV)\n(assert " + predicate + ")\n(check-sat)"
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestRandomGroundUFBVAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x514655464256))
	for example := 0; example < 64; example++ {
		first, second := uint8(random.Intn(256)), uint8(random.Intn(256))
		var declarations, assertions string
		if example%2 == 0 {
			declarations = "(declare-fun f ((_ BitVec 8)) (_ BitVec 4))\n"
			assertions = fmt.Sprintf("(assert (= #x%02x #x%02x))\n(assert (not (= (f #x%02x) (f #x%02x))))", first, first, first, first)
			if example%4 == 2 {
				assertions = fmt.Sprintf("(assert (not (= #x%02x #x%02x)))\n(assert (= (f #x%02x) (f #x%02x)))", first, second, first, second)
			}
		} else {
			declarations = "(declare-fun combine ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))\n"
			assertions = fmt.Sprintf("(assert (= #x%02x #x%02x))\n(assert (not (= (combine #x%02x #x01) (combine #x%02x #x01))))", first, first, first, first)
			if example%4 == 3 {
				assertions = fmt.Sprintf("(assert (not (= #x%02x #x%02x)))\n(assert (= (combine #x%02x #x01) (combine #x%02x #x01)))", first, second, first, second)
			}
		}
		script := "(set-logic QF_UFBV)\n" + declarations + assertions + "\n(check-sat)"
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
}

func TestLinearRealResultsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	context := NewContext(95)
	x := RealConst(context, "x", 1)
	y := RealConst(context, "y", 2)
	tests := []struct {
		name    string
		formula BoolExpr
		asserts string
	}{
		{
			name: "fractional model",
			formula: And(
				LeReal(AddReal(x, y), RealVal(context, Rational(3, 1))),
				LeReal(RealVal(context, Rational(1, 2)), x),
				LtReal(RealVal(context, Rational(1, 3)), y),
			),
			asserts: "(assert (<= (+ x y) 3))\n(assert (<= (/ 1 2) x))\n(assert (< (/ 1 3) y))",
		},
		{
			name: "strict contradiction",
			formula: And(
				LtReal(x, RealVal(context, Rational(0, 1))),
				LeReal(RealVal(context, Rational(0, 1)), x),
			),
			asserts: "(assert (< x 0))\n(assert (<= 0 x))",
		},
		{
			name: "arbitrary precision strict interval",
			formula: And(
				LtReal(RealVal(context, Rational(0, 1)), x),
				LtReal(x, RealVal(context, func() smt.Rational {
					value, _ := smt.ParseRational("1/1000000000000000000000000000000000000000000")
					return value
				}())),
			),
			asserts: "(assert (< 0 x))\n(assert (< x (/ 1 1000000000000000000000000000000000000000000)))",
		},
	}
	for index, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			result := Check(Assert(index+1, NewSolver(context), test.formula))
			ours := "sat"
			if _, ok := result.(Unsat); ok {
				ours = "unsat"
			} else if _, ok := result.(Unknown); ok {
				ours = "unknown"
			}
			script := "(set-logic QF_LRA)\n(declare-const x Real)\n(declare-const y Real)\n" + test.asserts + "\n(check-sat)\n"
			command := exec.Command(z3, "-in", "-smt2")
			command.Stdin = strings.NewReader(script)
			output, err := command.CombinedOutput()
			if err != nil {
				t.Fatalf("run Z3: %v\n%s", err, output)
			}
			if want := strings.TrimSpace(string(output)); ours != want {
				t.Fatalf("gosmt=%s z3=%s", ours, want)
			}
		})
	}
}

func TestRandomLinearRealSystemsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(29))
	context := NewContext(96)
	variables := []RealExpr{
		RealConst(context, "x", 1),
		RealConst(context, "y", 2),
		RealConst(context, "z", 3),
	}
	for example := 0; example < 100; example++ {
		constraints := make([]BoolExpr, 0, 6)
		var assertions strings.Builder
		for constraint := 0; constraint < 6; constraint++ {
			terms := make([]RealExpr, 0, len(variables))
			encoded := make([]string, 0, len(variables))
			for variable, expression := range variables {
				coefficient := random.Intn(7) - 3
				if coefficient == 0 {
					continue
				}
				terms = append(terms, ScaleReal(Rational(int64(coefficient), 1), expression))
				encoded = append(encoded, fmt.Sprintf("(* %d %c)", coefficient, 'x'+rune(variable)))
			}
			left := RealVal(context, Rational(0, 1))
			leftText := "0"
			if len(terms) != 0 {
				left = AddReal(terms...)
				leftText = "(+ " + strings.Join(encoded, " ") + ")"
			}
			bound := random.Intn(11) - 5
			strict := random.Intn(3) == 0
			if strict {
				constraints = append(constraints, LtReal(left, RealVal(context, Rational(int64(bound), 1))))
				fmt.Fprintf(&assertions, "(assert (< %s %d))\n", leftText, bound)
			} else {
				constraints = append(constraints, LeReal(left, RealVal(context, Rational(int64(bound), 1))))
				fmt.Fprintf(&assertions, "(assert (<= %s %d))\n", leftText, bound)
			}
		}
		result := Check(Assert(example+1, NewSolver(context), And(constraints...)))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}
		script := "(set-logic QF_LRA)\n(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n" + assertions.String() + "(check-sat)\n"
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s\n%s", example, ours, result, want, script)
		}
	}
}

func TestRandomLinearIntegerSystemsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	type relation struct {
		coefficients [3]int
		bound        int
		equal        bool
	}
	random := rand.New(rand.NewSource(41))
	context := NewContext(105)
	variables := []IntExpr{
		IntConst(context, "x", 1),
		IntConst(context, "y", 2),
		IntConst(context, "z", 3),
	}
	for example := 0; example < 96; example++ {
		constraints := []BoolExpr{
			Le(IntVal(context, -5), variables[0]), Le(variables[0], IntVal(context, 5)),
			Le(IntVal(context, -5), variables[1]), Le(variables[1], IntVal(context, 5)),
			Le(IntVal(context, -5), variables[2]), Le(variables[2], IntVal(context, 5)),
		}
		relations := make([]relation, 0, 5)
		var assertions strings.Builder
		assertions.WriteString("(assert (and (<= -5 x) (<= x 5) (<= -5 y) (<= y 5) (<= -5 z) (<= z 5)))\n")
		for index := 0; index < 5; index++ {
			current := relation{bound: random.Intn(19) - 9, equal: index == 0 && example%3 == 0}
			terms := make([]IntExpr, 0, 3)
			encoded := make([]string, 0, 3)
			for variable, expression := range variables {
				coefficient := random.Intn(9) - 4
				current.coefficients[variable] = coefficient
				if coefficient == 0 {
					continue
				}
				terms = append(terms, ScaleInt64(int64(coefficient), expression))
				encoded = append(encoded, fmt.Sprintf("(* %d %c)", coefficient, 'x'+rune(variable)))
			}
			left := IntVal(context, 0)
			leftText := "0"
			if len(terms) != 0 {
				left = Add(terms...)
				leftText = "(+ " + strings.Join(encoded, " ") + ")"
			}
			if current.equal {
				constraints = append(constraints, EqInt(left, IntVal(context, int64(current.bound))))
				fmt.Fprintf(&assertions, "(assert (= %s %d))\n", leftText, current.bound)
			} else {
				constraints = append(constraints, Le(left, IntVal(context, int64(current.bound))))
				fmt.Fprintf(&assertions, "(assert (<= %s %d))\n", leftText, current.bound)
			}
			relations = append(relations, current)
		}
		result := Check(Assert(example+1, NewSolver(context), And(constraints...)))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}
		script := "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n" + assertions.String() + "(check-sat)\n"
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s\n%s", example, ours, result, want, script)
		}
		if sat, ok := result.(Sat); ok {
			values := [3]int64{}
			for index, variable := range variables {
				value, found := EvalInt(sat.Value, variable)
				if !found || value < -5 || value > 5 {
					t.Fatalf("example %d: invalid model value %d=(%d,%v)", example, index, value, found)
				}
				values[index] = value
			}
			for _, relation := range relations {
				left := int64(0)
				for index, coefficient := range relation.coefficients {
					left += int64(coefficient) * values[index]
				}
				if relation.equal && left != int64(relation.bound) || !relation.equal && left > int64(relation.bound) {
					t.Fatalf("example %d: invalid model relation=%+v values=%v", example, relation, values)
				}
			}
		}
	}
}

func TestRandomBooleanLinearIntegerSystemsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	type relation struct {
		x, y  int
		bound int
	}
	satisfied := func(relation relation, x, y int64) bool {
		return int64(relation.x)*x+int64(relation.y)*y <= int64(relation.bound)
	}
	random := rand.New(rand.NewSource(43))
	context := NewContext(107)
	x, y := IntConst(context, "x", 1), IntConst(context, "y", 2)
	for example := 0; example < 64; example++ {
		relations := [4]relation{}
		atoms := [4]BoolExpr{}
		encoded := [4]string{}
		for index := range relations {
			relation := relation{x: random.Intn(7) - 3, y: random.Intn(7) - 3, bound: random.Intn(15) - 7}
			if relation.x == 0 && relation.y == 0 {
				relation.x = 1
			}
			relations[index] = relation
			atoms[index] = Le(Add(ScaleInt64(int64(relation.x), x), ScaleInt64(int64(relation.y), y)), IntVal(context, int64(relation.bound)))
			encoded[index] = fmt.Sprintf("(<= (+ (* %d x) (* %d y)) %d)", relation.x, relation.y, relation.bound)
		}
		prohibited := random.Intn(9) - 4
		formula := And(
			Le(IntVal(context, -4), x), Le(x, IntVal(context, 4)),
			Le(IntVal(context, -4), y), Le(y, IntVal(context, 4)),
			Or(And(atoms[0], atoms[1]), And(atoms[2], atoms[3])),
			NeInt(x, IntVal(context, int64(prohibited))),
		)
		result := Check(Assert(example+1, NewSolver(context), formula))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}
		script := fmt.Sprintf(`(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (<= -4 x) (<= x 4) (<= -4 y) (<= y 4)))
(assert (or (and %s %s) (and %s %s)))
(assert (distinct x %d))
(check-sat)
`, encoded[0], encoded[1], encoded[2], encoded[3], prohibited)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s\n%s", example, ours, result, want, script)
		}
		if sat, ok := result.(Sat); ok {
			xValue, xOK := EvalInt(sat.Value, x)
			yValue, yOK := EvalInt(sat.Value, y)
			leftBranch := satisfied(relations[0], xValue, yValue) && satisfied(relations[1], xValue, yValue)
			rightBranch := satisfied(relations[2], xValue, yValue) && satisfied(relations[3], xValue, yValue)
			if !xOK || !yOK || xValue < -4 || xValue > 4 || yValue < -4 || yValue > 4 || xValue == int64(prohibited) || !leftBranch && !rightBranch {
				t.Fatalf("example %d: invalid model x=%d/%v y=%d/%v", example, xValue, xOK, yValue, yOK)
			}
		}
	}
}

func TestIntegerDivisionModuloAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	context := NewContext(109)
	x := IntConst(context, "x", 1)
	for example := 0; example < 128; example++ {
		dividend := int64((example*37)%129 - 64)
		divisor := int64(example%9 + 1)
		quotient, remainder := dividend/divisor, dividend%divisor
		if remainder < 0 {
			quotient--
			remainder += divisor
		}
		expectedRemainder := remainder
		if example%4 == 0 {
			expectedRemainder = (remainder + 1) % divisor
			if divisor == 1 {
				expectedRemainder = 1
			}
		}
		formula := And(
			EqInt(x, IntVal(context, dividend)),
			EqInt(DivInt64(x, divisor), IntVal(context, quotient)),
			EqInt(ModInt64(x, divisor), IntVal(context, expectedRemainder)),
		)
		result := Check(Assert(example+1, NewSolver(context), formula))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}
		script := fmt.Sprintf(`(set-logic QF_LIA)
(declare-const x Int)
(assert (= x %d))
(assert (= (div x %d) %d))
(assert (= (mod x %d) %d))
(check-sat)
`, dividend, divisor, quotient, divisor, expectedRemainder)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s\n%s", example, ours, result, want, script)
		}
		if sat, ok := result.(Sat); ok {
			q, qOK := EvalInt(sat.Value, DivInt64(x, divisor))
			r, rOK := EvalInt(sat.Value, ModInt64(x, divisor))
			if !qOK || !rOK || q != quotient || r != remainder {
				t.Fatalf("example %d: invalid model q=%d/%v r=%d/%v", example, q, qOK, r, rOK)
			}
		}
	}
}

func TestFormattedSMTLibIsAcceptedByPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	source := `(set-logic QF_IDL)
(set-option :produce-models true)
(declare-const |x value| Int)
(assert (<= |x value| 3))
(check-sat)`
	parsed, ok := ParseSMTLib(source).(smtlib.Parsed)
	if !ok {
		t.Fatalf("parse result=%T", ParseSMTLib(source))
	}
	formatted := smtlib.Format(parsed.Commands)
	command := exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(formatted)
	output, err := command.CombinedOutput()
	if err != nil {
		t.Fatalf("Z3 rejected formatted script: %v\n%s\nscript:\n%s", err, output, formatted)
	}
	if strings.TrimSpace(string(output)) != "sat" {
		t.Fatalf("output=%q", output)
	}
}

func TestSMTLibExecutionAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	tests := []struct {
		name   string
		script string
	}{
		{
			name: "boolean",
			script: `(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert (or a b))
(check-sat)
(push 1)
(assert (not a))
(assert (not b))
(check-sat)
(pop 1)
(check-sat)`,
		},
		{
			name: "integer difference logic",
			script: `(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(assert (<= (- x y) (- 1)))
(check-sat)
(push 1)
(assert (<= (- y x) (- 1)))
(check-sat)
(pop 1)
(check-sat)`,
		},
		{
			name: "assumptions",
			script: `(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(assert (or a b))
(check-sat-assuming ((not a) (not b)))
(check-sat-assuming (a))`,
		},
		{
			name: "ground euf",
			script: `(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(assert (= a b))
(check-sat)
(push 1)
(assert (not (= (f a) (f b))))
(check-sat)
(pop 1)
(check-sat)`,
		},
		{
			name: "linear real arithmetic",
			script: `(set-logic QF_LRA)
(declare-const x Real)
(assert (< 0 x))
(assert (< x (/ 1 1000000000000000000000000000000)))
(check-sat)
(push 1)
(assert (<= x 0))
(check-sat)
(pop 1)
(check-sat)`,
		},
		{
			name: "disjoint euf and linear real arithmetic",
			script: `(set-logic ALL)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(declare-const x Real)
(assert (not (= a b)))
(assert (= (f a) (f b)))
(assert (<= 1 x))
(assert (<= x 2))
(check-sat)
(push 1)
(assert (< x 1))
(check-sat)
(pop 1)
(check-sat)`,
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(test.script))
			command := exec.Command(z3, "-in", "-smt2")
			command.Stdin = strings.NewReader(test.script)
			output, err := command.CombinedOutput()
			if err != nil {
				t.Fatalf("run Z3: %v\n%s", err, output)
			}
			want := strings.Fields(string(output))
			if fmt.Sprint(ours) != fmt.Sprint(want) {
				t.Fatalf("statuses: gosmt=%v z3=%v\nscript:\n%s", ours, want, test.script)
			}
		})
	}
}

func smtLIBExecutionStatuses(t *testing.T, result smtlib.ExecutionResult) []string {
	t.Helper()
	executed, ok := result.(smtlib.Executed)
	if !ok {
		t.Fatalf("execution result=%#v", result)
	}
	statuses := make([]string, 0, len(executed.Responses))
	for _, response := range executed.Responses {
		switch response.(type) {
		case smtlib.Satisfiable:
			statuses = append(statuses, "sat")
		case smtlib.Unsatisfiable, smtlib.AssumptionsUnsatisfiable:
			statuses = append(statuses, "unsat")
		case smtlib.Unknown:
			statuses = append(statuses, "unknown")
		}
	}
	return statuses
}

func runZ3Boolean(t *testing.T, binary string, formula smt.Term[smt.BoolSort]) string {
	t.Helper()
	symbols := make(map[int]struct{})
	expression, ok := smtLIBBoolean(formula, symbols)
	if !ok {
		t.Fatal("test attempted to serialize an unsupported term")
	}
	ids := make([]int, 0, len(symbols))
	for id := range symbols {
		ids = append(ids, id)
	}
	sort.Ints(ids)
	var input strings.Builder
	input.WriteString("(set-logic QF_UF)\n")
	for _, id := range ids {
		fmt.Fprintf(&input, "(declare-const v%d Bool)\n", id)
	}
	fmt.Fprintf(&input, "(assert %s)\n(check-sat)\n", expression)
	cmd := exec.Command(binary, "-in", "-smt2")
	cmd.Stdin = strings.NewReader(input.String())
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("run Z3: %v\n%s", err, out)
	}
	return strings.TrimSpace(string(out))
}

func smtLIBBoolean(term smt.Term[smt.BoolSort], symbols map[int]struct{}) (string, bool) {
	switch value := term.(type) {
	case smt.Bool:
		if value.Value {
			return "true", true
		}
		return "false", true
	case smt.BoolSymbol:
		symbols[value.ID] = struct{}{}
		return fmt.Sprintf("v%d", value.ID), true
	case smt.BooleanVariable:
		symbols[value.ID] = struct{}{}
		return fmt.Sprintf("v%d", value.ID), true
	case smt.NegatedBooleanVariable:
		symbols[value.ID] = struct{}{}
		return fmt.Sprintf("(not v%d)", value.ID), true
	case smt.BooleanClause:
		return smtLIBEncodedClause(value.Literals, symbols)
	case smt.BooleanCNF:
		clauses := make([]string, 0, len(value.ClauseEnds))
		start := 0
		for _, end := range value.ClauseEnds {
			if end < start || end > len(value.Literals) {
				return "", false
			}
			clause, ok := smtLIBEncodedClause(value.Literals[start:end], symbols)
			if !ok {
				return "", false
			}
			clauses = append(clauses, clause)
			start = end
		}
		return "(and " + strings.Join(clauses, " ") + ")", start == len(value.Literals)
	case smt.Not:
		return smtLIBUnary("not", value.Value, symbols)
	case smt.And:
		return smtLIBMany("and", value.Values, symbols)
	case smt.Or:
		return smtLIBMany("or", value.Values, symbols)
	case smt.Implies:
		return smtLIBBinary("=>", value.Left, value.Right, symbols)
	case smt.Iff:
		return smtLIBBinary("=", value.Left, value.Right, symbols)
	case smt.If[smt.BoolSort]:
		condition, conditionOK := smtLIBBoolean(value.Condition, symbols)
		thenValue, thenOK := smtLIBBoolean(value.Then, symbols)
		elseValue, elseOK := smtLIBBoolean(value.Else, symbols)
		return fmt.Sprintf("(ite %s %s %s)", condition, thenValue, elseValue), conditionOK && thenOK && elseOK
	case smt.Equal:
		left, leftOK := value.Left.(smt.Term[smt.BoolSort])
		right, rightOK := value.Right.(smt.Term[smt.BoolSort])
		if !leftOK || !rightOK {
			return "", false
		}
		return smtLIBBinary("=", left, right, symbols)
	default:
		return "", false
	}
}

func smtLIBEncodedClause(literals []int, symbols map[int]struct{}) (string, bool) {
	values := make([]string, len(literals))
	for index, literal := range literals {
		if literal == 0 {
			return "", false
		}
		id := literal - 1
		if literal < 0 {
			id = -literal - 1
		}
		symbols[id] = struct{}{}
		values[index] = fmt.Sprintf("v%d", id)
		if literal < 0 {
			values[index] = "(not " + values[index] + ")"
		}
	}
	return "(or " + strings.Join(values, " ") + ")", true
}

func smtLIBUnary(operator string, value smt.Term[smt.BoolSort], symbols map[int]struct{}) (string, bool) {
	encoded, ok := smtLIBBoolean(value, symbols)
	return fmt.Sprintf("(%s %s)", operator, encoded), ok
}

func smtLIBBinary(operator string, left, right smt.Term[smt.BoolSort], symbols map[int]struct{}) (string, bool) {
	leftValue, leftOK := smtLIBBoolean(left, symbols)
	rightValue, rightOK := smtLIBBoolean(right, symbols)
	return fmt.Sprintf("(%s %s %s)", operator, leftValue, rightValue), leftOK && rightOK
}

func smtLIBMany(operator string, values []smt.Term[smt.BoolSort], symbols map[int]struct{}) (string, bool) {
	encoded := make([]string, len(values))
	for index, value := range values {
		item, ok := smtLIBBoolean(value, symbols)
		if !ok {
			return "", false
		}
		encoded[index] = item
	}
	return "(" + operator + " " + strings.Join(encoded, " ") + ")", true
}
