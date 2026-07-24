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
	"goforge.dev/goplus/std/vec"
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

func TestParametricDatatypeCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		value := example*17 - 211
		valueTerm := fmt.Sprint(value)
		if value < 0 {
			valueTerm = fmt.Sprintf("(- %d)", -value)
		}
		nextTerm := fmt.Sprint(value + 1)
		if value+1 < 0 {
			nextTerm = fmt.Sprintf("(- %d)", -(value + 1))
		}
		assertion := fmt.Sprintf("(assert (= (head xs) %s))", valueTerm)
		if example%2 != 0 {
			assertion = fmt.Sprintf("(assert (not (= (head xs) %s)))", valueTerm)
		}
		script := fmt.Sprintf(`(declare-datatypes ((PList 1))
  ((par (T) ((nil) (cons (head T) (tail (PList T)))))))
(declare-datatypes ((BList 1))
  ((par (T) ((bnil) (bcons (bhead T) (btail (BList T)))))))
(declare-datatypes ((CList 1))
  ((par (T) ((cnil) (ccons (chead T) (ctail (CList T)))))))
(declare-datatype Color ((red) (blue)))
(declare-const xs (PList Int))
(declare-const ys (PList Int))
(declare-const bits (BList (_ BitVec 8)))
(declare-const choice (CList Int))
(assert (= xs (cons %s (as nil (PList Int)))))
(assert ((_ is cons) xs))
(assert (= (match xs (((nil) 0) ((cons h t) h))) %s))
(assert (= (match ys (((nil) 0) ((cons h t) h))) %s))
(assert (= (match bits (((bnil) #x00) ((bcons h t) h))) #x2a))
(assert (= (match choice (((cnil) red) ((ccons h t) blue))) blue))
(assert (= ((_ update-field head) xs %s) (cons %s (as nil (PList Int)))))
%s
(check-sat)`, valueTerm, valueTerm, valueTerm, nextTerm, nextTerm, assertion)
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

func TestMultiParameterDatatypeCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		value := example*19 - 307
		valueTerm := fmt.Sprint(value)
		if value < 0 {
			valueTerm = fmt.Sprintf("(- %d)", -value)
		}
		boolean := "false"
		if example%2 == 0 {
			boolean = "true"
		}
		assertion := fmt.Sprintf("(assert (= (left xs) %s))", valueTerm)
		if example%3 == 0 {
			assertion = fmt.Sprintf("(assert (not (= (left xs) %s)))", valueTerm)
		}
		script := fmt.Sprintf(`(declare-datatypes ((Pair 2))
  ((par (A B) ((pair (first A) (second B))))))
(declare-datatypes ((DuoList 2))
  ((par (A B) ((dnil) (dcons (left A) (right B) (rest (DuoList A B)))))))
(declare-const p (Pair Int Bool))
(declare-const xs (DuoList Int Bool))
(assert (= p (pair %s %s)))
(assert (= xs (dcons %s %s (as dnil (DuoList Int Bool)))))
(assert (= (first p) %s))
(assert (= (second p) %s))
%s
(check-sat)`, valueTerm, boolean, valueTerm, boolean, valueTerm, boolean, assertion)
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

func TestMutuallyParametricDatatypeCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		value := example*23 - 401
		valueTerm := fmt.Sprint(value)
		if value < 0 {
			valueTerm = fmt.Sprintf("(- %d)", -value)
		}
		assertion := fmt.Sprintf("(assert (= (leaf-value (first-tree (children tree))) %s))", valueTerm)
		if example%2 != 0 {
			assertion = fmt.Sprintf("(assert (not (= (leaf-value (first-tree (children tree))) %s)))", valueTerm)
		}
		script := fmt.Sprintf(`(declare-datatypes ((Tree 1) (Forest 1))
  ((par (T) ((leaf (leaf-value T)) (node (children (Forest T)))))
   (par (T) ((empty) (more (first-tree (Tree T)) (rest-forest (Forest T)))))))
(declare-const tree (Tree Int))
(assert (= tree (node (more (leaf %s) (as empty (Forest Int))))))
%s
(check-sat)`, valueTerm, assertion)
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

func TestBooleanDatatypeCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	constructors := []string{"red", "green", "blue"}
	for example := 0; example < 64; example++ {
		selected := constructors[example%len(constructors)]
		other := constructors[(example+1)%len(constructors)]
		final := fmt.Sprintf("(assert (not (= x %s)))", other)
		if example%2 != 0 {
			final = fmt.Sprintf("(assert (= x %s))", other)
		}
		script := fmt.Sprintf(`(declare-datatype Color ((red) (green) (blue)))
(declare-const x Color)
(assert (or (= x red) (= x green) (= x blue)))
(assert (=> (= x red) (and (not (= x green)) (not (= x blue)))))
(assert (= (= x red) (and (not (= x green)) (not (= x blue)))))
(assert (ite (= x red) (not (= x blue)) (or (= x green) (= x blue))))
(assert (= x %s))
%s
(check-sat)`, selected, final)
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

func TestStringCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		value := fmt.Sprintf("go-%02d-forge", example)
		final := fmt.Sprintf(`(assert (= (str.len x) %d))`, len(value))
		if example%2 != 0 {
			final = `(assert (str.prefixof "not-a-prefix" "forge"))`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(assert (= x (str.++ "go-" "%02d" "-forge")))
(assert (str.contains x "%02d"))
(assert (str.prefixof "go-" x))
(assert (str.suffixof "-forge" x))
(assert (= (str.at x 2) "-"))
(assert (= (str.substr x 0 3) "go-"))
(assert (= (str.indexof x "-" 0) 2))
(assert (= (str.replace x "-" ":") "go:%02d-forge"))
(assert (= (str.replace_all x "-" ":") "go:%02d:forge"))
(assert (= (str.to_int "%02d") %d))
(assert (= (str.from_int %d) "%d"))
(assert (= (str.to_int "12x") (- 1)))
(assert (= (str.from_int (- 1)) ""))
(assert (= (str.to_code "\u{d800}") 55296))
(assert (= (str.from_code 55296) "\u{d800}"))
(assert (= (str.from_code 196608) ""))
(assert (str.is_digit "7"))
(assert (not (str.is_digit "٧")))
(assert (= (str.len "a\u{1f642}") 2))
(assert (= (str.at "a\u{1f642}" 1) "\u{1f642}"))
%s
(check-sat)`, example, example, example, example, example, example, example, example, final)
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

func TestStringRegexCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		count := 2 + example%3
		value := "go-" + strings.Repeat("a", count)
		final := fmt.Sprintf(`(assert (str.in_re x (re.++ (str.to_re "go-") ((_ re.loop %d %d) (str.to_re "a")))))`, count, count+1)
		if example%2 != 0 {
			final = fmt.Sprintf(`(assert (str.in_re "%s" (re.++ (str.to_re "go-") ((_ re.^ 1) (str.to_re "z")))))`, value)
		}
		script := fmt.Sprintf(`(set-logic ALL)
(declare-const x String)
(assert (= x "%s"))
(assert (str.in_re x (re.++ (str.to_re "go-") (re.+ (re.range "a" "z")))))
(assert (str.in_re x (re.++ (str.to_re "go") (re.* (re.union (str.to_re "-") (re.range "a" "z"))))))
(assert (str.in_re x (re.inter re.all (re.comp (str.to_re "other")))))
(assert (str.in_re "a" (re.diff re.allchar (str.to_re "b"))))
(assert (str.in_re "" (re.opt (str.to_re "x"))))
(assert (not (str.in_re "a" (re.range "" "z"))))
(assert (not (str.in_re "" (as re.none (RegEx String)))))
%s
(check-sat)`, value, final)
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

func TestSymbolicStringRegexCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		minimum := 1 + example%4
		prefix := fmt.Sprintf("p%02d-", example)
		extra := ""
		if example%2 != 0 {
			extra = fmt.Sprintf("(assert (= x \"%sz\"))", prefix)
		}
		script := fmt.Sprintf(`(set-logic ALL)
(declare-const x String)
%s
(assert (str.in_re x (re.++ (str.to_re "%s") ((_ re.loop %d %d) (re.range "a" "c")))))
(check-sat)`, extra, prefix, minimum, minimum+2)
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

func TestInteractingStringRegexCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		first := string(rune('a' + example%20))
		middle := string(rune('b' + example%20))
		last := string(rune('c' + example%20))
		var script string
		if example%2 == 0 {
			script = fmt.Sprintf(`(set-logic ALL)
(declare-const x String)
(assert (str.in_re x (re.union (str.to_re "%s") (str.to_re "%s"))))
(assert (str.in_re x (re.union (str.to_re "%s") (str.to_re "%s"))))
(assert (not (str.in_re x (str.to_re "%s"))))
(check-sat)`, first, middle, middle, last, first)
		} else {
			script = fmt.Sprintf(`(set-logic ALL)
(declare-const x String)
(assert (str.in_re x (str.to_re "%s")))
(assert (str.in_re x (str.to_re "%s")))
(check-sat)`, first, middle)
		}
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

func TestBooleanStringRegexCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		first := string(rune('a' + example%20))
		second := string(rune('b' + example%20))
		var assertion string
		if example%2 == 0 {
			assertion = fmt.Sprintf(`(assert (or (str.in_re x (str.to_re "%s")) (str.in_re x (str.to_re "%s"))))
(assert (not (str.in_re x (str.to_re "%s"))))
(assert (ite (str.in_re x (str.to_re "%s")) false (str.in_re x (str.to_re "%s"))))`,
				first, second, first, first, second)
		} else {
			assertion = fmt.Sprintf(`(assert (or (str.in_re x (str.to_re "%s")) (str.in_re x (str.to_re "%s"))))
(assert (= (str.in_re x (str.to_re "%s")) (str.in_re x (str.to_re "%s"))))`,
				first, second, first, second)
		}
		script := fmt.Sprintf(`(set-logic ALL)
(declare-const x String)
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

func TestSingleUnknownWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		prefix := fmt.Sprintf("p%02d-", example)
		target := prefix + "middle!"
		if example%2 != 0 {
			target = "wrong-middle!"
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.++ "%s" x "!") "%s"))
(check-sat)`, prefix, target)
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

func TestUniquelyDelimitedWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("[left%02d]right%02d{inner%02d}tail%02d!", example, example, example, example)
		if example%2 != 0 {
			target = fmt.Sprintf("[left%02d-right%02d{inner%02d}tail%02d!", example, example, example, example)
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(assert (= (str.++ "[" x "]" y "{" z "}" w "!") "%s"))
(assert (= x "left%02d"))
(check-sat)`, target, example)
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

func TestCanonicalBoundedWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		var script string
		switch example % 4 {
		case 0:
			script = fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const a String)
(declare-const b String)
(declare-const c String)
(declare-const d String)
(assert (= (str.++ a b c d) "word%02d"))
(check-sat)`, example)
		case 1:
			script = fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ "[" x "]" y "!") "[a%02d]b]c!"))
(check-sat)`, example)
		case 2:
			script = fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ "[" x "]" y "!") "wrong%02d!"))
(check-sat)`, example)
		default:
			script = fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ "[" x "]" y "!") "[a%02d]missing"))
(check-sat)`, example)
		}
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

func TestRepeatedSymbolWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		token := fmt.Sprintf("v%02d", example)
		last := token
		if example%2 != 0 {
			last = fmt.Sprintf("other%02d", example)
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x "-" y "-" x) "%s-middle-%s"))
(check-sat)`, token, last)
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

func TestInteractingAmbiguousWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		left := fmt.Sprintf("a%02d]b", example)
		if example%2 != 0 {
			left = fmt.Sprintf("wrong%02d", example)
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ "[" x "]" y "!") "[a%02d]b]c!"))
(assert (= x "%s"))
(check-sat)`, example, left)
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

func TestWordEquationLengthCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		length := 6
		if example%2 != 0 {
			length = 20
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			length = 1
			if example%2 != 0 {
				length = 3
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert (= (str.len x) %d))
(check-sat)`, target, length)
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

func TestWordEquationLengthInequalityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		lower, upper := 1, 6
		if example%2 != 0 {
			lower, upper = 14, 20
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			lower, upper = 0, 1
			if example%2 != 0 {
				lower, upper = 2, 3
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert (< %d (str.len x)))
(assert (<= (str.len x) %d))
(check-sat)`, target, lower, upper)
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

func TestWordEquationRelationalLengthCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := "abcd"
		relation := `(= (str.len x) (str.len y))`
		switch example % 4 {
		case 1:
			target = "abc"
		case 2:
			target = `\u{1f642}ab`
			relation = `(< (str.len y) (str.len x))`
		case 3:
			target = `\u{1f642}a`
			relation = `(or (= (str.len x) (str.len y)) (<= (str.len y) (str.len x)))`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert %s)
(check-sat)`, target, relation)
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

func TestWordEquationAffineLengthCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := "abcd"
		relation := `(= (+ (* 2 (str.len x)) (str.len y)) 6)`
		switch example % 4 {
		case 1:
			target = "abc"
			relation = `(= (+ (* 2 (str.len x)) (str.len y)) 7)`
		case 2:
			target = `\u{1f642}ab`
			relation = `(< 0 (- (str.len x) (str.len y)))`
		case 3:
			target = `\u{1f642}a`
			relation = `(or (= (+ (* 2 (str.len x)) (str.len y)) 3) (= (+ (* 2 (str.len x)) (str.len y)) 4))`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert %s)
(check-sat)`, target, relation)
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

func TestWordEquationIntegerStringOperationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := "abc"
		relation := `(= (str.indexof x "b" 0) 1)`
		switch example % 5 {
		case 1:
			target = "12z"
			relation = `(= (str.to_int x) 12)`
		case 2:
			target = `a\u{1f642}`
			relation = `(= (str.to_code x) 97)`
		case 3:
			relation = `(= (str.to_code x) 122)`
		case 4:
			target = "12z"
			relation = `(= (+ (str.to_int x) 1) 13)`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert %s)
(check-sat)`, target, relation)
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

func TestWordEquationDerivedStringOperationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := `a\u{1f642}c`
		relation := `(= (str.at x 1) "\u{1f642}")`
		switch example % 6 {
		case 1:
			target = "abcd"
			relation = `(= (str.substr x 1 2) "bc")`
		case 2:
			target = "abc"
			relation = `(= (str.replace x "a" "z") "z")`
		case 3:
			target = "12x"
			relation = `(= (str.at x 0) (str.at (str.from_int 12) 0))`
		case 4:
			target = `a\u{1f642}`
			relation = `(= (str.at x 0) (str.from_code 97))`
		case 5:
			target = "abc"
			relation = `(= (str.at x 4) "z")`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert %s)
(check-sat)`, target, relation)
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

func TestStandaloneDerivedStringEqualityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	scripts := []string{
		`(assert (= (str.at x 1) "\u{1f642}"))`,
		`(assert (and (= (str.substr x 1 3) "b\u{1f642}c") (= (str.at x 2) "\u{1f642}")))`,
		`(assert (= (str.substr x 2 8) "go"))`,
		`(assert (and (= (str.at x 0) "a") (= (str.at x 0) "b")))`,
		`(assert (and (= (str.at x 1) "") (= (str.at x 2) "c")))`,
		`(assert (= (str.from_code 97) (str.at x 0)))`,
		`(assert (= (str.substr x (- 1) 2) ""))`,
		`(assert (= (str.substr x 1 0) ""))`,
		`(declare-const offset Int)
(declare-const length Int)
(assert (and (= offset 1) (= length 2)
             (= (str.substr x offset length) "bc")
             (= (str.at x offset) "b")))`,
		`(declare-const needle String)
(declare-const offset Int)
(declare-const expected Int)
(assert (and (= x "abcabc") (= needle "bc") (= offset 2) (= expected 4)
             (= (str.indexof x needle offset) expected)))`,
		`(declare-const needle String)
(assert (and (= x "abcabc") (= needle "bc")
             (= (str.indexof x needle 2) 4)))`,
	}
	for example, assertion := range scripts {
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
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

func TestGroundRegexReplacementExtendsPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	scripts := []string{
		`(set-logic QF_SLIA)
(assert (= (str.replace_re "abc123def456" (re.+ (re.range "0" "9")) "!")
           "abc!23def456"))
(check-sat)`,
		`(set-logic QF_SLIA)
(assert (= (str.replace_re_all "abc123def456" (re.+ (re.range "0" "9")) "!")
           "abc!!!def!!!"))
(check-sat)`,
	}
	for index, script := range scripts {
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		if got := fmt.Sprint(ours); got != "[sat]" {
			t.Fatalf("case %d: gosmt=%s", index, got)
		}
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("case %d: Z3: %v\n%s", index, err, output)
		}
		if got := strings.TrimSpace(string(output)); got != "unknown" {
			t.Fatalf("case %d: expected pinned Z3 unknown, got %q", index, got)
		}
	}
}

func TestStringLexicographicOrderingCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	literals := []string{
		`""`, `"a"`, `"aa"`, `"z"`,
		`"\u{80}"`, `"\u{d800}"`, `"\u{1f642}"`, `"\u{20000}"`,
	}
	for example := 0; example < 64; example++ {
		operator := "str.<"
		if example%2 != 0 {
			operator = "str.<="
		}
		left := literals[example%len(literals)]
		right := literals[(example*5+3)%len(literals)]
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= x %s))
(assert (= y %s))
(assert (%s x y))
(check-sat)`, left, right, operator)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("ground example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("ground example %d: gosmt=%s z3=%s\n%s", example, got, want, script)
		}
	}
	assertions := []string{
		`(assert (str.< "a" "aa"))`,
		`(assert (str.< "\u{20000}" "\u{d800}"))`,
		`(assert (str.< x y))`,
		`(assert (str.< x x))`,
		`(assert (str.<= x x))`,
		`(assert (not (str.<= x x)))`,
		`(assert (and (str.< x y) (str.< y "z")))`,
		`(assert (and (str.< x y) (str.< y x)))`,
		`(assert (and (str.< x y) (str.<= y x)))`,
		`(assert (and (str.< "a" x) (str.<= x "a")))`,
		`(assert (and (str.< x "b") (str.< "a" x)))`,
	}
	for example, assertion := range assertions {
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
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

func TestIndexedCharacterConstantCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	boundaries := []int{0, 1, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xd800, 0xdfff, 0xe000, 0xffff, 0x10000, 0x2ffff}
	for example := 0; example < 64; example++ {
		code := (example*3137 + 97) % 0x30000
		if example < len(boundaries) {
			code = boundaries[example]
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(assert (= (str.to_code (_ char #x%X)) %d))
(assert (= (str.len (_ char #x%05x)) 1))
(assert (= (_ char #x%X) (str.from_code %d)))
(check-sat)`, code, code, code, code, code)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d code=%x: Z3: %v\n%s\n%s", example, code, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d code=%x: gosmt=%s z3=%s\n%s", example, code, got, want, script)
		}
	}
}

func TestStandaloneStringReplaceEqualityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	assertions := []string{
		`(assert (= (str.replace x "a" "z") "z"))`,
		`(assert (= (str.replace x "a" "z") "za"))`,
		`(assert (= (str.replace x "" "!") "!ab"))`,
		`(assert (= (str.replace x "a" "") "bc"))`,
		`(assert (= "go!\u{1f642}" (str.replace x "\u{1f642}" "!")))`,
		`(assert (and (= (str.replace x "a" "z") "z") (= (str.replace x "b" "y") "a")))`,
		`(assert (and (= (str.replace x "a" "z") "z") (= (str.replace x "a" "z") "q")))`,
		`(declare-const source String)
(declare-const replacement String)
(declare-const target String)
(assert (and (= source "a") (= replacement "z") (= target "za")
             (= (str.replace x source replacement) target) (= x "aa")))`,
	}
	for example, assertion := range assertions {
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
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

func TestStandaloneStringReplaceAllEqualityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	assertions := []string{
		`(assert (= (str.replace_all x "" "!") "ab"))`,
		`(assert (and (= (str.replace_all x "a" "z") "zz") (= (str.replace_all x "a" "z") "q")))`,
		`(assert (and (= (str.replace_all x "a" "z") "zz") (= x "aa")))`,
		`(assert (and (= (str.replace_all x "a" "z") "zz") (= x "q")))`,
		`(assert (and (= (str.replace_all x "\u{1f642}" "!") "!!") (= x "\u{1f642}\u{1f642}")))`,
		`(assert (and (= (str.replace_all x "ab" "") "ab") (= x "aabb")))`,
		`(assert (and (= (str.replace_all x "ab" "") "ab") (= x "aababb")))`,
		`(assert (and (= (str.replace_all x "ab" "") "ab") (= x "abaabb")))`,
		`(assert (and (= (str.replace_all x "a" "") "a") (= x "a")))`,
		`(declare-const source String)
(declare-const replacement String)
(declare-const target String)
(assert (and (= source "a") (= replacement "z") (= target "zz")
             (= (str.replace_all x source replacement) target) (= x "aa")))`,
	}
	for example, assertion := range assertions {
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
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

func TestStringReplaceIndexedInteractionCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	assertions := []string{
		`(assert (and (= (str.replace x "a" "z") "z") (= (str.at x 0) "a")))`,
		`(assert (and (= (str.replace x "a" "z") "z") (= (str.at x 0) "z")))`,
		`(assert (and (= (str.replace x "a" "z") "z") (= (str.substr x 0 1) "b")))`,
		`(assert (and (= (str.replace x "\u{1f642}" "!") "!") (= (str.at x 0) "\u{1f642}")))`,
	}
	for example, assertion := range assertions {
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
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

func TestStringReplacePredicateInteractionCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	assertions := []string{
		`(assert (and (= (str.replace x "a" "z") "z") (str.contains x "a")))`,
		`(assert (and (= (str.replace x "a" "z") "z") (not (str.contains x "a"))))`,
		`(assert (and (= (str.replace x "a" "z") "z") (= (str.len x) 1) (str.prefixof "a" x)))`,
		`(assert (and (= (str.replace x "a" "z") "z") (or (str.prefixof "b" x) (str.suffixof "b" x))))`,
		`(assert (and (= (str.replace x "1" "9") "9") (= (str.to_int x) 1)))`,
		`(assert (and (= (str.replace x "\u{1f642}" "!") "!") (str.contains x "\u{1f642}")))`,
	}
	for example, assertion := range assertions {
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
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

func TestGroundIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(340 + example)
		firstValue := int64(example - 31)
		secondValue := int64(example*3 + 1)
		first := UnitIntSequence(IntVal(context, firstValue))
		second := UnitIntSequence(IntVal(context, secondValue))
		sequence := ConcatIntSequence(first, EmptyIntSequence(context), second)
		same := ConcatIntSequence(
			UnitIntSequence(IntVal(context, firstValue)),
			UnitIntSequence(IntVal(context, secondValue)),
		)
		different := UnitIntSequence(IntVal(context, firstValue))
		formula := EqIntSequence(sequence, same)
		assertion := fmt.Sprintf(
			"(= (seq.++ (seq.unit %s) (as seq.empty (Seq Int)) (seq.unit %s)) (seq.++ (seq.unit %s) (seq.unit %s)))",
			sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue),
			sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue),
		)
		switch example % 6 {
		case 1:
			formula = Not(EqIntSequence(sequence, different))
			assertion = fmt.Sprintf(
				"(not (= (seq.++ (seq.unit %s) (seq.unit %s)) (seq.unit %s)))",
				sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue), sequenceIntegerLiteral(firstValue),
			)
		case 2:
			formula = EqInt(LengthIntSequence(sequence), IntVal(context, 2))
			assertion = fmt.Sprintf(
				"(= (seq.len (seq.++ (seq.unit %s) (seq.unit %s))) 2)",
				sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue),
			)
		case 3:
			formula = EqIntSequence(sequence, different)
			assertion = fmt.Sprintf(
				"(= (seq.++ (seq.unit %s) (seq.unit %s)) (seq.unit %s))",
				sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue), sequenceIntegerLiteral(firstValue),
			)
		case 4:
			formula = EqInt(LengthIntSequence(sequence), IntVal(context, 3))
			assertion = fmt.Sprintf(
				"(= (seq.len (seq.++ (seq.unit %s) (seq.unit %s))) 3)",
				sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue),
			)
		case 5:
			formula = Or(
				EqIntSequence(sequence, different),
				EqInt(LengthIntSequence(sequence), IntVal(context, 2)),
			)
			assertion = fmt.Sprintf(
				"(or (= (seq.++ (seq.unit %s) (seq.unit %s)) (seq.unit %s)) (= (seq.len (seq.++ (seq.unit %s) (seq.unit %s))) 2))",
				sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue), sequenceIntegerLiteral(firstValue),
				sequenceIntegerLiteral(firstValue), sequenceIntegerLiteral(secondValue),
			)
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := "(set-logic ALL)\n(assert " + assertion + ")\n(check-sat)"
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestGroundIntegerSequenceOperationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(440 + example)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		sequence := ConcatIntSequence(unit(1), unit(2), unit(3), unit(2))
		pair := ConcatIntSequence(unit(2), unit(3))
		empty := EmptyIntSequence(context)
		formula := EqIntSequence(AtIntSequence(sequence, IntVal(context, 1)), unit(2))
		assertion := "(= (seq.at s 1) (seq.unit 2))"
		switch example % 10 {
		case 1:
			formula = EqIntSequence(
				ExtractIntSequence(sequence, IntVal(context, 1), IntVal(context, 2)),
				pair,
			)
			assertion = "(= (seq.extract s 1 2) (seq.++ (seq.unit 2) (seq.unit 3)))"
		case 2:
			formula = ContainsIntSequence(sequence, pair)
			assertion = "(seq.contains s (seq.++ (seq.unit 2) (seq.unit 3)))"
		case 3:
			formula = HasPrefixIntSequence(sequence, ConcatIntSequence(unit(1), unit(2)))
			assertion = "(seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) s)"
		case 4:
			formula = HasSuffixIntSequence(sequence, ConcatIntSequence(unit(3), unit(2)))
			assertion = "(seq.suffixof (seq.++ (seq.unit 3) (seq.unit 2)) s)"
		case 5:
			formula = EqInt(
				IndexOfIntSequence(sequence, unit(2), IntVal(context, 2)),
				IntVal(context, 3),
			)
			assertion = "(= (seq.indexof s (seq.unit 2) 2) 3)"
		case 6:
			formula = EqIntSequence(
				ReplaceIntSequence(sequence, pair, unit(9)),
				ConcatIntSequence(unit(1), unit(9), unit(2)),
			)
			assertion = "(= (seq.replace s (seq.++ (seq.unit 2) (seq.unit 3)) (seq.unit 9)) (seq.++ (seq.unit 1) (seq.unit 9) (seq.unit 2)))"
		case 7:
			formula = ContainsIntSequence(sequence, unit(9))
			assertion = "(seq.contains s (seq.unit 9))"
		case 8:
			formula = EqIntSequence(AtIntSequence(sequence, IntVal(context, 9)), empty)
			assertion = "(= (seq.at s 9) (as seq.empty (Seq Int)))"
		case 9:
			formula = EqIntSequence(
				ReplaceIntSequence(sequence, empty, unit(9)),
				ConcatIntSequence(unit(9), sequence),
			)
			assertion = "(= (seq.replace s (as seq.empty (Seq Int)) (seq.unit 9)) (seq.++ (seq.unit 9) s))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(define-fun s () (Seq Int) (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3) (seq.unit 2)))
(assert ` + assertion + `)
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestGroundAssignedIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(540 + example)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		x := IntSequenceConst(context, "x", 1)
		ground := ConcatIntSequence(unit(1), unit(2), unit(3))
		relation := ContainsIntSequence(x, ConcatIntSequence(unit(2), unit(3)))
		assertion := "(seq.contains x (seq.++ (seq.unit 2) (seq.unit 3)))"
		switch example % 8 {
		case 1:
			relation = HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2)))
			assertion = "(seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) x)"
		case 2:
			relation = EqInt(LengthIntSequence(x), IntVal(context, 3))
			assertion = "(= (seq.len x) 3)"
		case 3:
			relation = EqIntSequence(AtIntSequence(x, IntVal(context, 1)), unit(2))
			assertion = "(= (seq.at x 1) (seq.unit 2))"
		case 4:
			relation = EqInt(
				IndexOfIntSequence(x, unit(3), IntVal(context, 0)),
				IntVal(context, 2),
			)
			assertion = "(= (seq.indexof x (seq.unit 3) 0) 2)"
		case 5:
			relation = EqIntSequence(
				ReplaceIntSequence(x, unit(2), unit(9)),
				ConcatIntSequence(unit(1), unit(9), unit(3)),
			)
			assertion = "(= (seq.replace x (seq.unit 2) (seq.unit 9)) (seq.++ (seq.unit 1) (seq.unit 9) (seq.unit 3)))"
		case 6:
			relation = EqIntSequence(x, ConcatIntSequence(unit(1), unit(2)))
			assertion = "(= x (seq.++ (seq.unit 1) (seq.unit 2)))"
		case 7:
			relation = Not(HasSuffixIntSequence(x, unit(3)))
			assertion = "(not (seq.suffixof (seq.unit 3) x))"
		}
		formula := And(EqIntSequence(x, ground), relation)
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(assert (= x (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))))
(assert ` + assertion + `)
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestPositiveSymbolicIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(620 + example)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		formula := ContainsIntSequence(x, unit(int64(example%7)))
		assertions := fmt.Sprintf("(assert (seq.contains x (seq.unit %d)))", example%7)
		switch example % 8 {
		case 1:
			formula = HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2)))
			assertions = "(assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) x))"
		case 2:
			formula = HasSuffixIntSequence(x, ConcatIntSequence(unit(3), unit(4)))
			assertions = "(assert (seq.suffixof (seq.++ (seq.unit 3) (seq.unit 4)) x))"
		case 3:
			formula = And(
				HasPrefixIntSequence(x, unit(1)),
				ContainsIntSequence(x, unit(2)),
				HasSuffixIntSequence(x, unit(3)),
			)
			assertions = `(assert (seq.prefixof (seq.unit 1) x))
(assert (seq.contains x (seq.unit 2)))
(assert (seq.suffixof (seq.unit 3) x))`
		case 4:
			formula = And(
				HasPrefixIntSequence(x, unit(1)),
				HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
			)
			assertions = `(assert (seq.prefixof (seq.unit 1) x))
(assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) x))`
		case 5:
			formula = And(
				HasSuffixIntSequence(x, unit(4)),
				HasSuffixIntSequence(x, ConcatIntSequence(unit(3), unit(4))),
			)
			assertions = `(assert (seq.suffixof (seq.unit 4) x))
(assert (seq.suffixof (seq.++ (seq.unit 3) (seq.unit 4)) x))`
		case 6:
			formula = And(
				ContainsIntSequence(x, unit(5)),
				ContainsIntSequence(y, unit(6)),
			)
			assertions = `(assert (seq.contains x (seq.unit 5)))
(assert (seq.contains y (seq.unit 6)))`
		case 7:
			formula = And(
				HasPrefixIntSequence(x, unit(1)),
				HasPrefixIntSequence(x, unit(2)),
			)
			assertions = `(assert (seq.prefixof (seq.unit 1) x))
(assert (seq.prefixof (seq.unit 2) x))`
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestExactLengthIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(700 + example)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		x := IntSequenceConst(context, "x", 1)
		length := int64(1 + example%7)
		formula := EqInt(LengthIntSequence(x), IntVal(context, length))
		assertions := fmt.Sprintf("(assert (= (seq.len x) %d))", length)
		switch example % 8 {
		case 1:
			formula = And(
				HasPrefixIntSequence(x, unit(1)),
				EqInt(LengthIntSequence(x), IntVal(context, 3)),
			)
			assertions = `(assert (seq.prefixof (seq.unit 1) x))
(assert (= (seq.len x) 3))`
		case 2:
			formula = And(
				HasSuffixIntSequence(x, unit(3)),
				EqInt(LengthIntSequence(x), IntVal(context, 3)),
			)
			assertions = `(assert (seq.suffixof (seq.unit 3) x))
(assert (= (seq.len x) 3))`
		case 3:
			formula = And(
				ContainsIntSequence(x, ConcatIntSequence(unit(2), unit(3))),
				EqInt(LengthIntSequence(x), IntVal(context, 4)),
			)
			assertions = `(assert (seq.contains x (seq.++ (seq.unit 2) (seq.unit 3))))
(assert (= (seq.len x) 4))`
		case 4:
			formula = And(
				HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
				HasSuffixIntSequence(x, ConcatIntSequence(unit(2), unit(3))),
				EqInt(LengthIntSequence(x), IntVal(context, 3)),
			)
			assertions = `(assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) x))
(assert (seq.suffixof (seq.++ (seq.unit 2) (seq.unit 3)) x))
(assert (= (seq.len x) 3))`
		case 5:
			formula = And(
				EqInt(LengthIntSequence(x), IntVal(context, 2)),
				EqInt(LengthIntSequence(x), IntVal(context, 3)),
			)
			assertions = `(assert (= (seq.len x) 2))
(assert (= (seq.len x) 3))`
		case 6:
			formula = And(
				ContainsIntSequence(x, ConcatIntSequence(unit(1), unit(2), unit(3))),
				EqInt(LengthIntSequence(x), IntVal(context, 2)),
			)
			assertions = `(assert (seq.contains x (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))))
(assert (= (seq.len x) 2))`
		case 7:
			formula = EqInt(LengthIntSequence(x), IntVal(context, -1))
			assertions = "(assert (= (seq.len x) (- 1)))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestRelationalLengthIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(780 + example)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		x := IntSequenceConst(context, "x", 1)
		formula := Le(IntVal(context, int64(example%5)), LengthIntSequence(x))
		assertions := fmt.Sprintf("(assert (<= %d (seq.len x)))", example%5)
		switch example % 8 {
		case 1:
			formula = Lt(IntVal(context, 4), LengthIntSequence(x))
			assertions = "(assert (< 4 (seq.len x)))"
		case 2:
			formula = Le(LengthIntSequence(x), IntVal(context, 3))
			assertions = "(assert (<= (seq.len x) 3))"
		case 3:
			formula = And(
				Le(IntVal(context, 2), LengthIntSequence(x)),
				Le(LengthIntSequence(x), IntVal(context, 4)),
			)
			assertions = `(assert (<= 2 (seq.len x)))
(assert (<= (seq.len x) 4))`
		case 4:
			formula = And(
				HasPrefixIntSequence(x, ConcatIntSequence(unit(1), unit(2))),
				HasSuffixIntSequence(x, ConcatIntSequence(unit(2), unit(3))),
				Le(LengthIntSequence(x), IntVal(context, 3)),
			)
			assertions = `(assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) x))
(assert (seq.suffixof (seq.++ (seq.unit 2) (seq.unit 3)) x))
(assert (<= (seq.len x) 3))`
		case 5:
			formula = And(
				Le(IntVal(context, 4), LengthIntSequence(x)),
				Le(LengthIntSequence(x), IntVal(context, 3)),
			)
			assertions = `(assert (<= 4 (seq.len x)))
(assert (<= (seq.len x) 3))`
		case 6:
			formula = Lt(LengthIntSequence(x), IntVal(context, 0))
			assertions = "(assert (< (seq.len x) 0))"
		case 7:
			formula = And(
				ContainsIntSequence(x, ConcatIntSequence(unit(1), unit(2), unit(3))),
				Le(LengthIntSequence(x), IntVal(context, 2)),
			)
			assertions = `(assert (seq.contains x (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))))
(assert (<= (seq.len x) 2))`
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestAffineLengthIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(860 + example)
		x := IntSequenceConst(context, "x", 1)
		length := LengthIntSequence(x)
		formula := EqInt(
			Add(ScaleInt64(2, length), IntVal(context, 1)),
			IntVal(context, 7),
		)
		assertion := "(= (+ (* 2 (seq.len x)) 1) 7)"
		switch example % 8 {
		case 1:
			formula = EqInt(ScaleInt64(2, length), IntVal(context, 3))
			assertion = "(= (* 2 (seq.len x)) 3)"
		case 2:
			formula = Le(
				Add(ScaleInt64(2, length), IntVal(context, 1)),
				IntVal(context, 9),
			)
			assertion = "(<= (+ (* 2 (seq.len x)) 1) 9)"
		case 3:
			formula = Lt(
				Add(ScaleInt64(-2, length), IntVal(context, 1)),
				IntVal(context, -4),
			)
			assertion = "(< (+ (* (- 2) (seq.len x)) 1) (- 4))"
		case 4:
			formula = And(
				Le(
					Add(ScaleInt64(2, length), IntVal(context, 1)),
					IntVal(context, 9),
				),
				Lt(
					Add(ScaleInt64(-2, length), IntVal(context, 1)),
					IntVal(context, -4),
				),
			)
			assertion = `(and
  (<= (+ (* 2 (seq.len x)) 1) 9)
  (< (+ (* (- 2) (seq.len x)) 1) (- 4)))`
		case 5:
			formula = Le(
				Sub(IntVal(context, 10), length),
				IntVal(context, 7),
			)
			assertion = "(<= (- 10 (seq.len x)) 7)"
		case 6:
			formula = EqInt(
				Sub(length, length),
				IntVal(context, 0),
			)
			assertion = "(= (- (seq.len x) (seq.len x)) 0)"
		case 7:
			formula = EqInt(
				Sub(length, length),
				IntVal(context, 1),
			)
			assertion = "(= (- (seq.len x) (seq.len x)) 1)"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(assert ` + assertion + `)
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestIntegerSequenceEqualityClassCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(940 + example)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		z := IntSequenceConst(context, "z", 3)
		formula := EqIntSequence(x, y)
		assertions := "(assert (= x y))"
		switch example % 8 {
		case 1:
			formula = And(
				EqIntSequence(x, y),
				EqIntSequence(y, ConcatIntSequence(unit(1), unit(2))),
			)
			assertions = `(assert (= x y))
(assert (= y (seq.++ (seq.unit 1) (seq.unit 2))))`
		case 2:
			formula = And(
				EqIntSequence(x, y),
				EqIntSequence(y, z),
				HasPrefixIntSequence(x, unit(1)),
				ContainsIntSequence(y, unit(2)),
				HasSuffixIntSequence(z, unit(3)),
			)
			assertions = `(assert (= x y))
(assert (= y z))
(assert (seq.prefixof (seq.unit 1) x))
(assert (seq.contains y (seq.unit 2)))
(assert (seq.suffixof (seq.unit 3) z))`
		case 3:
			formula = And(
				EqIntSequence(x, y),
				EqIntSequence(x, unit(1)),
				EqIntSequence(y, unit(2)),
			)
			assertions = `(assert (= x y))
(assert (= x (seq.unit 1)))
(assert (= y (seq.unit 2)))`
		case 4:
			formula = And(
				EqIntSequence(x, y),
				EqInt(LengthIntSequence(x), IntVal(context, 3)),
				EqInt(LengthIntSequence(y), IntVal(context, 3)),
			)
			assertions = `(assert (= x y))
(assert (= (seq.len x) 3))
(assert (= (seq.len y) 3))`
		case 5:
			formula = And(
				EqIntSequence(x, y),
				ContainsIntSequence(x, ConcatIntSequence(unit(4), unit(5))),
				HasSuffixIntSequence(y, unit(6)),
			)
			assertions = `(assert (= x y))
(assert (seq.contains x (seq.++ (seq.unit 4) (seq.unit 5))))
(assert (seq.suffixof (seq.unit 6) y))`
		case 6:
			formula = And(
				EqIntSequence(x, y),
				EqInt(LengthIntSequence(x), IntVal(context, 2)),
				EqInt(LengthIntSequence(y), IntVal(context, 3)),
			)
			assertions = `(assert (= x y))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 3))`
		case 7:
			formula = And(
				EqIntSequence(x, y),
				EqIntSequence(y, z),
				EqIntSequence(z, unit(int64(example))),
			)
			assertions = fmt.Sprintf(`(assert (= x y))
(assert (= y z))
(assert (= z (seq.unit %d)))`, example)
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestTwoSymbolAffineIntegerSequenceLengthCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1020 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		formula := EqInt(
			Add(ScaleInt64(2, xLength), yLength),
			IntVal(context, 7),
		)
		assertions := "(assert (= (+ (* 2 (seq.len x)) (seq.len y)) 7))"
		switch example % 8 {
		case 1:
			formula = EqInt(
				Add(ScaleInt64(2, xLength), ScaleInt64(2, yLength)),
				IntVal(context, 3),
			)
			assertions = "(assert (= (+ (* 2 (seq.len x)) (* 2 (seq.len y))) 3))"
		case 2:
			formula = EqInt(
				Add(ScaleInt64(-1, xLength), yLength),
				IntVal(context, 2),
			)
			assertions = "(assert (= (+ (* (- 1) (seq.len x)) (seq.len y)) 2))"
		case 3:
			formula = EqInt(
				Add(ScaleInt64(3, xLength), ScaleInt64(-1, yLength)),
				IntVal(context, 1),
			)
			assertions = "(assert (= (+ (* 3 (seq.len x)) (* (- 1) (seq.len y))) 1))"
		case 4:
			relation := EqInt(
				Add(ScaleInt64(2, xLength), yLength),
				IntVal(context, 7),
			)
			formula = And(
				relation,
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 3)),
			)
			assertions = `(assert (= (+ (* 2 (seq.len x)) (seq.len y)) 7))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 3))`
		case 5:
			relation := EqInt(
				Add(ScaleInt64(2, xLength), yLength),
				IntVal(context, 7),
			)
			formula = And(
				relation,
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 2)),
			)
			assertions = `(assert (= (+ (* 2 (seq.len x)) (seq.len y)) 7))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 2))`
		case 6:
			formula = EqInt(
				Sub(xLength, yLength),
				IntVal(context, -3),
			)
			assertions = "(assert (= (- (seq.len x) (seq.len y)) (- 3)))"
		case 7:
			formula = EqInt(
				Add(xLength, yLength),
				IntVal(context, int64(example%6)),
			)
			assertions = fmt.Sprintf(
				"(assert (= (+ (seq.len x) (seq.len y)) %d))",
				example%6,
			)
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestThreeSymbolAffineIntegerSequenceLengthCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1100 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		z := IntSequenceConst(context, "z", 3)
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		zLength := LengthIntSequence(z)
		target := int64(example % 7)
		formula := EqInt(Add(xLength, yLength, zLength), IntVal(context, target))
		assertions := fmt.Sprintf(
			"(assert (= (+ (seq.len x) (seq.len y) (seq.len z)) %d))",
			target,
		)
		switch example % 8 {
		case 1:
			formula = EqInt(
				Add(ScaleInt64(2, xLength), yLength, zLength),
				IntVal(context, 7),
			)
			assertions = "(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 7))"
		case 2:
			formula = EqInt(
				Add(ScaleInt64(-1, xLength), yLength, zLength),
				IntVal(context, 2),
			)
			assertions = "(assert (= (+ (* (- 1) (seq.len x)) (seq.len y) (seq.len z)) 2))"
		case 3:
			formula = EqInt(
				Add(
					ScaleInt64(3, xLength),
					ScaleInt64(-1, yLength),
					zLength,
				),
				IntVal(context, 1),
			)
			assertions = "(assert (= (+ (* 3 (seq.len x)) (* (- 1) (seq.len y)) (seq.len z)) 1))"
		case 4:
			relation := EqInt(
				Add(ScaleInt64(2, xLength), yLength, zLength),
				IntVal(context, 7),
			)
			formula = And(
				relation,
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 1)),
				EqInt(zLength, IntVal(context, 2)),
			)
			assertions = `(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 7))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 2))`
		case 5:
			relation := EqInt(
				Add(ScaleInt64(2, xLength), yLength, zLength),
				IntVal(context, 7),
			)
			formula = And(
				relation,
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 1)),
				EqInt(zLength, IntVal(context, 1)),
			)
			assertions = `(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 7))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 1))`
		case 6:
			formula = EqInt(
				Add(xLength, ScaleInt64(-1, yLength), zLength),
				IntVal(context, -3),
			)
			assertions = "(assert (= (+ (seq.len x) (* (- 1) (seq.len y)) (seq.len z)) (- 3)))"
		case 7:
			formula = EqInt(
				Add(xLength, yLength, ScaleInt64(-1, zLength)),
				IntVal(context, 3),
			)
			assertions = "(assert (= (+ (seq.len x) (seq.len y) (* (- 1) (seq.len z))) 3))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestMultiSymbolAffineIntegerSequenceLengthInequalityCorpusAgreesWithPinnedZ3(
	t *testing.T,
) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1200 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		z := IntSequenceConst(context, "z", 3)
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		zLength := LengthIntSequence(z)
		target := int64(example % 7)
		formula := Le(Add(xLength, yLength), IntVal(context, target))
		assertions := fmt.Sprintf(
			"(assert (<= (+ (seq.len x) (seq.len y)) %d))",
			target,
		)
		switch example % 8 {
		case 1:
			formula = Lt(
				Add(ScaleInt64(2, xLength), yLength),
				IntVal(context, 4),
			)
			assertions = "(assert (< (+ (* 2 (seq.len x)) (seq.len y)) 4))"
		case 2:
			formula = Le(
				Add(ScaleInt64(-1, xLength), yLength),
				IntVal(context, -2),
			)
			assertions = "(assert (<= (+ (* (- 1) (seq.len x)) (seq.len y)) (- 2)))"
		case 3:
			formula = Lt(
				Add(xLength, yLength, zLength),
				IntVal(context, 4),
			)
			assertions = "(assert (< (+ (seq.len x) (seq.len y) (seq.len z)) 4))"
		case 4:
			bound := Le(
				Add(ScaleInt64(2, xLength), yLength, zLength),
				IntVal(context, 7),
			)
			formula = And(
				bound,
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 1)),
				EqInt(zLength, IntVal(context, 2)),
			)
			assertions = `(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 7))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 2))`
		case 5:
			bound := Le(
				Add(ScaleInt64(2, xLength), yLength, zLength),
				IntVal(context, 6),
			)
			formula = And(
				bound,
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 1)),
				EqInt(zLength, IntVal(context, 2)),
			)
			assertions = `(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 6))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 2))`
		case 6:
			formula = Le(
				Add(xLength, yLength, ScaleInt64(-2, zLength)),
				IntVal(context, -3),
			)
			assertions = "(assert (<= (+ (seq.len x) (seq.len y) (* (- 2) (seq.len z))) (- 3)))"
		case 7:
			formula = Lt(
				Add(ScaleInt64(-1, xLength), yLength, zLength),
				IntVal(context, -2),
			)
			assertions = "(assert (< (+ (* (- 1) (seq.len x)) (seq.len y) (seq.len z)) (- 2)))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestInteractingAffineIntegerSequenceLengthRelationCorpusAgreesWithPinnedZ3(
	t *testing.T,
) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1300 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		z := IntSequenceConst(context, "z", 3)
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		zLength := LengthIntSequence(z)
		sum := Add(xLength, yLength, zLength)
		target := int64(example % 6)
		formula := And(
			Le(IntVal(context, target), sum),
			Le(sum, IntVal(context, target+2)),
		)
		assertions := fmt.Sprintf(
			"(assert (<= %d (+ (seq.len x) (seq.len y) (seq.len z))))\n"+
				"(assert (<= (+ (seq.len x) (seq.len y) (seq.len z)) %d))",
			target,
			target+2,
		)
		switch example % 8 {
		case 1:
			formula = And(
				Le(IntVal(context, 6), sum),
				Le(
					Add(ScaleInt64(2, xLength), yLength, zLength),
					IntVal(context, 8),
				),
			)
			assertions = `(assert (<= 6 (+ (seq.len x) (seq.len y) (seq.len z))))
(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 8))`
		case 2:
			pair := Add(xLength, yLength)
			formula = And(
				Le(pair, IntVal(context, 2)),
				Le(IntVal(context, 3), pair),
			)
			assertions = `(assert (<= (+ (seq.len x) (seq.len y)) 2))
(assert (<= 3 (+ (seq.len x) (seq.len y))))`
		case 3:
			formula = And(
				EqInt(sum, IntVal(context, 6)),
				Le(
					Add(ScaleInt64(2, xLength), yLength, zLength),
					IntVal(context, 8),
				),
			)
			assertions = `(assert (= (+ (seq.len x) (seq.len y) (seq.len z)) 6))
(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 8))`
		case 4:
			formula = And(
				Le(IntVal(context, 6), sum),
				Le(
					Add(ScaleInt64(2, xLength), yLength, zLength),
					IntVal(context, 8),
				),
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 1)),
				EqInt(zLength, IntVal(context, 3)),
			)
			assertions = `(assert (<= 6 (+ (seq.len x) (seq.len y) (seq.len z))))
(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 8))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 3))`
		case 5:
			formula = And(
				Le(
					Add(ScaleInt64(2, xLength), yLength, zLength),
					IntVal(context, 7),
				),
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 1)),
				EqInt(zLength, IntVal(context, 3)),
			)
			assertions = `(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z)) 7))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 3))`
		case 6:
			formula = And(
				Le(
					Add(xLength, yLength, ScaleInt64(-2, zLength)),
					IntVal(context, -3),
				),
				Le(sum, IntVal(context, 4)),
			)
			assertions = `(assert (<= (+ (seq.len x) (seq.len y) (* (- 2) (seq.len z))) (- 3)))
(assert (<= (+ (seq.len x) (seq.len y) (seq.len z)) 4))`
		case 7:
			formula = And(
				Lt(sum, IntVal(context, 4)),
				Lt(IntVal(context, 4), sum),
			)
			assertions = `(assert (< (+ (seq.len x) (seq.len y) (seq.len z)) 4))
(assert (< 4 (+ (seq.len x) (seq.len y) (seq.len z))))`
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestFourSymbolAffineIntegerSequenceLengthCorpusAgreesWithPinnedZ3(
	t *testing.T,
) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1400 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		z := IntSequenceConst(context, "z", 3)
		w := IntSequenceConst(context, "w", 4)
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		zLength := LengthIntSequence(z)
		wLength := LengthIntSequence(w)
		sum := Add(xLength, yLength, zLength, wLength)
		weighted := Add(ScaleInt64(2, xLength), yLength, zLength, wLength)
		target := int64(example % 7)
		formula := EqInt(sum, IntVal(context, target))
		assertions := fmt.Sprintf(
			"(assert (= (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w)) %d))",
			target,
		)
		switch example % 8 {
		case 1:
			formula = EqInt(weighted, IntVal(context, 10))
			assertions = "(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w)) 10))"
		case 2:
			formula = EqInt(
				Add(
					ScaleInt64(2, xLength),
					ScaleInt64(2, yLength),
					ScaleInt64(2, zLength),
					ScaleInt64(2, wLength),
				),
				IntVal(context, 7),
			)
			assertions = "(assert (= (+ (* 2 (seq.len x)) (* 2 (seq.len y)) (* 2 (seq.len z)) (* 2 (seq.len w))) 7))"
		case 3:
			formula = And(
				Le(IntVal(context, 8), sum),
				Le(weighted, IntVal(context, 10)),
			)
			assertions = `(assert (<= 8 (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w))))
(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w)) 10))`
		case 4:
			formula = And(
				EqInt(weighted, IntVal(context, 10)),
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 2)),
				EqInt(zLength, IntVal(context, 2)),
				EqInt(wLength, IntVal(context, 2)),
			)
			assertions = `(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w)) 10))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 2))
(assert (= (seq.len z) 2))
(assert (= (seq.len w) 2))`
		case 5:
			formula = And(
				Le(weighted, IntVal(context, 9)),
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 2)),
				EqInt(zLength, IntVal(context, 2)),
				EqInt(wLength, IntVal(context, 2)),
			)
			assertions = `(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w)) 9))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 2))
(assert (= (seq.len z) 2))
(assert (= (seq.len w) 2))`
		case 6:
			formula = And(
				Le(
					Add(xLength, yLength, zLength, ScaleInt64(-2, wLength)),
					IntVal(context, -3),
				),
				Le(sum, IntVal(context, 6)),
			)
			assertions = `(assert (<= (+ (seq.len x) (seq.len y) (seq.len z) (* (- 2) (seq.len w))) (- 3)))
(assert (<= (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w)) 6))`
		case 7:
			formula = And(
				Lt(sum, IntVal(context, 4)),
				Lt(IntVal(context, 4), sum),
			)
			assertions = `(assert (< (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w)) 4))
(assert (< 4 (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w))))`
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
(declare-const w (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestFiveSymbolAffineIntegerSequenceLengthCorpusAgreesWithPinnedZ3(
	t *testing.T,
) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1500 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		z := IntSequenceConst(context, "z", 3)
		w := IntSequenceConst(context, "w", 4)
		v := IntSequenceConst(context, "v", 5)
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		zLength := LengthIntSequence(z)
		wLength := LengthIntSequence(w)
		vLength := LengthIntSequence(v)
		sum := Add(xLength, yLength, zLength, wLength, vLength)
		weighted := Add(
			ScaleInt64(2, xLength), yLength, zLength, wLength, vLength,
		)
		target := int64(example % 7)
		formula := EqInt(sum, IntVal(context, target))
		assertions := fmt.Sprintf(
			"(assert (= (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) %d))",
			target,
		)
		switch example % 8 {
		case 1:
			formula = EqInt(weighted, IntVal(context, 12))
			assertions = "(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) 12))"
		case 2:
			formula = EqInt(
				Add(
					ScaleInt64(2, xLength),
					ScaleInt64(2, yLength),
					ScaleInt64(2, zLength),
					ScaleInt64(2, wLength),
					ScaleInt64(2, vLength),
				),
				IntVal(context, 7),
			)
			assertions = "(assert (= (+ (* 2 (seq.len x)) (* 2 (seq.len y)) (* 2 (seq.len z)) (* 2 (seq.len w)) (* 2 (seq.len v))) 7))"
		case 3:
			formula = And(
				Le(IntVal(context, 10), sum),
				Le(weighted, IntVal(context, 12)),
			)
			assertions = `(assert (<= 10 (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w) (seq.len v))))
(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) 12))`
		case 4:
			formula = And(
				EqInt(weighted, IntVal(context, 12)),
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 2)),
				EqInt(zLength, IntVal(context, 2)),
				EqInt(wLength, IntVal(context, 2)),
				EqInt(vLength, IntVal(context, 2)),
			)
			assertions = `(assert (= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) 12))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 2))
(assert (= (seq.len z) 2))
(assert (= (seq.len w) 2))
(assert (= (seq.len v) 2))`
		case 5:
			formula = And(
				Le(weighted, IntVal(context, 11)),
				EqInt(xLength, IntVal(context, 2)),
				EqInt(yLength, IntVal(context, 2)),
				EqInt(zLength, IntVal(context, 2)),
				EqInt(wLength, IntVal(context, 2)),
				EqInt(vLength, IntVal(context, 2)),
			)
			assertions = `(assert (<= (+ (* 2 (seq.len x)) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) 11))
(assert (= (seq.len x) 2))
(assert (= (seq.len y) 2))
(assert (= (seq.len z) 2))
(assert (= (seq.len w) 2))
(assert (= (seq.len v) 2))`
		case 6:
			formula = And(
				Le(
					Add(
						xLength,
						yLength,
						zLength,
						wLength,
						ScaleInt64(-2, vLength),
					),
					IntVal(context, -3),
				),
				Le(sum, IntVal(context, 7)),
			)
			assertions = `(assert (<= (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w) (* (- 2) (seq.len v))) (- 3)))
(assert (<= (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) 7))`
		case 7:
			formula = And(
				Lt(sum, IntVal(context, 5)),
				Lt(IntVal(context, 5), sum),
			)
			assertions = `(assert (< (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w) (seq.len v)) 5))
(assert (< 5 (+ (seq.len x) (seq.len y) (seq.len z) (seq.len w) (seq.len v))))`
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
(declare-const w (Seq Int))
(declare-const v (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestDisjunctiveSymbolicIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1600 + example)
		x := IntSequenceConst(context, "x", 1)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		length := LengthIntSequence(x)
		formula := Or(
			HasPrefixIntSequence(x, unit(1)),
			HasPrefixIntSequence(x, unit(2)),
		)
		assertions := "(assert (or (seq.prefixof (seq.unit 1) x) (seq.prefixof (seq.unit 2) x)))"
		switch example % 8 {
		case 1:
			formula = Or(
				And(
					EqInt(length, IntVal(context, 0)),
					HasPrefixIntSequence(x, unit(1)),
				),
				HasSuffixIntSequence(x, unit(2)),
			)
			assertions = "(assert (or (and (= (seq.len x) 0) (seq.prefixof (seq.unit 1) x)) (seq.suffixof (seq.unit 2) x)))"
		case 2:
			formula = Or(
				And(
					EqInt(length, IntVal(context, 0)),
					HasPrefixIntSequence(x, unit(1)),
				),
				And(
					EqInt(length, IntVal(context, 0)),
					HasSuffixIntSequence(x, unit(2)),
				),
			)
			assertions = "(assert (or (and (= (seq.len x) 0) (seq.prefixof (seq.unit 1) x)) (and (= (seq.len x) 0) (seq.suffixof (seq.unit 2) x))))"
		case 3:
			formula = And(
				Or(
					HasPrefixIntSequence(x, unit(3)),
					HasPrefixIntSequence(x, unit(4)),
				),
				EqInt(length, IntVal(context, 1)),
			)
			assertions = `(assert (or (seq.prefixof (seq.unit 3) x) (seq.prefixof (seq.unit 4) x)))
(assert (= (seq.len x) 1))`
		case 4:
			formula = Or(
				And(
					EqInt(length, IntVal(context, 2)),
					HasPrefixIntSequence(
						x,
						ConcatIntSequence(unit(5), unit(6)),
					),
				),
				And(
					EqInt(length, IntVal(context, 1)),
					HasSuffixIntSequence(x, unit(7)),
				),
			)
			assertions = "(assert (or (and (= (seq.len x) 2) (seq.prefixof (seq.++ (seq.unit 5) (seq.unit 6)) x)) (and (= (seq.len x) 1) (seq.suffixof (seq.unit 7) x))))"
		case 5:
			formula = Or(
				And(
					EqInt(ScaleInt64(2, length), IntVal(context, 3)),
					HasPrefixIntSequence(x, unit(8)),
				),
				EqInt(Add(length, IntVal(context, 1)), IntVal(context, 3)),
			)
			assertions = "(assert (or (and (= (* 2 (seq.len x)) 3) (seq.prefixof (seq.unit 8) x)) (= (+ (seq.len x) 1) 3)))"
		case 6:
			formula = Or(
				ContainsIntSequence(x, unit(9)),
				HasSuffixIntSequence(x, unit(10)),
			)
			assertions = "(assert (or (seq.contains x (seq.unit 9)) (seq.suffixof (seq.unit 10) x)))"
		case 7:
			formula = Or(
				HasPrefixIntSequence(x, unit(11)),
				HasPrefixIntSequence(x, unit(12)),
				HasPrefixIntSequence(x, unit(13)),
			)
			assertions = "(assert (or (seq.prefixof (seq.unit 11) x) (seq.prefixof (seq.unit 12) x) (seq.prefixof (seq.unit 13) x)))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestNegatedBooleanSymbolicIntegerSequenceLengthCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1700 + example)
		x := IntSequenceConst(context, "x", 1)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		length := LengthIntSequence(x)
		lengthOne := EqInt(length, IntVal(context, 1))
		prefix := HasPrefixIntSequence(x, unit(7))
		formula := Not(EqInt(length, IntVal(context, 0)))
		assertions := "(assert (not (= (seq.len x) 0)))"
		switch example % 8 {
		case 1:
			formula = And(lengthOne, Not(lengthOne))
			assertions = "(assert (and (= (seq.len x) 1) (not (= (seq.len x) 1))))"
		case 2:
			formula = And(lengthOne, ImpliesBool(lengthOne, prefix))
			assertions = "(assert (and (= (seq.len x) 1) (=> (= (seq.len x) 1) (seq.prefixof (seq.unit 7) x))))"
		case 3:
			formula = And(lengthOne, IffBool(lengthOne, prefix))
			assertions = "(assert (and (= (seq.len x) 1) (= (= (seq.len x) 1) (seq.prefixof (seq.unit 7) x))))"
		case 4:
			formula = And(
				lengthOne,
				IfBool(
					lengthOne,
					prefix,
					HasSuffixIntSequence(x, unit(8)),
				),
			)
			assertions = "(assert (and (= (seq.len x) 1) (ite (= (seq.len x) 1) (seq.prefixof (seq.unit 7) x) (seq.suffixof (seq.unit 8) x))))"
		case 5:
			formula = Not(Le(length, IntVal(context, 0)))
			assertions = "(assert (not (<= (seq.len x) 0)))"
		case 6:
			formula = And(
				Not(Lt(length, IntVal(context, 1))),
				HasSuffixIntSequence(x, unit(9)),
			)
			assertions = "(assert (and (not (< (seq.len x) 1)) (seq.suffixof (seq.unit 9) x)))"
		case 7:
			formula = And(
				Not(Not(EqInt(length, IntVal(context, 2)))),
				HasPrefixIntSequence(
					x, ConcatIntSequence(unit(10), unit(11)),
				),
			)
			assertions = "(assert (and (not (not (= (seq.len x) 2))) (seq.prefixof (seq.++ (seq.unit 10) (seq.unit 11)) x)))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestSymbolicIntegerSequenceGroundDisequalityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1800 + example)
		x := IntSequenceConst(context, "x", 1)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		pair := func(left, right int64) IntSequenceExpr {
			return ConcatIntSequence(unit(left), unit(right))
		}
		length := LengthIntSequence(x)
		formula := Not(EqIntSequence(x, EmptyIntSequence(context)))
		assertions := "(assert (not (= x (as seq.empty (Seq Int)))))"
		switch example % 8 {
		case 1:
			formula = And(
				EqInt(length, IntVal(context, 0)),
				Not(EqIntSequence(x, EmptyIntSequence(context))),
			)
			assertions = "(assert (and (= (seq.len x) 0) (not (= x (as seq.empty (Seq Int))))))"
		case 2:
			formula = And(
				EqInt(length, IntVal(context, 1)),
				Not(EqIntSequence(x, unit(0))),
			)
			assertions = "(assert (and (= (seq.len x) 1) (not (= x (seq.unit 0)))))"
		case 3:
			formula = And(
				EqIntSequence(x, unit(1)),
				Not(EqIntSequence(x, unit(1))),
			)
			assertions = "(assert (and (= x (seq.unit 1)) (not (= x (seq.unit 1)))))"
		case 4:
			formula = And(
				EqInt(length, IntVal(context, 2)),
				HasPrefixIntSequence(x, unit(1)),
				Not(EqIntSequence(x, pair(1, 0))),
			)
			assertions = "(assert (and (= (seq.len x) 2) (seq.prefixof (seq.unit 1) x) (not (= x (seq.++ (seq.unit 1) (seq.unit 0))))))"
		case 5:
			formula = And(
				EqInt(length, IntVal(context, 2)),
				ContainsIntSequence(x, unit(1)),
				ContainsIntSequence(x, unit(2)),
				Not(EqIntSequence(x, pair(1, 2))),
			)
			assertions = "(assert (and (= (seq.len x) 2) (seq.contains x (seq.unit 1)) (seq.contains x (seq.unit 2)) (not (= x (seq.++ (seq.unit 1) (seq.unit 2))))))"
		case 6:
			formula = And(
				EqInt(length, IntVal(context, 2)),
				ContainsIntSequence(x, unit(1)),
				ContainsIntSequence(x, unit(2)),
				Not(EqIntSequence(x, pair(1, 2))),
				Not(EqIntSequence(x, pair(2, 1))),
			)
			assertions = "(assert (and (= (seq.len x) 2) (seq.contains x (seq.unit 1)) (seq.contains x (seq.unit 2)) (not (= x (seq.++ (seq.unit 1) (seq.unit 2)))) (not (= x (seq.++ (seq.unit 2) (seq.unit 1))))))"
		case 7:
			formula = And(
				EqInt(length, IntVal(context, 1)),
				Not(EqIntSequence(x, unit(0))),
				Not(EqIntSequence(x, unit(1))),
				Not(EqIntSequence(x, unit(2))),
			)
			assertions = "(assert (and (= (seq.len x) 1) (not (= x (seq.unit 0))) (not (= x (seq.unit 1))) (not (= x (seq.unit 2)))))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestNegatedGroundSymbolicIntegerSequencePredicateCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(1900 + example)
		x := IntSequenceConst(context, "x", 1)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		length := LengthIntSequence(x)
		formula := Not(ContainsIntSequence(x, unit(0)))
		assertions := "(assert (not (seq.contains x (seq.unit 0))))"
		switch example % 8 {
		case 1:
			formula = And(
				EqInt(length, IntVal(context, 1)),
				Not(ContainsIntSequence(x, unit(0))),
			)
			assertions = "(assert (and (= (seq.len x) 1) (not (seq.contains x (seq.unit 0)))))"
		case 2:
			formula = And(
				EqInt(length, IntVal(context, 0)),
				Not(HasPrefixIntSequence(x, unit(1))),
			)
			assertions = "(assert (and (= (seq.len x) 0) (not (seq.prefixof (seq.unit 1) x))))"
		case 3:
			formula = And(
				EqInt(length, IntVal(context, 2)),
				ContainsIntSequence(x, unit(1)),
				Not(HasPrefixIntSequence(x, unit(1))),
			)
			assertions = "(assert (and (= (seq.len x) 2) (seq.contains x (seq.unit 1)) (not (seq.prefixof (seq.unit 1) x))))"
		case 4:
			formula = And(
				ContainsIntSequence(x, unit(1)),
				Not(ContainsIntSequence(x, unit(1))),
			)
			assertions = "(assert (and (seq.contains x (seq.unit 1)) (not (seq.contains x (seq.unit 1)))))"
		case 5:
			formula = And(
				HasPrefixIntSequence(x, unit(2)),
				Not(HasPrefixIntSequence(x, unit(2))),
			)
			assertions = "(assert (and (seq.prefixof (seq.unit 2) x) (not (seq.prefixof (seq.unit 2) x))))"
		case 6:
			formula = And(
				HasSuffixIntSequence(x, unit(3)),
				Not(HasSuffixIntSequence(x, unit(3))),
			)
			assertions = "(assert (and (seq.suffixof (seq.unit 3) x) (not (seq.suffixof (seq.unit 3) x))))"
		case 7:
			formula = Not(ContainsIntSequence(
				x, EmptyIntSequence(context),
			))
			assertions = "(assert (not (seq.contains x (as seq.empty (Seq Int)))))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestSymbolicIntegerSequencePairDisequalityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(2000 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		disequal := Not(EqIntSequence(x, y))
		formula := disequal
		assertions := "(assert (not (= x y)))"
		switch example % 8 {
		case 1:
			formula = And(
				EqInt(xLength, IntVal(context, 0)),
				EqInt(yLength, IntVal(context, 0)),
				disequal,
			)
			assertions = "(assert (and (= (seq.len x) 0) (= (seq.len y) 0) (not (= x y))))"
		case 2:
			formula = And(
				EqInt(xLength, IntVal(context, 1)),
				EqInt(yLength, IntVal(context, 1)),
				disequal,
			)
			assertions = "(assert (and (= (seq.len x) 1) (= (seq.len y) 1) (not (= x y))))"
		case 3:
			formula = And(
				EqInt(xLength, yLength),
				HasPrefixIntSequence(x, unit(1)),
				HasPrefixIntSequence(y, unit(1)),
				disequal,
			)
			assertions = "(assert (and (= (seq.len x) (seq.len y)) (seq.prefixof (seq.unit 1) x) (seq.prefixof (seq.unit 1) y) (not (= x y))))"
		case 4:
			formula = And(
				EqIntSequence(x, unit(2)),
				EqIntSequence(y, unit(2)),
				disequal,
			)
			assertions = "(assert (and (= x (seq.unit 2)) (= y (seq.unit 2)) (not (= x y))))"
		case 5:
			formula = And(EqIntSequence(x, y), disequal)
			assertions = "(assert (and (= x y) (not (= x y))))"
		case 6:
			formula = And(EqIntSequence(x, unit(3)), disequal)
			assertions = "(assert (and (= x (seq.unit 3)) (not (= x y))))"
		case 7:
			formula = And(
				EqInt(
					Add(
						ScaleInt64(2, xLength),
						ScaleInt64(-2, yLength),
					),
					IntVal(context, 0),
				),
				HasSuffixIntSequence(x, unit(4)),
				HasSuffixIntSequence(y, unit(4)),
				disequal,
			)
			assertions = "(assert (and (= (+ (* 2 (seq.len x)) (* (- 2) (seq.len y))) 0) (seq.suffixof (seq.unit 4) x) (seq.suffixof (seq.unit 4) y) (not (= x y))))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestNegatedSymbolicIntegerSequencePatternCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(2100 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		formula := Not(ContainsIntSequence(x, y))
		assertions := "(assert (not (seq.contains x y)))"
		switch example % 8 {
		case 1:
			formula = And(
				EqInt(xLength, yLength),
				HasPrefixIntSequence(x, unit(1)),
				HasPrefixIntSequence(y, unit(1)),
				Not(HasPrefixIntSequence(x, y)),
			)
			assertions = "(assert (and (= (seq.len x) (seq.len y)) (seq.prefixof (seq.unit 1) x) (seq.prefixof (seq.unit 1) y) (not (seq.prefixof y x))))"
		case 2:
			formula = And(
				EqIntSequence(x, y),
				Not(ContainsIntSequence(x, y)),
			)
			assertions = "(assert (and (= x y) (not (seq.contains x y))))"
		case 3:
			formula = And(
				EqInt(xLength, IntVal(context, 0)),
				Not(HasSuffixIntSequence(x, y)),
			)
			assertions = "(assert (and (= (seq.len x) 0) (not (seq.suffixof y x))))"
		case 4:
			formula = And(
				EqIntSequence(x, unit(1)),
				Not(ContainsIntSequence(x, y)),
			)
			assertions = "(assert (and (= x (seq.unit 1)) (not (seq.contains x y))))"
		case 5:
			formula = And(
				EqIntSequence(x, unit(1)),
				EqIntSequence(y, unit(1)),
				Not(HasPrefixIntSequence(x, y)),
			)
			assertions = "(assert (and (= x (seq.unit 1)) (= y (seq.unit 1)) (not (seq.prefixof y x))))"
		case 6:
			formula = And(
				EqInt(
					Add(
						ScaleInt64(2, xLength),
						ScaleInt64(-2, yLength),
					),
					IntVal(context, 0),
				),
				HasSuffixIntSequence(x, unit(4)),
				HasSuffixIntSequence(y, unit(4)),
				Not(HasSuffixIntSequence(x, y)),
			)
			assertions = "(assert (and (= (+ (* 2 (seq.len x)) (* (- 2) (seq.len y))) 0) (seq.suffixof (seq.unit 4) x) (seq.suffixof (seq.unit 4) y) (not (seq.suffixof y x))))"
		case 7:
			formula = And(
				EqInt(yLength, IntVal(context, 0)),
				Not(ContainsIntSequence(x, y)),
			)
			assertions = "(assert (and (= (seq.len y) 0) (not (seq.contains x y))))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestCyclicNegatedSymbolicIntegerSequencePatternCorpusAgreesWithPinnedZ3(
	t *testing.T,
) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(2200 + example)
		x := IntSequenceConst(context, "x", 1)
		y := IntSequenceConst(context, "y", 2)
		unit := func(value int64) IntSequenceExpr {
			return UnitIntSequence(IntVal(context, value))
		}
		xLength := LengthIntSequence(x)
		yLength := LengthIntSequence(y)
		formula := And(
			Not(ContainsIntSequence(x, y)),
			Not(ContainsIntSequence(y, x)),
		)
		assertions := "(assert (and (not (seq.contains x y)) (not (seq.contains y x))))"
		switch example % 8 {
		case 1:
			formula = And(
				EqInt(xLength, yLength),
				HasPrefixIntSequence(x, unit(1)),
				HasPrefixIntSequence(y, unit(1)),
				Not(HasPrefixIntSequence(x, y)),
				Not(HasPrefixIntSequence(y, x)),
			)
			assertions = "(assert (and (= (seq.len x) (seq.len y)) (seq.prefixof (seq.unit 1) x) (seq.prefixof (seq.unit 1) y) (not (seq.prefixof y x)) (not (seq.prefixof x y))))"
		case 2:
			formula = And(
				EqInt(xLength, yLength),
				HasSuffixIntSequence(x, unit(2)),
				HasSuffixIntSequence(y, unit(2)),
				Not(HasSuffixIntSequence(x, y)),
				Not(HasSuffixIntSequence(y, x)),
			)
			assertions = "(assert (and (= (seq.len x) (seq.len y)) (seq.suffixof (seq.unit 2) x) (seq.suffixof (seq.unit 2) y) (not (seq.suffixof y x)) (not (seq.suffixof x y))))"
		case 3:
			formula = And(
				EqIntSequence(x, y),
				Not(ContainsIntSequence(x, y)),
				Not(ContainsIntSequence(y, x)),
			)
			assertions = "(assert (and (= x y) (not (seq.contains x y)) (not (seq.contains y x))))"
		case 4:
			formula = And(
				EqIntSequence(x, unit(1)),
				EqIntSequence(y, unit(2)),
				Not(ContainsIntSequence(x, y)),
				Not(ContainsIntSequence(y, x)),
			)
			assertions = "(assert (and (= x (seq.unit 1)) (= y (seq.unit 2)) (not (seq.contains x y)) (not (seq.contains y x))))"
		case 5:
			formula = And(
				EqInt(xLength, IntVal(context, 0)),
				EqIntSequence(y, unit(1)),
				Not(ContainsIntSequence(x, y)),
				Not(ContainsIntSequence(y, x)),
			)
			assertions = "(assert (and (= (seq.len x) 0) (= y (seq.unit 1)) (not (seq.contains x y)) (not (seq.contains y x))))"
		case 6:
			formula = And(
				EqInt(xLength, IntVal(context, 1)),
				EqInt(yLength, IntVal(context, 1)),
				HasPrefixIntSequence(x, unit(1)),
				HasPrefixIntSequence(y, unit(1)),
				Not(HasPrefixIntSequence(x, y)),
				Not(HasPrefixIntSequence(y, x)),
			)
			assertions = "(assert (and (= (seq.len x) 1) (= (seq.len y) 1) (seq.prefixof (seq.unit 1) x) (seq.prefixof (seq.unit 1) y) (not (seq.prefixof y x)) (not (seq.prefixof x y))))"
		case 7:
			formula = And(
				EqInt(xLength, yLength),
				Not(ContainsIntSequence(x, y)),
				Not(HasPrefixIntSequence(y, x)),
			)
			assertions = "(assert (and (= (seq.len x) (seq.len y)) (not (seq.contains x y)) (not (seq.prefixof x y))))"
		}
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
` + assertions + `
(check-sat)`
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, oursStatus, want, script)
		}
	}
}

func TestNineSymbolAffineIntegerSequenceCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(2300 + example)
		expressions := make([]IntSequenceExpr, 9)
		lengths := make([]IntExpr, len(expressions))
		constraints := make([]BoolExpr, 0, len(expressions)+1)
		var declarations strings.Builder
		var requirements strings.Builder
		for index := range expressions {
			name := fmt.Sprintf("x%d", index)
			expressions[index] = IntSequenceConst(context, name, index+1)
			lengths[index] = LengthIntSequence(expressions[index])
			fmt.Fprintf(&declarations, "(declare-const %s (Seq Int))\n", name)
		}
		target := int64(9)
		for index, expression := range expressions {
			value := int64(index + 1)
			if example%8 == 4 {
				constraints = append(
					constraints,
					HasSuffixIntSequence(
						expression, UnitIntSequence(IntVal(context, value)),
					),
				)
				fmt.Fprintf(
					&requirements,
					"(seq.suffixof (seq.unit %d) x%d) ",
					value,
					index,
				)
				continue
			}
			prefix := UnitIntSequence(IntVal(context, value))
			if index == 0 && (example%8 == 5 || example%8 == 6) {
				prefix = ConcatIntSequence(prefix, UnitIntSequence(IntVal(context, 10)))
			}
			constraints = append(
				constraints, HasPrefixIntSequence(expression, prefix),
			)
			if index == 0 && (example%8 == 5 || example%8 == 6) {
				fmt.Fprintf(
					&requirements,
					"(seq.prefixof (seq.++ (seq.unit %d) (seq.unit 10)) x%d) ",
					value,
					index,
				)
			} else {
				fmt.Fprintf(
					&requirements,
					"(seq.prefixof (seq.unit %d) x%d) ",
					value,
					index,
				)
			}
		}
		sum := Add(lengths...)
		sumSMT := "(+"
		for index := range expressions {
			sumSMT += fmt.Sprintf(" (seq.len x%d)", index)
		}
		sumSMT += ")"
		switch example % 8 {
		case 1:
			target = 8
		case 2:
			target = 10
		case 3:
			for index, length := range lengths {
				constraints = append(
					constraints, EqInt(length, IntVal(context, 1)),
				)
				fmt.Fprintf(&requirements, "(= (seq.len x%d) 1) ", index)
			}
		case 5:
			target = 9
		case 6:
			target = 10
		case 7:
			sum = Add(ScaleInt64(2, lengths[0]), Add(lengths[1:]...))
			sumSMT = "(+ (* 2 (seq.len x0))"
			for index := 1; index < len(expressions); index++ {
				sumSMT += fmt.Sprintf(" (seq.len x%d)", index)
			}
			sumSMT += ")"
			target = 10
		}
		constraints = append(constraints, EqInt(sum, IntVal(context, target)))
		formula := And(constraints...)
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
` + declarations.String() + `(assert (and ` + requirements.String() +
			fmt.Sprintf("(= %s %d)))\n(check-sat)", sumSMT, target)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf(
				"nine-root example %d: gosmt=%s (%#v) z3=%s\n%s",
				example, oursStatus, ours, want, script,
			)
		}
	}
}

func TestSeventeenSymbolAffineIntegerSequenceCorpusAgreesWithPinnedZ3(
	t *testing.T,
) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		context := NewContext(2400 + example)
		expressions := make([]IntSequenceExpr, 17)
		lengths := make([]IntExpr, len(expressions))
		constraints := make([]BoolExpr, 0, len(expressions)+1)
		var declarations strings.Builder
		var requirements strings.Builder
		for index := range expressions {
			name := fmt.Sprintf("x%d", index)
			expressions[index] = IntSequenceConst(context, name, index+1)
			lengths[index] = LengthIntSequence(expressions[index])
			fmt.Fprintf(&declarations, "(declare-const %s (Seq Int))\n", name)
			value := int64(index + 1)
			if example%8 == 7 {
				constraints = append(
					constraints,
					HasSuffixIntSequence(
						expressions[index],
						UnitIntSequence(IntVal(context, value)),
					),
				)
				fmt.Fprintf(
					&requirements,
					"(seq.suffixof (seq.unit %d) x%d) ",
					value,
					index,
				)
				continue
			}
			prefix := UnitIntSequence(IntVal(context, value))
			if index == 0 && (example%8 == 3 || example%8 == 4) {
				prefix = ConcatIntSequence(
					prefix, UnitIntSequence(IntVal(context, 99)),
				)
			}
			constraints = append(
				constraints,
				HasPrefixIntSequence(expressions[index], prefix),
			)
			if index == 0 && (example%8 == 3 || example%8 == 4) {
				fmt.Fprintf(
					&requirements,
					"(seq.prefixof (seq.++ (seq.unit %d) (seq.unit 99)) x0) ",
					value,
				)
			} else {
				fmt.Fprintf(
					&requirements,
					"(seq.prefixof (seq.unit %d) x%d) ",
					value,
					index,
				)
			}
		}
		target := int64(17)
		sum := Add(lengths...)
		sumSMT := "(+"
		for index := range expressions {
			sumSMT += fmt.Sprintf(" (seq.len x%d)", index)
		}
		sumSMT += ")"
		switch example % 8 {
		case 1:
			target = 16
		case 2:
			target = 18
		case 3:
			target = 17
		case 4:
			target = 18
		case 5:
			for index, length := range lengths {
				constraints = append(
					constraints, EqInt(length, IntVal(context, 1)),
				)
				fmt.Fprintf(&requirements, "(= (seq.len x%d) 1) ", index)
			}
		case 6:
			sum = Add(ScaleInt64(2, lengths[0]), Add(lengths[1:]...))
			sumSMT = "(+ (* 2 (seq.len x0))"
			for index := 1; index < len(expressions); index++ {
				sumSMT += fmt.Sprintf(" (seq.len x%d)", index)
			}
			sumSMT += ")"
			target = 18
		}
		constraints = append(constraints, EqInt(sum, IntVal(context, target)))
		formula := And(constraints...)
		ours := Check(Assert(example+1, NewSolver(context), formula))
		oursStatus := "sat"
		if _, ok := ours.(Unsat); ok {
			oursStatus = "unsat"
		} else if _, ok := ours.(Unknown); ok {
			oursStatus = "unknown"
		}
		script := `(set-logic ALL)
` + declarations.String() + `(assert (and ` + requirements.String() +
			fmt.Sprintf("(= %s %d)))\n(check-sat)", sumSMT, target)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); oursStatus != want {
			t.Fatalf(
				"seventeen-root example %d: gosmt=%s (%#v) z3=%s\n%s",
				example, oursStatus, ours, want, script,
			)
		}
	}
}

func sequenceIntegerLiteral(value int64) string {
	if value < 0 {
		return fmt.Sprintf("(- %d)", -value)
	}
	return fmt.Sprint(value)
}

func TestMultipleWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		second := fmt.Sprintf(`(= (str.++ x "-" z) "left%02d-tail")`, example)
		if example%2 != 0 {
			second = `(= (str.++ x x) "zz")`
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			second = `(= (str.++ x "-" z) "\u{1f642}-tail")`
			if example%2 != 0 {
				second = `(= (str.++ x x) "zz")`
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= (str.++ x y) "%s"))
(assert %s)
(check-sat)`, target, second)
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

func TestEightWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		left := fmt.Sprintf("left%02d", example)
		right := "right"
		if example%4 >= 2 {
			left, right = `\u{1f642}`, "a"
		}
		last := fmt.Sprintf(`(= (str.++ z w "]") "%s!]")`, "tail")
		if example%2 != 0 {
			last = `(= (str.++ z w "]") "wrong]")`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(assert (= (str.++ x y) "%s%s"))
(assert (= (str.++ x "-" z) "%s-tail"))
(assert (= (str.++ y w) "%s!"))
(assert (= (str.++ z w) "tail!"))
(assert (= (str.++ "<" x y) "<%s%s"))
(assert (= (str.++ x y ">") "%s%s>"))
(assert (= (str.++ "[" z w) "[tail!"))
(assert %s)
(check-sat)`, left, right, left, right, left, right, left, right, last)
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

func TestOverflowWordEquationCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		left := fmt.Sprintf("left%02d", example)
		right := "right"
		if example%4 >= 2 {
			left, right = `\u{1f642}`, "a"
		}
		last := `(= (str.++ z w ")") "tail!)")`
		if example%2 != 0 {
			last = `(= (str.++ z w ")") "wrong)")`
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(assert (= (str.++ x y) "%s%s"))
(assert (= (str.++ x "-" z) "%s-tail"))
(assert (= (str.++ y w) "%s!"))
(assert (= (str.++ z w) "tail!"))
(assert (= (str.++ "<" x y) "<%s%s"))
(assert (= (str.++ x y ">") "%s%s>"))
(assert (= (str.++ "[" z w) "[tail!"))
(assert (= (str.++ z w "]") "tail!]"))
(assert (= (str.++ "<" x "-" z) "<%s-tail"))
(assert (= (str.++ x "-" z ">") "%s-tail>"))
(assert (= (str.++ "(" y w) "(%s!"))
(assert %s)
(check-sat)`,
			left, right, left, right, left, right, left, right, left, left, right, last,
		)
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

func TestOverflowWordEquationConstraintCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		complemented := "z"
		if example%2 != 0 {
			complemented = "a"
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const w String)
(declare-const v String)
(assert (= (str.++ x "-" y "-" z "-" w) "a-b-c-d"))
(assert (= (str.++ v "!") "e!"))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(assert (= (str.len z) 1))
(assert (= (str.len w) 1))
(assert (= (str.len v) 1))
(assert (str.in_re x (str.to_re "a")))
(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "z"))))
(assert (str.in_re x (re.inter re.all (str.to_re "a"))))
(assert (str.in_re x (re.diff (str.to_re "a") (str.to_re "z"))))
(assert (str.in_re x (re.comp (str.to_re "%s"))))
(assert (str.contains x "a"))
(assert (str.prefixof "a" x))
(assert (str.suffixof "a" x))
(assert (not (= x "z")))
(assert (not (= x "")))
(check-sat)`, complemented)
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

func TestWordEquationRegexCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		prefix := fmt.Sprintf("left%02d", example)
		regex := fmt.Sprintf(`(re.union (str.to_re "%s") (str.to_re "%sright"))`, prefix, prefix)
		if example%2 != 0 {
			regex = `(str.to_re "z")`
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			regex = `(re.union (str.to_re "\u{1f642}") (str.to_re "\u{1f642}a"))`
			if example%2 != 0 {
				regex = `(str.to_re "z")`
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert (str.in_re x %s))
(check-sat)`, target, regex)
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

func TestWordEquationBooleanRegexCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		prefix := fmt.Sprintf("left%02d", example)
		second := prefix
		if example%2 != 0 {
			second = "q"
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			prefix = `\u{1f642}`
			second = prefix
			if example%2 != 0 {
				second = "q"
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert (or (str.in_re x (str.to_re "z"))
            (str.in_re x (str.to_re "%s"))))
(check-sat)`, target, second)
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

func TestWordEquationStringDisequalityCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		forbidden := ""
		if example%2 != 0 {
			target = ""
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			forbidden = ""
			if example%2 != 0 {
				target = ""
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert (not (= x "%s")))
(check-sat)`, target, forbidden)
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

func TestWordEquationStringPredicateCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		target := fmt.Sprintf("left%02dright", example)
		part := fmt.Sprintf("%02d", example)
		if example%2 != 0 {
			part = "z"
		}
		if example%4 >= 2 {
			target = `\u{1f642}a`
			part = `\u{1f642}`
			if example%2 != 0 {
				part = "z"
			}
		}
		script := fmt.Sprintf(`(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x y) "%s"))
(assert (str.contains x "%s"))
(check-sat)`, target, part)
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

func TestIntegerSortedFunctionCongruenceAgainstPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for index := 0; index < 64; index++ {
		operator := "f"
		declaration := "(declare-fun f (Int) Int)"
		left, right := "(f x)", "(f y)"
		if index&1 != 0 {
			operator = "combine"
			declaration = "(declare-fun combine (Int Int) Int)"
			left, right = "(combine x y)", "(combine y x)"
		}
		relation := "(= x y)"
		want := "unsat"
		if index&2 != 0 {
			relation = "(not (= x y))"
			want = "sat"
		}
		if index&4 != 0 {
			left = fmt.Sprintf("(%s %d", operator, index)
			right = left
			if operator == "combine" {
				left += " x)"
				right += " x)"
			} else {
				left += ")"
				right += ")"
			}
			want = "unsat"
		}
		script := fmt.Sprintf(`(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
%s
(assert %s)
(assert (not (= %s %s)))
(check-sat)`, declaration, relation, left, right)
		got := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		if fmt.Sprint(got) != "["+want+"]" {
			t.Fatalf("case %d statuses=%v script=%s", index, got, script)
		}
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil || strings.TrimSpace(string(output)) != want {
			t.Fatalf("case %d Z3: %v %s", index, err, output)
		}
	}
}

func TestRandomPurifiedIntegerApplicationsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x55464c4941))
	for example := 0; example < 64; example++ {
		offset := random.Intn(11)
		upper := 4 + random.Intn(11)
		lower := upper - 1 - random.Intn(4)
		if random.Intn(2) == 0 {
			lower = upper + random.Intn(4)
		}
		equality := "(assert (= x y))"
		if example&1 != 0 {
			equality = "(assert (<= x y))\n(assert (<= y x))"
		}
		declaration := "(declare-fun f (Int) Int)"
		left := fmt.Sprintf("(f (+ x %d))", offset)
		right := fmt.Sprintf("(f (+ y %d))", offset)
		switch example % 3 {
		case 1:
			declaration = "(declare-fun f (Int Int) Int)"
			left = fmt.Sprintf("(f (+ x %d) y)", offset)
			right = fmt.Sprintf("(f (+ y %d) x)", offset)
		case 2:
			declaration = "(declare-fun f (Int Int Int) Int)"
			left = fmt.Sprintf("(f (+ x %d) y x)", offset)
			right = fmt.Sprintf("(f (+ y %d) x y)", offset)
		}
		script := fmt.Sprintf(`(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
%s
%s
(assert (<= %s %d))
(assert (< %d %s))
(check-sat)`, declaration, equality, left, upper, lower, right)
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

func TestRandomIntegerPredicatesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x5052454449434154))
	for example := 0; example < 64; example++ {
		leftOffset := random.Intn(7)
		rightOffset := leftOffset
		if example%4 == 0 {
			rightOffset++
		}
		equality := "(assert (= x y))"
		if example&1 != 0 {
			equality = "(assert (<= x y))\n(assert (<= y x))"
		}
		declaration := "(declare-fun p (Int) Bool)"
		left := fmt.Sprintf("(p (+ x %d))", leftOffset)
		rightApplication := fmt.Sprintf("(p (+ y %d))", rightOffset)
		if example%3 == 2 {
			declaration = "(declare-fun p (Int Int) Bool)"
			left = fmt.Sprintf("(p (+ x %d) z)", leftOffset)
			rightApplication = fmt.Sprintf("(p (+ y %d) z)", rightOffset)
		}
		right := "(not " + rightApplication + ")"
		if example&2 != 0 {
			right = rightApplication
		}
		script := fmt.Sprintf(`(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
%s
%s
(assert %s)
(assert %s)
(check-sat)`, declaration, equality, left, right)
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

func TestRandomRealPredicatesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x5245414c50524544))
	for example := 0; example < 64; example++ {
		leftOffset := random.Intn(7)
		rightOffset := leftOffset
		if example%4 == 0 {
			rightOffset++
		}
		equality := "(assert (= x y))"
		if example&1 != 0 {
			equality = "(assert (<= x y))\n(assert (<= y x))"
		}
		declaration := "(declare-fun p (Real) Bool)"
		left := fmt.Sprintf("(p (+ x %d))", leftOffset)
		rightApplication := fmt.Sprintf("(p (+ y %d))", rightOffset)
		if example%3 == 2 {
			declaration = "(declare-fun p (Real Real) Bool)"
			left = fmt.Sprintf("(p (+ x %d) z)", leftOffset)
			rightApplication = fmt.Sprintf("(p (+ y %d) z)", rightOffset)
		}
		right := "(not " + rightApplication + ")"
		if example&2 != 0 {
			right = rightApplication
		}
		script := fmt.Sprintf(`(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
%s
%s
(assert %s)
(assert %s)
(check-sat)`, declaration, equality, left, right)
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

func TestRandomTernaryRealApplicationsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x5245414c5445524e))
	for example := 0; example < 64; example++ {
		upper := 1 + random.Intn(19)
		lower := upper - 1
		if example&1 != 0 {
			lower = upper
		}
		offset := random.Intn(5)
		rightOffset := offset
		if example&2 != 0 {
			rightOffset++
		}
		script := fmt.Sprintf(`(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-fun combine3 (Real Real Real) Real)
(assert (= x y))
(assert (<= (combine3 (+ x %d) y z) %d))
(assert (< %d (combine3 (+ y %d) x z)))
(check-sat)`, offset, upper, lower, rightOffset)
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

func TestRandomGroundIntegerRealCoercionsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x434f455243494f4e))
	for example := 0; example < 64; example++ {
		integer := random.Intn(41) - 20
		integerText := fmt.Sprintf("%d", integer)
		integerRealText := fmt.Sprintf("%d.0", integer)
		if integer < 0 {
			integerText = fmt.Sprintf("(- %d)", -integer)
			integerRealText = fmt.Sprintf("(- %d.0)", -integer)
		}
		rationalText := integerRealText
		floor, integral := integer, true
		if example&1 != 0 {
			integral = false
			if integer >= 0 {
				rationalText = fmt.Sprintf("%d.5", integer)
			} else {
				rationalText = fmt.Sprintf("(- %d.5)", -integer)
				floor--
			}
		}
		integralityAssertion := fmt.Sprintf("(assert (is_int %s))", rationalText)
		if !integral {
			integralityAssertion = fmt.Sprintf("(assert (not (is_int %s)))", rationalText)
		}
		floorText := fmt.Sprintf("%d", floor)
		if floor < 0 {
			floorText = fmt.Sprintf("(- %d)", -floor)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(assert (= (to_real %s) %s))
(assert (= (to_int %s) %s))
%s
(check-sat)`,
			integerText, integerRealText, rationalText, floorText, integralityAssertion,
		)
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

func TestRandomSymbolicIntegerToRealComparisonsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x53594d544f524541))
	for example := 0; example < 64; example++ {
		lower := random.Intn(31) - 15
		upper := lower + random.Intn(4)
		fractional := example&1 != 0
		right := fmt.Sprintf("%d.0", upper)
		if upper < 0 {
			right = fmt.Sprintf("(- %d.0)", -upper)
		}
		if fractional {
			if upper >= 0 {
				right = fmt.Sprintf("%d.5", upper)
			} else {
				right = fmt.Sprintf("(- %d.5)", -upper)
			}
		}
		lowerText := fmt.Sprintf("%d.0", lower)
		if lower < 0 {
			lowerText = fmt.Sprintf("(- %d.0)", -lower)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(assert (<= %s (to_real x)))
(assert (< (to_real x) %s))
(check-sat)`, lowerText, right)
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

func TestRandomSymbolicIntegerRealRoundTripsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x524f554e44545249))
	for example := 0; example < 64; example++ {
		value := random.Intn(2001) - 1000
		valueText := fmt.Sprintf("%d", value)
		if value < 0 {
			valueText = fmt.Sprintf("(- %d)", -value)
		}
		contradiction := "(not (= (to_int (to_real x)) x))"
		if example&1 != 0 {
			contradiction = "(not (is_int (to_real x)))"
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(assert (= x %s))
(assert %s)
(check-sat)`, valueText, contradiction)
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

func TestRandomAffineIntegerRealCoercionsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x414646494e455249))
	for example := 0; example < 64; example++ {
		integer := random.Intn(101) - 50
		halfUnits := 2*random.Intn(15) - 15
		offset := smt.NewRational(int64(halfUnits), 2)
		expected := smt.AddIntegerValue(smt.NewIntegerValue(int64(integer)), smt.FloorRational(offset))
		integerText := fmt.Sprintf("%d", integer)
		if integer < 0 {
			integerText = fmt.Sprintf("(- %d)", -integer)
		}
		offsetText := offset.String()
		if halfUnits&1 == 0 {
			offsetText = fmt.Sprintf("%d.0", halfUnits/2)
			if halfUnits < 0 {
				offsetText = fmt.Sprintf("(- %d.0)", -halfUnits/2)
			}
		} else {
			absolute := halfUnits
			if absolute < 0 {
				absolute = -absolute
			}
			offsetText = fmt.Sprintf("%d.5", absolute/2)
			if halfUnits < 0 {
				offsetText = fmt.Sprintf("(- %s)", offsetText)
			}
		}
		expectedText := expected.String()
		if smt.CompareIntegerValue(expected, smt.IntegerValue{}) < 0 {
			expectedText = fmt.Sprintf("(- %s)", strings.TrimPrefix(expectedText, "-"))
		}
		integrality := fmt.Sprintf("(assert (is_int (+ (to_real x) %s)))", offsetText)
		if !offset.IsInteger() {
			integrality = fmt.Sprintf("(assert (not (is_int (+ (to_real x) %s))))", offsetText)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(assert (= x %s))
(assert (= (to_int (+ (to_real x) %s)) %s))
%s
(check-sat)`, integerText, offsetText, expectedText, integrality)
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

func TestRandomAffineIntegerRealComparisonsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x414646494e45434d))
	integerText := func(value int) string {
		if value < 0 {
			return fmt.Sprintf("(- %d)", -value)
		}
		return fmt.Sprintf("%d", value)
	}
	halfText := func(value int) string {
		absolute := value
		if absolute < 0 {
			absolute = -absolute
		}
		text := fmt.Sprintf("%d.%d", absolute/2, 5*(absolute&1))
		if value < 0 {
			return fmt.Sprintf("(- %s)", text)
		}
		return text
	}
	operators := [...]string{"=", "<", "<="}
	for example := 0; example < 64; example++ {
		x := random.Intn(41) - 20
		y := random.Intn(41) - 20
		leftOffset := random.Intn(21) - 10
		rightOffset := random.Intn(21) - 10
		operator := operators[example%len(operators)]
		assertion := fmt.Sprintf(
			"(assert (%s (+ (to_real x) %s) (+ (to_real y) %s)))",
			operator, halfText(leftOffset), halfText(rightOffset),
		)
		if example&1 != 0 {
			assertion = fmt.Sprintf(
				"(assert (not (%s (+ (to_real x) %s) (+ (to_real y) %s))))",
				operator, halfText(leftOffset), halfText(rightOffset),
			)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(declare-const y Int)
(assert (= x %s))
(assert (= y %s))
%s
(check-sat)`, integerText(x), integerText(y), assertion)
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

func TestRandomRationalScaledIntegerRealCoercionsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x5241545343414c45))
	for example := 0; example < 64; example++ {
		integer := random.Intn(101) - 50
		// Keep the SMT-LIB spelling positive here. Negative rational scaling
		// is covered through the typed API because the executor intentionally
		// does not accept a unary-minus term in the coefficient position yet.
		halfUnits := 2*random.Intn(8) + 1
		coefficient := smt.NewRational(int64(halfUnits), 2)
		product := smt.MultiplyRational(
			smt.RationalFromInteger(smt.NewIntegerValue(int64(integer))),
			coefficient,
		)
		expected := smt.FloorRational(product)
		integerText := fmt.Sprintf("%d", integer)
		if integer < 0 {
			integerText = fmt.Sprintf("(- %d)", -integer)
		}
		absolute := halfUnits
		if absolute < 0 {
			absolute = -absolute
		}
		coefficientText := fmt.Sprintf("%d.5", absolute/2)
		expectedText := expected.String()
		if smt.CompareIntegerValue(expected, smt.IntegerValue{}) < 0 {
			expectedText = fmt.Sprintf("(- %s)", strings.TrimPrefix(expectedText, "-"))
		}
		integrality := fmt.Sprintf("(assert (is_int (* %s (to_real x))))", coefficientText)
		if !product.IsInteger() {
			integrality = fmt.Sprintf("(assert (not (is_int (* %s (to_real x)))))", coefficientText)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(assert (= x %s))
(assert (= (to_int (* %s (to_real x))) %s))
%s
(check-sat)`, integerText, coefficientText, expectedText, integrality)
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

func TestRandomAffineRationalScaledIntegerRealCoercionsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4146465241545343))
	for example := 0; example < 64; example++ {
		integer := random.Intn(101) - 50
		coefficientHalfUnits := 2*random.Intn(8) + 1
		offsetHalfUnits := random.Intn(15) - 7
		coefficient := smt.NewRational(int64(coefficientHalfUnits), 2)
		offset := smt.NewRational(int64(offsetHalfUnits), 2)
		affine := smt.AddRational(
			smt.RationalFromInteger(smt.NewIntegerValue(int64(integer))),
			offset,
		)
		product := smt.MultiplyRational(coefficient, affine)
		expected := smt.FloorRational(product)
		integerText := fmt.Sprintf("%d", integer)
		if integer < 0 {
			integerText = fmt.Sprintf("(- %d)", -integer)
		}
		coefficientText := fmt.Sprintf("%d.5", coefficientHalfUnits/2)
		offsetAbsolute := offsetHalfUnits
		if offsetAbsolute < 0 {
			offsetAbsolute = -offsetAbsolute
		}
		offsetText := fmt.Sprintf("%d.5", offsetAbsolute/2)
		if offsetHalfUnits&1 == 0 {
			offsetText = fmt.Sprintf("%d.0", offsetAbsolute/2)
		}
		if offsetHalfUnits < 0 {
			offsetText = fmt.Sprintf("(- %s)", offsetText)
		}
		expectedText := expected.String()
		if smt.CompareIntegerValue(expected, smt.IntegerValue{}) < 0 {
			expectedText = fmt.Sprintf("(- %s)", strings.TrimPrefix(expectedText, "-"))
		}
		integrality := fmt.Sprintf(
			"(assert (is_int (* %s (+ (to_real x) %s))))",
			coefficientText, offsetText,
		)
		if !product.IsInteger() {
			integrality = fmt.Sprintf(
				"(assert (not (is_int (* %s (+ (to_real x) %s)))))",
				coefficientText, offsetText,
			)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(assert (= x %s))
(assert (= (to_int (* %s (+ (to_real x) %s))) %s))
%s
(check-sat)`, integerText, coefficientText, offsetText, expectedText, integrality)
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

func TestRandomTwoSymbolRationalScaledIntegerRealCoercionsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x54574f5241545343))
	for example := 0; example < 64; example++ {
		xValue := random.Intn(101) - 50
		yValue := random.Intn(101) - 50
		coefficientHalfUnits := 2*random.Intn(8) + 1
		offsetHalfUnits := random.Intn(15) - 7
		coefficient := smt.NewRational(int64(coefficientHalfUnits), 2)
		offset := smt.NewRational(int64(offsetHalfUnits), 2)
		integerSum := smt.NewIntegerValue(int64(xValue + yValue))
		affine := smt.AddRational(smt.RationalFromInteger(integerSum), offset)
		product := smt.MultiplyRational(coefficient, affine)
		expected := smt.FloorRational(product)
		integerText := func(value int) string {
			if value < 0 {
				return fmt.Sprintf("(- %d)", -value)
			}
			return fmt.Sprintf("%d", value)
		}
		coefficientText := fmt.Sprintf("%d.5", coefficientHalfUnits/2)
		offsetAbsolute := offsetHalfUnits
		if offsetAbsolute < 0 {
			offsetAbsolute = -offsetAbsolute
		}
		offsetText := fmt.Sprintf("%d.5", offsetAbsolute/2)
		if offsetHalfUnits&1 == 0 {
			offsetText = fmt.Sprintf("%d.0", offsetAbsolute/2)
		}
		if offsetHalfUnits < 0 {
			offsetText = fmt.Sprintf("(- %s)", offsetText)
		}
		expectedText := expected.String()
		if smt.CompareIntegerValue(expected, smt.IntegerValue{}) < 0 {
			expectedText = fmt.Sprintf("(- %s)", strings.TrimPrefix(expectedText, "-"))
		}
		integrality := fmt.Sprintf(
			"(assert (is_int (* %s (+ (to_real x) (to_real y) %s))))",
			coefficientText, offsetText,
		)
		if !product.IsInteger() {
			integrality = fmt.Sprintf(
				"(assert (not (is_int (* %s (+ (to_real x) (to_real y) %s)))))",
				coefficientText, offsetText,
			)
		}
		script := fmt.Sprintf(`(set-logic QF_LIRA)
(declare-const x Int)
(declare-const y Int)
(assert (= x %s))
(assert (= y %s))
(assert (= (to_int (* %s (+ (to_real x) (to_real y) %s))) %s))
%s
(check-sat)`,
			integerText(xValue), integerText(yValue),
			coefficientText, offsetText, expectedText, integrality,
		)
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

func TestRandomConditionalIntegerApplicationsAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x49544555464c4941))
	for example := 0; example < 64; example++ {
		upper := 1 + random.Intn(19)
		lower := upper - 1
		if example&1 != 0 {
			lower = upper
		}
		condition := "(<= x y)"
		thenTerm, elseTerm := "(f x)", "0"
		if example&2 != 0 {
			condition = "(< x y)"
			thenTerm, elseTerm = "0", "(f x)"
		}
		script := fmt.Sprintf(`(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= x y))
(assert (<= (ite %s %s %s) %d))
(assert (< %d (f y)))
(check-sat)`, condition, thenTerm, elseTerm, upper, lower)
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
		if example%2 != 0 {
			divisor = -divisor
		}
		quotient, remainder := dividend/divisor, dividend%divisor
		if remainder < 0 {
			if divisor > 0 {
				quotient--
				remainder += divisor
			} else {
				quotient++
				remainder -= divisor
			}
		}
		expectedRemainder := remainder
		if example%4 == 0 {
			magnitude := divisor
			if magnitude < 0 {
				magnitude = -magnitude
			}
			expectedRemainder = (remainder + 1) % magnitude
			if magnitude == 1 {
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

func TestFiniteEnumerationDatatypesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		constructorCount := 2 + example%4
		forced := (example * 3) % constructorCount
		compared := (example*5 + 1) % constructorCount
		equality := example%2 == 0
		context := NewContext(112)
		x := DatatypeConst(77, constructorCount, context, "x", 1)
		constructor := DatatypeConstructor(77, constructorCount, compared, context, fmt.Sprintf("c%d", compared))
		comparison := EqDatatype(x, constructor)
		if !equality {
			comparison = Not(comparison)
		}
		formula := And(IsDatatypeConstructor(77, constructorCount, forced, x), comparison)
		result := Check(Assert(example+1, NewSolver(context), formula))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}

		var script strings.Builder
		script.WriteString("(set-logic QF_DT)\n(declare-datatype D (")
		for constructorID := 0; constructorID < constructorCount; constructorID++ {
			fmt.Fprintf(&script, " (c%d)", constructorID)
		}
		script.WriteString("))\n(declare-const x D)\n")
		fmt.Fprintf(&script, "(assert (is-c%d x))\n", forced)
		if equality {
			fmt.Fprintf(&script, "(assert (= x c%d))\n", compared)
		} else {
			fmt.Fprintf(&script, "(assert (distinct x c%d))\n", compared)
		}
		script.WriteString("(check-sat)\n")
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script.String())
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s\n%s", example, ours, result, want, script.String())
		}
		if sat, ok := result.(Sat); ok {
			value, found := EvalDatatype(77, constructorCount, sat.Value, x)
			if !found || value.ConstructorID != forced {
				t.Fatalf("example %d: invalid datatype model %#v/%v", example, value, found)
			}
		}
	}
}

func TestRecursiveUnaryDatatypesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		forcedDepth := 1 + example%8
		comparedDepth := (example*5 + 3) % 8
		equality := example%2 == 0
		context := NewContext(153)
		zero := DatatypeConstructor(78, 2, 0, context, "zero")
		succ := DeclareRecursiveDatatypeConstructor(78, 2, 1, context, "succ", "pred")
		chain := func(depth int) DatatypeExpr {
			value := zero
			for step := 0; step < depth; step++ {
				value = ApplyRecursiveDatatypeConstructor(succ, value)
			}
			return value
		}
		x := DatatypeConst(78, 2, context, "x", 1)
		comparison := EqDatatype(SelectRecursiveDatatypeConstructor(succ, x), chain(comparedDepth))
		if !equality {
			comparison = Not(comparison)
		}
		formula := And(EqDatatype(x, chain(forcedDepth)), IsRecursiveDatatypeConstructor(succ, x), comparison)
		result := Check(Assert(example+1, NewSolver(context), formula))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}

		z3Chain := func(depth int) string {
			value := "zero"
			for step := 0; step < depth; step++ {
				value = "(succ " + value + ")"
			}
			return value
		}
		comparisonOperator := "="
		if !equality {
			comparisonOperator = "distinct"
		}
		script := fmt.Sprintf(`(set-logic QF_DT)
(declare-datatype Nat ((zero) (succ (pred Nat))))
(declare-const x Nat)
(assert (= x %s))
(assert (is-succ x))
(assert (%s (pred x) %s))
(check-sat)
`, z3Chain(forcedDepth), comparisonOperator, z3Chain(comparedDepth))
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
			value, found := EvalDatatype(78, 2, sat.Value, x)
			depth := 0
			for found && value.ConstructorID == 1 && value.Child != nil {
				depth++
				value = *value.Child
			}
			if !found || depth != forcedDepth || value.ConstructorID != 0 {
				t.Fatalf("example %d: invalid recursive datatype model depth=%d value=%#v/%v", example, depth, value, found)
			}
		}
	}
}

func TestBinaryRecursiveDatatypesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	for example := 0; example < 64; example++ {
		leftDepth := 1 + example%6
		rightDepth := (example * 3) % 6
		field := example % 2
		forcedDepth := leftDepth
		fieldWitness := FirstDatatypeField()
		if field == 1 {
			forcedDepth = rightDepth
			fieldWitness = SecondDatatypeField()
		}
		comparedDepth := (example*5 + 2) % 6
		equality := example%4 < 2
		context := NewContext(156)
		leaf := DatatypeConstructor(79, 2, 0, context, "leaf")
		node := DeclareBinaryRecursiveDatatypeConstructor(79, 2, 1, context, "node", "left", "right")
		chain := func(depth int) DatatypeExpr {
			value := leaf
			for step := 0; step < depth; step++ {
				value = ApplyBinaryRecursiveDatatypeConstructor(node, value, leaf)
			}
			return value
		}
		x := DatatypeConst(79, 2, context, "x", 1)
		tree := ApplyBinaryRecursiveDatatypeConstructor(node, chain(leftDepth), chain(rightDepth))
		comparison := EqDatatype(SelectBinaryRecursiveDatatypeConstructor(fieldWitness, node, x), chain(comparedDepth))
		if !equality {
			comparison = Not(comparison)
		}
		formula := And(EqDatatype(x, tree), IsBinaryRecursiveDatatypeConstructor(node, x), comparison)
		result := Check(Assert(example+1, NewSolver(context), formula))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}

		z3Chain := func(depth int) string {
			value := "leaf"
			for step := 0; step < depth; step++ {
				value = "(node " + value + " leaf)"
			}
			return value
		}
		selector := "left"
		if field == 1 {
			selector = "right"
		}
		comparisonOperator := "="
		if !equality {
			comparisonOperator = "distinct"
		}
		script := fmt.Sprintf(`(set-logic QF_DT)
(declare-datatype Tree ((leaf) (node (left Tree) (right Tree))))
(declare-const x Tree)
(assert (= x (node %s %s)))
(assert (is-node x))
(assert (%s (%s x) %s))
(check-sat)
`, z3Chain(leftDepth), z3Chain(rightDepth), comparisonOperator, selector, z3Chain(comparedDepth))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s forced=%d compared=%d\n%s", example, ours, result, want, forcedDepth, comparedDepth, script)
		}
		if sat, ok := result.(Sat); ok {
			value, found := EvalDatatype(79, 2, sat.Value, x)
			if !found || value.ConstructorID != 1 || value.Child == nil || value.SecondChild == nil {
				t.Fatalf("example %d: invalid binary model %#v/%v", example, value, found)
			}
		}
	}
}

func TestNaryRecursiveDatatypesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	fieldWitness := func(field int) vec.Fin {
		var result vec.Fin = vec.Zero{}
		for index := 0; index < field; index++ {
			result = vec.Succ{Prev: result}
		}
		return result
	}
	for example := 0; example < 64; example++ {
		depths := [3]int{1 + example%5, (example * 3) % 5, (example * 7) % 5}
		field := example % 3
		forcedDepth := depths[field]
		comparedDepth := (example*5 + 2) % 5
		equality := example%4 < 2
		context := NewContext(157)
		leaf := DatatypeConstructor(80, 2, 0, context, "leaf")
		branch := DeclareNaryRecursiveDatatypeConstructor(80, 2, 1, 3, context, "branch", narySelectorNames())
		chain := func(depth int) DatatypeExpr {
			value := leaf
			for step := 0; step < depth; step++ {
				value = ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(value, leaf, leaf))
			}
			return value
		}
		x := DatatypeConst(80, 2, context, "x", 1)
		tree := ApplyNaryRecursiveDatatypeConstructor(branch, naryDatatypeExpressions(chain(depths[0]), chain(depths[1]), chain(depths[2])))
		comparison := EqDatatype(SelectNaryRecursiveDatatypeConstructor(fieldWitness(field), branch, x), chain(comparedDepth))
		if !equality {
			comparison = Not(comparison)
		}
		formula := And(EqDatatype(x, tree), IsNaryRecursiveDatatypeConstructor(branch, x), comparison)
		result := Check(Assert(example+1, NewSolver(context), formula))
		ours := "sat"
		if _, ok := result.(Unsat); ok {
			ours = "unsat"
		} else if _, ok := result.(Unknown); ok {
			ours = "unknown"
		}

		z3Chain := func(depth int) string {
			value := "leaf"
			for step := 0; step < depth; step++ {
				value = "(branch " + value + " leaf leaf)"
			}
			return value
		}
		selectors := [3]string{"first", "second", "third"}
		comparisonOperator := "="
		if !equality {
			comparisonOperator = "distinct"
		}
		script := fmt.Sprintf(`(set-logic QF_DT)
(declare-datatype Tree ((leaf) (branch (first Tree) (second Tree) (third Tree))))
(declare-const x Tree)
(assert (= x (branch %s %s %s)))
(assert (is-branch x))
(assert (%s (%s x) %s))
(check-sat)
`, z3Chain(depths[0]), z3Chain(depths[1]), z3Chain(depths[2]), comparisonOperator, selectors[field], z3Chain(comparedDepth))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s", example, err, output)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s (%#v) z3=%s forced=%d compared=%d\n%s", example, ours, result, want, forcedDepth, comparedDepth, script)
		}
		if sat, ok := result.(Sat); ok {
			value, found := EvalDatatype(80, 2, sat.Value, x)
			if !found || value.ConstructorID != 1 || value.Children.Len() != 3 {
				t.Fatalf("example %d: invalid n-ary model %#v/%v", example, value, found)
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

func TestMixedDatatypeSMTLibAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	tests := []string{
		`(declare-datatype Tree ((leaf) (node (payload Int) (next Tree))))
(declare-const x Tree)
(assert (= x (node 42 leaf)))
(assert (= (payload x) 42))
(assert (is-node x))
(check-sat)`,
		`(declare-datatype Tree ((leaf) (node (payload Int) (next Tree))))
(assert (= (node 1 leaf) (node 2 leaf)))
(check-sat)`,
		`(declare-datatype Tree ((leaf) (node (flag Bool) (weight Real) (bits (_ BitVec 8)) (next Tree))))
(declare-const x Tree)
(assert (= x (node true (/ 3.0 2.0) #xa5 leaf)))
(assert (= (weight x) (/ 3.0 2.0)))
(assert (= (bits x) #xa5))
(check-sat)`,
		`(declare-datatype Box ((box (payload Int))))
(declare-const x Box)
(assert (= (payload x) 7))
(assert (is-box x))
(check-sat)`,
		`(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-const x Tree)
(assert (= x (node (cons leaf nil))))
(assert (= (head (children x)) leaf))
(assert (= (tail (children x)) nil))
(check-sat)`,
		`(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-const tree Tree)
(declare-const forest Forest)
(assert (= tree (node forest)))
(assert (= forest (cons tree nil)))
(check-sat)`,
	}
	for index, script := range tests {
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("case %d: run Z3: %v\n%s", index, err, output)
		}
		want := strings.Fields(string(output))
		if strings.Join(ours, " ") != strings.Join(want, " ") {
			t.Fatalf("case %d: gosmt=%v z3=%v\n%s", index, ours, want, script)
		}
	}
}

func TestMutuallyRecursiveDatatypeCorpusAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	var script strings.Builder
	script.WriteString(`(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (children Forest)))
   ((nil) (cons (head Tree) (tail Forest)))))
(declare-const x Tree)
`)
	for example := 0; example < 64; example++ {
		left := mutualTreeTerm(4, uint64(example*17+5))
		right := left
		if example%2 != 0 {
			right = mutualTreeTerm(4, uint64(example*31+19))
		}
		fmt.Fprintf(&script, "(push 1)\n(assert (= x %s))\n(assert (= x %s))\n(check-sat)\n(pop 1)\n", left, right)
	}
	source := script.String()
	ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(source))
	command := exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(source)
	output, err := command.CombinedOutput()
	if err != nil {
		t.Fatalf("run Z3: %v\n%s", err, output)
	}
	want := strings.Fields(string(output))
	if strings.Join(ours, " ") != strings.Join(want, " ") {
		t.Fatalf("mutual corpus mismatch: gosmt=%v z3=%v\n%s", ours, want, source)
	}
}

func mutualTreeTerm(depth int, seed uint64) string {
	if depth == 0 || seed%3 == 0 {
		return "leaf"
	}
	return "(node " + mutualForestTerm(depth-1, seed/3+7) + ")"
}

func mutualForestTerm(depth int, seed uint64) string {
	if depth == 0 || seed%4 == 0 {
		return "nil"
	}
	return "(cons " + mutualTreeTerm(depth-1, seed/5+11) + " " + mutualForestTerm(depth-1, seed/7+13) + ")"
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

func TestGroundFloatingPointPredicatesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	bits := []uint64{
		0x00000000, 0x80000000,
		0x7f800000, 0xff800000,
		0x7fc00000, 0xffc00000,
		0x00000001, 0x007fffff,
		0x00800000, 0x3f800000,
	}
	random := rand.New(rand.NewSource(0x4650))
	for len(bits) < 74 {
		bits = append(bits, uint64(random.Uint32()))
	}
	var script strings.Builder
	script.WriteString("(set-logic QF_FP)\n")
	predicate := func(name string, literal string, want bool) {
		if want {
			fmt.Fprintf(&script, "(assert (%s %s))\n", name, literal)
		} else {
			fmt.Fprintf(&script, "(assert (not (%s %s)))\n", name, literal)
		}
	}
	for _, pattern := range bits {
		value := smt.FloatingPointFromUint64(8, 24, pattern)
		literal := smtLIBFloat32(pattern)
		predicate("fp.isNaN", literal, smt.FloatingPointIsNaN(value))
		predicate("fp.isInfinite", literal, smt.FloatingPointIsInfinite(value))
		predicate("fp.isZero", literal, smt.FloatingPointIsZero(value))
		predicate("fp.isSubnormal", literal, smt.FloatingPointIsSubnormal(value))
		predicate("fp.isNormal", literal, smt.FloatingPointIsNormal(value))
		predicate("fp.isNegative", literal, smt.FloatingPointIsNegative(value))
		predicate("fp.isPositive", literal, smt.FloatingPointIsPositive(value))
	}
	pairs := [][2]uint64{
		{0x00000000, 0x80000000},
		{0x7fc00000, 0x7fc00000},
		{0x3f800000, 0x3f800000},
		{0x3f800000, 0x40000000},
	}
	for _, pair := range pairs {
		left := smt.FloatingPointFromUint64(8, 24, pair[0])
		right := smt.FloatingPointFromUint64(8, 24, pair[1])
		expression := fmt.Sprintf("(fp.eq %s %s)", smtLIBFloat32(pair[0]), smtLIBFloat32(pair[1]))
		if smt.FloatingPointEqual(left, right) {
			fmt.Fprintf(&script, "(assert %s)\n", expression)
		} else {
			fmt.Fprintf(&script, "(assert (not %s))\n", expression)
		}
	}
	script.WriteString("(check-sat)\n")
	command := exec.Command(z3, "-in", "-smt2")
	command.Stdin = strings.NewReader(script.String())
	output, err := command.CombinedOutput()
	if err != nil {
		t.Fatalf("run Z3: %v\n%s\n%s", err, output, script.String())
	}
	if got := strings.TrimSpace(string(output)); got != "sat" {
		t.Fatalf("Z3=%q\n%s", got, script.String())
	}
}

func TestSymbolicFloatingPointPredicatesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	predicates := []struct {
		name  string
		apply func(FloatingPointExpr) BoolExpr
	}{
		{"fp.isNaN", FloatingPointIsNaN},
		{"fp.isInfinite", FloatingPointIsInfinite},
		{"fp.isZero", FloatingPointIsZero},
		{"fp.isSubnormal", FloatingPointIsSubnormal},
		{"fp.isNormal", FloatingPointIsNormal},
		{"fp.isNegative", FloatingPointIsNegative},
		{"fp.isPositive", FloatingPointIsPositive},
	}
	random := rand.New(rand.NewSource(0x46505359))
	for example := 0; example < 64; example++ {
		pattern := uint64(random.Uint32())
		predicate := predicates[example%len(predicates)]
		positive := example%2 == 0
		context := NewContext(170 + example)
		value := FloatingPointConst(8, 24, context, "x", 1)
		fixed := FloatingPointFromUint64(8, 24, context, pattern)
		classification := predicate.apply(value)
		if !positive {
			classification = Not(classification)
		}
		formula := And(
			EqBitVec(FloatingPointBits(value), FloatingPointBits(fixed)),
			classification,
		)
		ours := floatingPointResultStatus(Check(Assert(1, NewSolver(context), formula)))
		operator := ""
		if !positive {
			operator = "(not "
		}
		close := ""
		if !positive {
			close = ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const x (_ FloatingPoint 8 24))\n(assert (= x %s))\n(assert %s(%s x)%s)\n(check-sat)\n",
			smtLIBFloat32(pattern), operator, predicate.name, close,
		)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, ours, want, script)
		}
	}
}

func TestSMTLibFloatingPointPredicatesAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	predicates := []string{
		"fp.isNaN", "fp.isInfinite", "fp.isZero", "fp.isSubnormal",
		"fp.isNormal", "fp.isNegative", "fp.isPositive",
	}
	random := rand.New(rand.NewSource(0x534d5443))
	for example := 0; example < 64; example++ {
		pattern := uint64(random.Uint32())
		switch example % 16 {
		case 0:
			pattern = 0
		case 1:
			pattern = 0x80000000
		case 2:
			pattern = 0x7f800000
		case 3:
			pattern = 0xff800000
		case 4:
			pattern = 0x7fc12345
		case 5:
			pattern = 1
		}
		predicate := predicates[example%len(predicates)]
		assertion := fmt.Sprintf("(%s x)", predicate)
		if example%2 != 0 {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const x (_ FloatingPoint 8 24))\n(assert (= (fp.to_ieee_bv x) #x%08x))\n(assert %s)\n(check-sat)\n",
			uint32(pattern), assertion,
		)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d (%s): gosmt=%s z3=%s\n%s", example, predicate, got, want, script)
		}
	}
}

func TestSMTLibFloatingPointEqualityAndOrderAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	operators := []string{"fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"}
	random := rand.New(rand.NewSource(0x534d544f))
	for example := 0; example < 64; example++ {
		left := uint64(random.Uint32())
		right := uint64(random.Uint32())
		switch example % 16 {
		case 0:
			left, right = 0, 0x80000000
		case 1:
			left, right = 0x7fc12345, 0x7fc12345
		case 2:
			left, right = 0xbf800000, 0x3f800000
		case 3:
			left, right = 0xff800000, 0x7f800000
		}
		operator := operators[example%len(operators)]
		assertion := fmt.Sprintf("(%s left right)", operator)
		if example%2 != 0 {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const left (_ FloatingPoint 8 24))\n(declare-const right (_ FloatingPoint 8 24))\n(assert (= (fp.to_ieee_bv left) #x%08x))\n(assert (= (fp.to_ieee_bv right) #x%08x))\n(assert %s)\n(check-sat)\n",
			uint32(left), uint32(right), assertion,
		)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d (%s): gosmt=%s z3=%s\n%s", example, operator, got, want, script)
		}
	}
}

func TestSMTLibFloatingPointUnaryAndMinMaxAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x534d5455))
	for example := 0; example < 64; example++ {
		leftPattern := uint64(random.Uint32())
		rightPattern := uint64(random.Uint32())
		if leftPattern&0x7f800000 == 0x7f800000 &&
			leftPattern&0x007fffff != 0 {
			leftPattern &= 0xff800000
		}
		if rightPattern&0x7f800000 == 0x7f800000 &&
			rightPattern&0x007fffff != 0 {
			rightPattern &= 0xff800000
		}
		switch example % 16 {
		case 0:
			leftPattern, rightPattern = 0xbf800000, 0x3f800000
		case 1:
			leftPattern, rightPattern = 0xff800000, 0x7f800000
		case 2:
			leftPattern, rightPattern = 1, 0x80000001
		}
		left := smt.FloatingPointFromUint64(8, 24, leftPattern)
		right := smt.FloatingPointFromUint64(8, 24, rightPattern)
		operator := "fp.abs"
		selected := smt.FloatingPointAbs(left)
		expression := "(fp.abs left)"
		switch example % 4 {
		case 1:
			operator = "fp.neg"
			selected = smt.FloatingPointNeg(left)
			expression = "(fp.neg left)"
		case 2:
			operator = "fp.min"
			selected = smt.FloatingPointMin(left, right)
			expression = "(fp.min left right)"
		case 3:
			operator = "fp.max"
			selected = smt.FloatingPointMax(left, right)
			expression = "(fp.max left right)"
		}
		expectedBits, _ := smt.FloatingPointBits(selected).Uint64()
		assertion := fmt.Sprintf(
			"(= (fp.to_ieee_bv %s) #x%08x)",
			expression, uint32(expectedBits),
		)
		if example%8 >= 4 {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const left (_ FloatingPoint 8 24))\n(declare-const right (_ FloatingPoint 8 24))\n(assert (= (fp.to_ieee_bv left) #x%08x))\n(assert (= (fp.to_ieee_bv right) #x%08x))\n(assert %s)\n(check-sat)\n",
			uint32(leftPattern), uint32(rightPattern), assertion,
		)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d (%s): gosmt=%s z3=%s\n%s", example, operator, got, want, script)
		}
	}
}

func TestSMTLibFloatingPointConstructionAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x46504354))
	for example := 0; example < 64; example++ {
		pattern := random.Uint32()
		sign := pattern >> 31
		exponent := pattern >> 23 & 0xff
		significand := pattern & 0x7fffff
		name := "fp"
		assertion := fmt.Sprintf(
			"(= (fp.to_ieee_bv (fp #b%d #x%02x #b%023b)) #x%08x)",
			sign, exponent, significand, pattern,
		)
		switch example % 6 {
		case 1:
			name, assertion = "+zero", "(fp.isZero (_ +zero 8 24))"
		case 2:
			name, assertion = "-zero", "(= (fp.to_ieee_bv (_ -zero 8 24)) #x80000000)"
		case 3:
			name, assertion = "+oo", "(fp.isInfinite (_ +oo 8 24))"
		case 4:
			name, assertion = "-oo", "(fp.isNegative (_ -oo 8 24))"
		case 5:
			name, assertion = "NaN", "(fp.isNaN (_ NaN 8 24))"
		}
		if example%12 >= 6 {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(assert %s)\n(check-sat)\n",
			assertion,
		)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d (%s): gosmt=%s z3=%s\n%s", example, name, got, want, script)
		}
	}
}

func TestSymbolicFloatingPointEqualityAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x46504551))
	for example := 0; example < 64; example++ {
		leftPattern := uint64(random.Uint32())
		rightPattern := uint64(random.Uint32())
		if example%8 == 0 {
			rightPattern = leftPattern
		}
		if example%16 == 0 {
			leftPattern, rightPattern = 0, 0x80000000
		}
		if example%16 == 8 {
			leftPattern, rightPattern = 0x7fc00000, 0x7fc00000
		}
		context := NewContext(270 + example)
		left := FloatingPointConst(8, 24, context, "left", 1)
		right := FloatingPointConst(8, 24, context, "right", 2)
		formula := And(
			EqBitVec(FloatingPointBits(left), FloatingPointBits(FloatingPointFromUint64(8, 24, context, leftPattern))),
			EqBitVec(FloatingPointBits(right), FloatingPointBits(FloatingPointFromUint64(8, 24, context, rightPattern))),
			FloatingPointEqual(left, right),
		)
		ours := floatingPointResultStatus(Check(Assert(1, NewSolver(context), formula)))
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const left (_ FloatingPoint 8 24))\n(declare-const right (_ FloatingPoint 8 24))\n(assert (= left %s))\n(assert (= right %s))\n(assert (fp.eq left right))\n(check-sat)\n",
			smtLIBFloat32(leftPattern), smtLIBFloat32(rightPattern),
		)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, ours, want, script)
		}
	}
}

func TestSymbolicFloatingPointAbsAndNegAgreeWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x4650554e))
	for example := 0; example < 64; example++ {
		pattern := uint64(random.Uint32())
		operation, expected := "fp.abs", pattern&0x7fffffff
		apply := FloatingPointAbs
		if example%2 != 0 {
			operation, expected = "fp.neg", pattern^0x80000000
			apply = FloatingPointNeg
		}
		positive := example%4 < 2
		context := NewContext(370 + example)
		value := FloatingPointConst(8, 24, context, "x", 1)
		transformed := apply(value)
		relation := EqBitVec(
			FloatingPointBits(transformed),
			BitVecValue(32, context, expected),
		)
		if !positive {
			relation = Not(relation)
		}
		formula := And(
			EqBitVec(
				FloatingPointBits(value),
				FloatingPointBits(FloatingPointFromUint64(8, 24, context, pattern)),
			),
			relation,
		)
		ours := floatingPointResultStatus(Check(Assert(1, NewSolver(context), formula)))
		assertion := fmt.Sprintf(
			"(= (fp.to_ieee_bv (%s x)) #x%08x)", operation, uint32(expected),
		)
		if !positive {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FPBV)\n(declare-const x (_ FloatingPoint 8 24))\n(assert (= x ((_ to_fp 8 24) #x%08x)))\n(assert %s)\n(check-sat)\n",
			uint32(pattern), assertion,
		)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, ours, want, script)
		}
	}
}

func TestSymbolicFloatingPointOrderingAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	operations := []struct {
		name  string
		apply func(FloatingPointExpr, FloatingPointExpr) BoolExpr
	}{
		{"fp.lt", FloatingPointLessThan},
		{"fp.leq", FloatingPointLessOrEqual},
		{"fp.gt", FloatingPointGreaterThan},
		{"fp.geq", FloatingPointGreaterOrEqual},
	}
	random := rand.New(rand.NewSource(0x46504f52))
	for example := 0; example < 64; example++ {
		leftPattern := uint64(random.Uint32())
		rightPattern := uint64(random.Uint32())
		if example%16 == 0 {
			leftPattern, rightPattern = 0x80000000, 0
		}
		if example%16 == 4 {
			leftPattern = 0x7fc00000
		}
		operation := operations[example%len(operations)]
		positive := example%8 < 4
		context := NewContext(470 + example)
		left := FloatingPointConst(8, 24, context, "left", 1)
		right := FloatingPointConst(8, 24, context, "right", 2)
		relation := operation.apply(left, right)
		if !positive {
			relation = Not(relation)
		}
		formula := And(
			EqBitVec(
				FloatingPointBits(left),
				FloatingPointBits(FloatingPointFromUint64(8, 24, context, leftPattern)),
			),
			EqBitVec(
				FloatingPointBits(right),
				FloatingPointBits(FloatingPointFromUint64(8, 24, context, rightPattern)),
			),
			relation,
		)
		ours := floatingPointResultStatus(Check(Assert(1, NewSolver(context), formula)))
		assertion := fmt.Sprintf("(%s left right)", operation.name)
		if !positive {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const left (_ FloatingPoint 8 24))\n(declare-const right (_ FloatingPoint 8 24))\n(assert (= left ((_ to_fp 8 24) #x%08x)))\n(assert (= right ((_ to_fp 8 24) #x%08x)))\n(assert %s)\n(check-sat)\n",
			uint32(leftPattern), uint32(rightPattern), assertion,
		)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, ours, want, script)
		}
	}
}

func TestSymbolicFloatingPointMinMaxAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	random := rand.New(rand.NewSource(0x46504d4d))
	for example := 0; example < 64; example++ {
		leftPattern := uint64(random.Uint32())
		rightPattern := uint64(random.Uint32())
		if example%16 == 0 {
			leftPattern, rightPattern = 0, 0x80000000
		}
		if example%16 == 4 {
			leftPattern = 0x7fc12345
		}
		if example%16 == 8 {
			leftPattern, rightPattern = 0x7fc12345, 0xffc54321
		}
		operation := "fp.min"
		apply := FloatingPointMin
		coreApply := smt.FloatingPointMin
		if example%2 != 0 {
			operation = "fp.max"
			apply = FloatingPointMax
			coreApply = smt.FloatingPointMax
		}
		leftCore := smt.FloatingPointFromUint64(8, 24, leftPattern)
		rightCore := smt.FloatingPointFromUint64(8, 24, rightPattern)
		expectedCore := coreApply(leftCore, rightCore)
		expectedBits, _ := smt.FloatingPointBits(expectedCore).Uint64()
		positive := example%4 < 2
		context := NewContext(570 + example)
		left := FloatingPointConst(8, 24, context, "left", 1)
		right := FloatingPointConst(8, 24, context, "right", 2)
		selected := apply(left, right)
		relation := EqBitVec(
			FloatingPointBits(selected),
			BitVecValue(32, context, expectedBits),
		)
		if !positive {
			relation = Not(relation)
		}
		formula := And(
			EqBitVec(
				FloatingPointBits(left),
				FloatingPointBits(FloatingPointFromUint64(8, 24, context, leftPattern)),
			),
			EqBitVec(
				FloatingPointBits(right),
				FloatingPointBits(FloatingPointFromUint64(8, 24, context, rightPattern)),
			),
			relation,
		)
		ours := floatingPointResultStatus(Check(Assert(1, NewSolver(context), formula)))
		selectedText := fmt.Sprintf("(%s left right)", operation)
		assertion := fmt.Sprintf("(fp.eq %s %s)", selectedText, smtLIBFloat32(expectedBits))
		if smt.FloatingPointIsNaN(expectedCore) {
			assertion = fmt.Sprintf("(fp.isNaN %s)", selectedText)
		}
		if !positive {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const left (_ FloatingPoint 8 24))\n(declare-const right (_ FloatingPoint 8 24))\n(assert (= left ((_ to_fp 8 24) #x%08x)))\n(assert (= right ((_ to_fp 8 24) #x%08x)))\n(assert %s)\n(check-sat)\n",
			uint32(leftPattern), uint32(rightPattern), assertion,
		)
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d: gosmt=%s z3=%s\n%s", example, ours, want, script)
		}
	}
}

func TestSymbolicFloatingPointRoundToIntegralAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	modes := []struct {
		name string
		core smt.FloatingPointRoundingMode
	}{
		{"RNE", smt.RoundNearestTiesToEven()},
		{"RNA", smt.RoundNearestTiesToAway()},
		{"RTP", smt.RoundTowardPositive()},
		{"RTN", smt.RoundTowardNegative()},
		{"RTZ", smt.RoundTowardZero()},
	}
	random := rand.New(rand.NewSource(0x46505249))
	for example := 0; example < 64; example++ {
		pattern := uint64(random.Uint32())
		switch example % 16 {
		case 0:
			pattern = 0
		case 1:
			pattern = 0x80000000
		case 2:
			pattern = 0x3fc00000
		case 3:
			pattern = 0xbfc00000
		case 4:
			pattern = 0x7f800000
		case 5:
			pattern = 0xff800000
		case 6:
			pattern = 0x7fc12345
		}
		mode := modes[example%len(modes)]
		sourceCore := smt.FloatingPointFromUint64(8, 24, pattern)
		expectedCore := smt.FloatingPointRoundToIntegral(mode.core, sourceCore)
		expectedBits, _ := smt.FloatingPointBits(expectedCore).Uint64()
		positive := example%4 < 2

		context := NewContext(700 + example)
		source := FloatingPointConst(8, 24, context, "source", 1)
		rounded := FloatingPointRoundToIntegral(mode.core, source)
		relation := EqBitVec(
			FloatingPointBits(rounded),
			BitVecValue(32, context, expectedBits),
		)
		if !positive {
			relation = Not(relation)
		}
		formula := And(
			EqBitVec(
				FloatingPointBits(source),
				FloatingPointBits(FloatingPointFromUint64(8, 24, context, pattern)),
			),
			relation,
		)
		ours := floatingPointResultStatus(Check(Assert(1, NewSolver(context), formula)))
		selected := fmt.Sprintf("(fp.roundToIntegral %s source)", mode.name)
		assertion := fmt.Sprintf(
			"(= (fp.to_ieee_bv %s) #x%08x)", selected, uint32(expectedBits),
		)
		if smt.FloatingPointIsNaN(expectedCore) {
			assertion = fmt.Sprintf("(fp.isNaN %s)", selected)
		}
		if !positive {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const source (_ FloatingPoint 8 24))\n(assert (= source ((_ to_fp 8 24) #x%08x)))\n(assert %s)\n(check-sat)\n",
			uint32(pattern), assertion,
		)
		command := exec.Command(z3, "-in")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: run Z3: %v\n%s\n%s", example, err, output, script)
		}
		if want := strings.TrimSpace(string(output)); ours != want {
			t.Fatalf("example %d (%s): gosmt=%s z3=%s\n%s", example, mode.name, ours, want, script)
		}
	}
}

func TestSMTLibFloatingPointRoundToIntegralAgreesWithPinnedZ3(t *testing.T) {
	z3 := os.Getenv("GOSMT_Z3")
	if z3 == "" {
		t.Skip("set GOSMT_Z3 to the pinned Z3 4.16.0 binary")
	}
	modes := []struct {
		name string
		core smt.FloatingPointRoundingMode
	}{
		{"RNE", smt.RoundNearestTiesToEven()},
		{"RNA", smt.RoundNearestTiesToAway()},
		{"RTP", smt.RoundTowardPositive()},
		{"RTN", smt.RoundTowardNegative()},
		{"RTZ", smt.RoundTowardZero()},
	}
	random := rand.New(rand.NewSource(0x534d5446))
	for example := 0; example < 64; example++ {
		pattern := uint64(random.Uint32())
		if pattern&0x7f800000 == 0x7f800000 && pattern&0x007fffff != 0 {
			pattern &= 0xff800000
		}
		switch example % 16 {
		case 0:
			pattern = 0
		case 1:
			pattern = 0x80000000
		case 2:
			pattern = 0x3fc00000
		case 3:
			pattern = 0xbfc00000
		case 4:
			pattern = 0x7f800000
		case 5:
			pattern = 0xff800000
		}
		mode := modes[example%len(modes)]
		source := smt.FloatingPointFromUint64(8, 24, pattern)
		expected := smt.FloatingPointRoundToIntegral(mode.core, source)
		expectedBits, _ := smt.FloatingPointBits(expected).Uint64()
		assertion := fmt.Sprintf(
			"(= (fp.to_ieee_bv (fp.roundToIntegral %s source)) #x%08x)",
			mode.name, uint32(expectedBits),
		)
		if example%4 >= 2 {
			assertion = "(not " + assertion + ")"
		}
		script := fmt.Sprintf(
			"(set-logic QF_FP)\n(declare-const source (_ FloatingPoint 8 24))\n(assert (= (fp.to_ieee_bv source) #x%08x))\n(assert %s)\n(check-sat)\n",
			uint32(pattern), assertion,
		)
		ours := smtLIBExecutionStatuses(t, ExecuteSMTLib(script))
		command := exec.Command(z3, "-in", "-smt2")
		command.Stdin = strings.NewReader(script)
		output, err := command.CombinedOutput()
		if err != nil {
			t.Fatalf("example %d: Z3: %v\n%s\n%s", example, err, output, script)
		}
		if got, want := fmt.Sprint(ours), "["+strings.TrimSpace(string(output))+"]"; got != want {
			t.Fatalf("example %d (%s): gosmt=%s z3=%s\n%s", example, mode.name, got, want, script)
		}
	}
}

func floatingPointResultStatus(result Result) string {
	switch result.(type) {
	case Sat:
		return "sat"
	case Unsat:
		return "unsat"
	default:
		return "unknown"
	}
}

func smtLIBFloat32(pattern uint64) string {
	bits := fmt.Sprintf("%032b", uint32(pattern))
	return fmt.Sprintf("(fp #b%s #b%s #b%s)", bits[:1], bits[1:9], bits[9:])
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
