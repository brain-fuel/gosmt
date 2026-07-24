package compilefixture

import "goforge.dev/gosmt"

func RejectedRealTernaryContext() {
	leftContext := gosmt.NewContext(7)
	rightContext := gosmt.NewContext(8)
	function := gosmt.DeclareRealTernary(leftContext, "combine3", 1)
	left := gosmt.RealConst(leftContext, "left", 2)
	right := gosmt.RealConst(rightContext, "right", 3)
	_ = gosmt.ApplyRealTernary(function, left, left, right)
}
