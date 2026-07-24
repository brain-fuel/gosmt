package compilefixture

import "goforge.dev/gosmt"

func RejectedRealCoercionContext() {
	leftContext := gosmt.NewContext(7)
	rightContext := gosmt.NewContext(8)
	integer := gosmt.IntVal(leftContext, 3)
	real := gosmt.RealVal(rightContext, gosmt.Rational(3, 1))
	_ = gosmt.EqReal(gosmt.ToReal(integer), real)
}
