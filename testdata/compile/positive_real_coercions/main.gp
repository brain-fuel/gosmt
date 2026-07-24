package compilefixture

import "goforge.dev/gosmt"

func AcceptedRealCoercions() {
	context := gosmt.NewContext(7)
	integer := gosmt.IntVal(context, 3)
	real := gosmt.RealVal(context, gosmt.Rational(3, 2))
	_ = gosmt.ToReal(integer)
	_ = gosmt.ToIntReal(real)
	_ = gosmt.IsIntReal(real)
}
