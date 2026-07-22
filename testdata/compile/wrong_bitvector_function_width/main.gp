package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	function := gosmt.DeclareBitVecFunction(8, 4, context, "f", 1)
	nibble := gosmt.BitVecValue(4, context, 0xa)
	_ = gosmt.ApplyBitVecFunction(function, nibble)
}
