package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	nibble := gosmt.BitVecValue(4, context, 0xa)
	repeated := gosmt.RepeatBitVec(2, nibble)
	_ = gosmt.EqBitVec(repeated, nibble)
}
