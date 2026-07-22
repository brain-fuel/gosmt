package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	byteValue := gosmt.BitVecValue(8, context, 0xab)
	upperNibble := gosmt.ExtractBitVec(7, 4, byteValue)
	_ = gosmt.EqBitVec(upperNibble, byteValue)
}
