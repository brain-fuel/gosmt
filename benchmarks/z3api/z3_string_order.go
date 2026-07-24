package z3api

/*
#include <stdint.h>
#include <z3.h>

static void *gosmt_z3_mk_str_lt(void *context, void *left, void *right) {
	return Z3_mk_str_lt((Z3_context)context, (Z3_ast)left, (Z3_ast)right);
}

static void *gosmt_z3_mk_str_le(void *context, void *left, void *right) {
	return Z3_mk_str_le((Z3_context)context, (Z3_ast)left, (Z3_ast)right);
}

static void *gosmt_z3_mk_char_string(void *context, unsigned code) {
	Z3_ast character = Z3_mk_char((Z3_context)context, code);
	return Z3_mk_seq_unit((Z3_context)context, character);
}

static void *gosmt_z3_mk_fpa_min(void *context, void *left, void *right) {
	return Z3_mk_fpa_min((Z3_context)context, (Z3_ast)left, (Z3_ast)right);
}

static void gosmt_z3_inc_ref(void *context, void *value) {
	Z3_inc_ref((Z3_context)context, (Z3_ast)value);
}

static void gosmt_z3_dec_ref(void *context, void *value) {
	Z3_dec_ref((Z3_context)context, (Z3_ast)value);
}
*/
import "C"

import (
	"runtime"
	"unsafe"

	z3 "github.com/Z3Prover/z3/src/api/go"
)

type z3ExpressionLayout struct {
	context *z3.Context
	pointer unsafe.Pointer
}

func z3StringLess(context *z3.Context, left, right *z3.Expr) *z3.Expr {
	return z3StringOrder(context, left, right, false)
}

func z3StringLessEqual(context *z3.Context, left, right *z3.Expr) *z3.Expr {
	return z3StringOrder(context, left, right, true)
}

func z3CharacterString(context *z3.Context, code uint32) *z3.Expr {
	contextPointer := *(*unsafe.Pointer)(unsafe.Pointer(context))
	return z3ManagedExpression(
		context,
		contextPointer,
		C.gosmt_z3_mk_char_string(contextPointer, C.uint(code)),
	)
}

func z3FloatingPointMin(context *z3.Context, left, right *z3.Expr) *z3.Expr {
	contextPointer := *(*unsafe.Pointer)(unsafe.Pointer(context))
	leftPointer := (*z3ExpressionLayout)(unsafe.Pointer(left)).pointer
	rightPointer := (*z3ExpressionLayout)(unsafe.Pointer(right)).pointer
	return z3ManagedExpression(
		context,
		contextPointer,
		C.gosmt_z3_mk_fpa_min(contextPointer, leftPointer, rightPointer),
	)
}

func z3StringOrder(
	context *z3.Context,
	left, right *z3.Expr,
	inclusive bool,
) *z3.Expr {
	contextPointer := *(*unsafe.Pointer)(unsafe.Pointer(context))
	leftPointer := (*z3ExpressionLayout)(unsafe.Pointer(left)).pointer
	rightPointer := (*z3ExpressionLayout)(unsafe.Pointer(right)).pointer
	var resultPointer unsafe.Pointer
	if inclusive {
		resultPointer = C.gosmt_z3_mk_str_le(contextPointer, leftPointer, rightPointer)
	} else {
		resultPointer = C.gosmt_z3_mk_str_lt(contextPointer, leftPointer, rightPointer)
	}
	return z3ManagedExpression(context, contextPointer, resultPointer)
}

func z3ManagedExpression(
	context *z3.Context,
	contextPointer unsafe.Pointer,
	resultPointer unsafe.Pointer,
) *z3.Expr {
	C.gosmt_z3_inc_ref(contextPointer, resultPointer)
	layout := &z3ExpressionLayout{context: context, pointer: resultPointer}
	result := (*z3.Expr)(unsafe.Pointer(layout))
	runtime.SetFinalizer(result, func(*z3.Expr) {
		C.gosmt_z3_dec_ref(contextPointer, resultPointer)
		runtime.KeepAlive(context)
	})
	return result
}
