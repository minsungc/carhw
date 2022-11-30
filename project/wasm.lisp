;; WebAssembly 1.0 in ACL2
;; Minsung Cho, Michelle Thalakottur

;; We first define i32 and i64 types (no floats as ACL2 does not support them)
;; Instruction execution semantics can be found here: https://webassembly.github.io/JS-BigInt-integration/core/exec/numerics.html

(defdata i32 (range integer (0 <= _ < (expt 2 32))))
(defdata i64 (range integer (0 <= _ < (expt 2 64))))

;; we can define instructions as either:

;; constants,

(defdata const (oneof i32 i64))

#| 
These are the Unary Operations that we model: 
I32Eqz, I32Clz, I32Ctz, I32Popcnt, I32WrapI64
I64Eqz, I64Clz, I64Ctz, I64Popcnt, I64ExtendI32S, I64ExtendI32U

The following unary operations are not supported since ACL2 does not support floating points:
F32Abs, F32Neg, F32Ceil, F32Floor, F32Trunc, F32Nearest, F32Sqrt
F64Abs, F64Neg, F64Ceil, F64Floor, F64Trunc, F64Nearest, F64Sqrt
I32TruncF32S, I32TruncF32U, I32TruncF64S, I32TruncF64U
I64TruncF32S, I64TruncF32U, I64TruncF64S, I64TruncF64U
F32ConvertI32S, F32ConvertI32U, F32ConvertI64S, F32ConvertI64U, F32DemoteF64
F64ConvertI32S, F64ConvertI32U, F64ConvertI64S, F64ConvertI64U, F64PromoteF32
I32ReinterpretF32, I64ReinterpretF64, F32ReinterpretI32, F64ReinterpretI64
|#

;; unary operations on 32-bit nums,
  
(defdata i32unop (enum '(eqz32 clz32 ctz32 popcnt32 wrap64)))

;; unary operations on 64-bit nums,

(defdata i64unop (enum '(eqz64 clz64 ctz64 popcnt64 extend_s32 extend_u32)))

#| 
These are the Binary Operations that we model: 
- I32Eq, I32Ne, I32LtS, I32LtU, I32GtS, I32GtU, I32LeS, I32LeU, I32GeS, I32GeU
  I32Add, I32Sub, I32Mul, I32DivS, I32DivU, I32RemS, I32RemU, I32And, I32Or, I32Xor, I32Shl, I32ShrS, I32ShrU, I32Rotl, I32Rotr
- I64Eq, I64Ne, I64LtS, I64LtU, I64GtS, I64GtU, I64LeS, I64LeU, I64GeS, I64GeU
  I64Add, I64Sub, I64Mul, I64DivS, I64DivU, I64RemS, I64RemU, I64And, I64Or, I64Xor, I64Shl, I64ShrS, I64ShrU, I64Rotl, I64Rotr

The following binary operations are not supported since ACL2 does not support floating points:
F32Eq, F32Ne, F32Lt, F32Gt, F32Le, F32Ge
F64Eq, F64Ne, F64Lt, F64Gt, F64Le, F64Ge
F32Add, F32Sub, F32Mul, F32Div, F32Min, F32Max, F32Copysign
F64Add, F64Sub, F64Mul, F64Div, F64Min, F64Max, F64Copysign
|#

;; binary operations on 32-bit nums,

(defdata i32binop (enum '(add32 sub32 mul32 div_u32 rem_u32 div_s32 rem_s32
			  and32 or32 xor32 shl32 shr_u32 shr_s32 rotl32 rotr32
			  eq32 ne32 lt_s32 lt_u32 gt_u32 gt_s32 le_u32 le_s32 ge_u32 ge_s32)))

;; binary operations on 64-bit nums,

(defdata i64binop (enum '(add64 sub64 mul64 div_u64 rem_u64 div_s64 rem_s64
			  and64 or64 xor64 shl64 shr_u64 shr_s64 rotl64 rotr64
			  eq64 ne64 lt_s64 lt_u64 gt_u64 gt_s64 le_u64 le_s64 ge_u64 ge_s64)))

;; or a nop keyword (specifying no operation).

(defdata nop 'nop)

;; which lets us finally define our set of wasm instructions for now.

(defdata instr (oneof const i32unop i64unop i32binop i64binop nop))

;; we can represent a wasm program as a list of wasm instructions. since wasm is stack-based, we also define a stack.

(defdata wasm-program (listof instr))

(defdata stack (listof const))

;; to specify evaluation, we need to be able to throw exceptions. this will be done with the val-or-error sum type.

(defdata val-or-error (oneof const String))

#|
We want to define helper functions for wasm-eval, our evaluator. these will:
1. take in a wasm-program and a stack
2. either do the unary or binary operations necessary, or
3. throw an exception which will be handled by wasm-eval-h.

to do the either-or we define the type wasm-eval-h-out, 
which is a sum type of either an exception String or a program stack.
|#

(defdata wasm-eval-h-out (oneof String stack))


; returns a bit string of the integer passed in
(definec bits (x :int b :tl) :tl
  (if (> x 1)
      (bits (truncate x 2) (append (list (rem x 2)) b))
      (append (list x) b)  
  ))


(definec wasm-eval-h-i32unop (i :i32unop s :stack) :wasm-eval-h-out
  (let ((x (car s))
	;; (b (bits x nil))
	)
    (if (not x) "not enough variables declared to do i32unop!"
      (match i
	('eqz32 (cons (if (zerop x) 1 0) (cdr s))) 
        ('clz32 "TODO")
        ('ctz32 "TODO")
        ('popcnt32 "TODO")
	('wrap64 (cons x (cdr s)))))))


(definec wasm-eval-h-i64unop (i :i64unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not x) "not enough variables declared to do i64unop!"
      (match i
	('eqz64 (cons (zerop x) (cdr s)))
        ('clz64 "TODO")
        ('ctz64 "TODO")
        ('popcnt64 "TODO")
	('extend_s32 (cons (i32 x) (cdr s))) 
	('extend_u32 (cons (i32 x) (cdr s)))))))
  
(definec wasm-eval-h-i32binop (i :i32binop s :stack) :wasm-eval-h-out
  (let ((x (car s))
        (y (cadr s)))
    (if (or (not x) (not y))
      "not enough variables declared to do i32binop!"
      (if (and (i32p x) (i32p y))
      (match i
	('add32 (cons (rem (+ x y) (expt 2 32)) (cddr s)))
	('sub32 (cons (rem (+ (- x y) (expt 2 32)) (expt 2 32)) (cddr s)))
	('mul32 (cons (rem (* x y) (expt 2 32))(cddr s)))
	('div_u32 (if (zerop y) "div by 0 error" (cons (truncate x y) (cddr s))))
	('rem_u32 (if (zerop y) "rem by 0 error" (cons (rem x y) (cddr s))))
        ) "not i32 inputs!"))))

(definec wasm-eval-h-i64binop (i :i64binop s :stack) :wasm-eval-h-out
  (let ((x (car s))
        (y (cadr s)))
    (if (or (not x) (not y))
      "not enough variables declared to do i64binop!"
      (if (and (i64p x) (i64p y))
      (match i
	('add64 (cons (rem (+ x y) (expt 2 64)) (cddr s)))
	('sub64 (cons (rem (+ (- x y) (expt 2 64)) (expt 2 64)) (cddr s)))
	('mul64 (cons (rem (* x y) (expt 2 64))(cddr s)))
	('div_u64 (if (zerop y) "div by 0 error" (cons (truncate x y) (cddr s))))
	('rem_u64 (if (zerop y) "rem by 0 error" (cons (rem x y) (cddr s))))
        ) "not i64 inputs!"))))

(property (s :stack)
  (implies (not (equal s nil)) (val-or-errorp (car s))))

(property (s :string)
  (val-or-errorp s))

(definec wasm-eval-h (p :wasm-program s :stack) :val-or-error
  (match p
    (nil (match s
	   (nil "No value to be returned!")
	   (& (car s))))
    ((f . r) (match f
	       (:const (wasm-eval-h r (cons f s)))
	       (:i32unop
		(let ((x (wasm-eval-h-i32unop f s)))
		  (if (Stringp x) x (wasm-eval-h r x))))
	       (:i64unop
		(let ((x (wasm-eval-h-i64unop f s)))
		  (if (Stringp x) x (wasm-eval-h r x))))
	       (:i32binop
		(let ((x (wasm-eval-h-i32binop f s)))
		  (if (Stringp x) x (wasm-eval-h r x))))
	       (:i64binop
		(let ((x (wasm-eval-h-i64binop f s)))
		  (if (Stringp x) x (wasm-eval-h r x))))
	       (:nop (wasm-eval-h r s)))))
  :timeout 300)

(definec wasm-eval (p :wasm-program) :val-or-error
  (wasm-eval-h p nil))
