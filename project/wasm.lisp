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
			  and32 or32 xor32
			  eq32 ne32 lt_s32 lt_u32 gt_u32 gt_s32 le_u32 le_s32 ge_u32 ge_s32)))

;; binary operations on 64-bit nums,

(defdata i64binop (enum '(add64 sub64 mul64 div_u64 rem_u64 div_s64 rem_s64
			  and64 or64 xor64
			  eq64 ne64 lt_s64 lt_u64 gt_u64 gt_s64 le_u64 le_s64 ge_u64 ge_s64)))

;; or a nop keyword (specifying no operation).

(defdata nop 'nop)

;; which lets us finally define our set of wasm instructions for now.

(defdata instr (oneof const i32unop i64unop i32binop i64binop nop))


;; we can represent a wasm function as a list of wasm instructions.
;; right now, we only support functions that take in no parameters 

(defdata wasm-function (listof instr))

;; a wasm module is a list of wasm functions

(defdata wasm-module (listof wasm-function))

;; since wasm is stack-based, we also define a stack.

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

(definec bit-listp (l :tl) :bool
       (cond ((atom l) (eq l nil))
             (t (and (bitp (car l))
                     (bit-listp (cdr l))))))

;; integer to bits as a tl 
(definec int-to-bits-helper (x :int b :tl) :tl
  (if (> x 1)
      (int-to-bits-helper (truncate x 2) (append (list (rem x 2)) b))
    (append (list x) b)))
(definec int-to-bits (x :int) :tl
  (int-to-bits-helper x nil))

;; bits to integer 
(definec bits-to-int-helper (bits :tl ct :nat ret :int) :int
  :skip-admissibilityp t
  :skip-body-contractsp t
  (if (or (not (bit-listp bits)) (> ct 64)) 0
    (if (or (= ct 63) (not (nth ct bits))) ret
      (bits-to-int-helper bits (+ ct 1) (+ (* (nth ct bits) (expt 2 ct)) ret)))))

(definec bits-to-int (bits :tl) :int
  (bits-to-int-helper (rev bits) 0 0))


(definec count-trailing-zeros-helper (bits :tl) :nat
  :skip-admissibilityp t
  (if (not (bit-listp bits)) 0 
  (match bits
    (nil 0)
    ((f . r) (if (zerop f) (+ 1 (count-trailing-zeros r)) 0)))))

(definec count-trailing-zeros (bits :tl) :nat
  (count-trailing-zeros-helper (rev bits)))

(definec count-non-zero-bits (bits :tl) :nat
  (if (or (= 1 (car bits)) (= 0 (car bits)))
      (+ (car bits) (count-non-zero-bits (cdr bits)))
    0))


(definec wasm-eval-h-i32unop (i :i32unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not (and (not x) (i32p x))) "not enough variables declared to do i32unop!"
      (match i
	('eqz32 (cons (if (zerop x) 1 0) (cdr s))) 
	;; clz gives you the count of leading zeros 
	('clz32 (cons (- 32 (length (int-to-bits x))) (cdr s)))
	;; ctz gives you the count of trailing zero bits 
	('ctz32 (cons (count-trailing-zeros (int-to-bits x)) (cdr s)))
	;; popcnt returns the count of non-zero bits 
	('popcnt32 (cons (count-non-zero-bits (int-to-bits x)) (cdr s)))
	;; wrap (64, 32) = return x modulo 2^32
	('wrap64 (cons (rem x (expt 2 32)) (cdr s)))))))


;; invert all the bits
(definec invert-bits (bits :tl) :tl
  (if (consp bits)
      (if (== 0 (car bits))
	  (cons 1 (invert-bits (cdr bits)))
	  (cons 0 (invert-bits (cdr bits))))
      nil))

;; this takes the reverse of bits as input 
(definec twos-complement-helper (bits :tl carry :nat) :tl
  (if (consp bits)
      (if (== 0 (car bits)) ;; I should technically write this in match but i don't trust match 
	  (if (== 0 carry)
	      (append (twos-complement-helper (cdr bits) 0) '(0))
	    (append (twos-complement-helper (cdr bits) 0) '(1)))
	(if (== 0 carry)
	    (append (twos-complement-helper (cdr bits) 0) '(1))
          (append (twos-complement-helper (cdr bits) 1) '(0))))
    nil))
    
;; invert all the bits and then add 1
(definec twos-complement (bits :tl) :tl
  (twos-complement-helper (rev (invert-bits bits)) 1))
	

;; if the value is between 0 and 2^31 then return the value
;; else return the integer value of the twos complement of i
(definec sign-interpretation-32 (i :i32) :i32
  :skip-function-contractp t
  (if (and (>= i 0) (< i (expt 2 31)))
      i
      (bits-to-int (twos-complement (int-to-bits i)))))

(definec wasm-eval-h-i64unop (i :i64unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not (and (not x) (i64p x))) "not enough variables declared to do i64unop!"
      (match i
	('eqz64 (cons (if (zerop x) 1 0) (cdr s))) 
	('clz64 (cons (- 64 (length (int-to-bits x))) (cdr s)))
	('ctz64 (cons (count-trailing-zeros (int-to-bits x)) (cdr s)))
	('popcnt64 (cons (count-non-zero-bits (int-to-bits x)) (cdr s)))
	;; extend_s(32,64) 
	;; let the j be the signed interpretation of x of size 32
	;; return the two's complement of j relative to size 64	
	('extend_s32 (cons (bits-to-int (twos-complement (int-to-bits (sign-interpretation-32 x)))) (cdr s)))
	;; extend_u(32,64): return x
	('extend_u32 (cons x (cdr s)))))))

;; bitwise and
(definec bit-and-h (x :tl y :tl ct :nat ret :tl) :int
  (if (= 0 ct) (bits-to-int ret) (bit-and-h x y (- ct 1) (cons (and (nth ct x) (nth ct y)) ret))))

(definec bits-and (x :i32 y :i32) :i32
  :skip-function-contractp t
  (let ((bx (rev (int-to-bits x)))
        (by (rev (int-to-bits y))))
    (bit-and-h bx by 31 nil)))

(definec bit-or-h (x :tl y :tl ct :nat ret :tl) :int
  (if (= 0 ct) (bits-to-int ret) (bit-and-h x y (- ct 1) (cons (or (nth ct x) (nth ct y)) ret))))

(definec bits-or (x :i32 y :i32) :i32
  :skip-function-contractp t
  (let ((bx (rev (int-to-bits x)))
        (by (rev (int-to-bits y))))
   (bit-and-h bx by 31 nil)))

(definec bit-xor-h (x :tl y :tl ct :nat ret :tl) :int
  (if (= 0 ct) (bits-to-int ret) (bit-and-h x y (- ct 1) (cons (xor (nth ct x) (nth ct y)) ret))))

(definec bits-xor (x :i32 y :i32) :i32
  :skip-function-contractp t
  (let ((bx (rev (int-to-bits x)))
        (by (rev (int-to-bits y))))
   (bit-and-h bx by 31 nil)))


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
	('div_s32 (let ((sx (sign-interpretation-32 x))
			 (sy (sign-interpretation-32 y)))
		     (if (zerop sy) "div by 0 error"
		       (if (= (truncate sx sy) (expt 2 31)) "signed div by 0 error" (cons (truncate sx sy) (cddr s))))))
	('rem_s32 (let ((sx (sign-interpretation-32 x))
			 (sy (sign-interpretation-32 y)))
		     (if (zerop sy) "rem by 0 error" (cons (rem sx sy) (cddr s)))))
	
	('and32 (cons (bit-and x y) (cddr s)))
	('or32 (cons (bit-or x y) (cddr s)))
	('xor32 (cons (bit-xor x y) (cddr s)))

	('eq32 if )
	('ne32 "TODO")
	('lt_s32 "TODO")
	('lt_u32 "TODO")
	('gt_u32 "TODO")
	('gt_s32 "TODO")
	('le_u32 "TODO")
	('le_s32 "TODO")
	('ge_u32 "TODO")
	('ge_s32 "TODO")	

	) "not i32 inputs!")))
  :timeout 300)

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
