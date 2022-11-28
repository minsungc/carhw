;; WebAssembly 1.0 in ACL2
;; Minsung Cho, Michelle Thalakottur

;; We first define i32 and i64 types (no floats as ACL2 does not support them)

(defdata i32 (range integer (_ < (expt 2 32))))
(defdata i64 (range integer (_ < (expt 2 64))))

;; we can define instructions as either:

;; constants,

(defdata const (oneof i32 i64))

;; unary operations on 32-bit nums,
  
(defdata i32unop (enum '(clz ctz popcnt)))

;; unary operations on 64-bit nums,

(defdata i64unop (enum '(clz ctz popcnt)))

;; binary operations on 32-bit nums,

(defdata i32binop (enum '(add sub mul div_u div_s rem_u rem_s and or xor shl shr_u shr_s rotl rotr)))

;; binary operations on 64-bit nums,

(defdata i64binop (enum '(add sub mul div_u div_s rem_u rem_s and or xor shl shr_u shr_s rotl rotr)))

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
which is a sum type of either an exception String or a wasm-program stack pair.
|#

(defdata wasm-eval-h-out (oneof String (list wasm-program stack)))

(definec wasm-eval-h-i32unop (i :i32unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not x) "not enough variables declared to do i32unop!"
      (match i
        ('clz "TODO")
        ('ctz "TODO")
        ('popcnt "TODO")))))

(definec wasm-eval-h-i64unop (i :i64unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not x) "not enough variables declared to do i64unop!"
      (match i
        ('clz "TODO")
        ('ctz "TODO")
        ('popcnt "TODO")))))

(definec wasm-eval-h-i64binop (i :i64binop s :stack) :wasm-eval-h-out
  (let ((x (car s))
        (y (cadr s)))
    (if (or (not x) (not y))
      "not enough variables declared to do i64binop!"
      (match i
	('add "TODO")
	('sub "TODO")
	('mul "TODO")
	('div_u "TODO")
	('div_s "TODO")
	('rem_u "TODO")
	('rem_s "TODO")
	('and "TODO")
	('or "TODO")
	('xor "TODO")
	('shl "TODO")
	('shr_u "TODO")
	('shr_s "TODO")
	('rotl "TODO")
	('rotr "TODO")))))

(definec wasm-eval-h-i32binop (i :i32binop s :stack) :wasm-eval-h-out
  (let ((x (car s))
        (y (cadr s)))
    (if (or (not x) (not y))
      "not enough variables declared to do i32binop!"
      (match i
	('add "TODO")
	('sub "TODO")
	('mul "TODO")
	('div_u "TODO")
	('div_s "TODO")
	('rem_u "TODO")
	('rem_s "TODO")
	('and "TODO")
	('or "TODO")
	('xor "TODO")
	('shl "TODO")
	('shr_u "TODO")
	('shr_s "TODO")
	('rotl "TODO")
	('rotr "TODO")))))

(definec wasm-eval-h (p :wasm-program s :stack) :val-or-error
  (match p
    (nil (match s
	   (nil "No value to be returned!")
	   (& (car s))))
    ((f . r) (match f
	       (:const (wasm-eval-h r (cons f s)))
	       (:i32unop
		(let ((x (wasm-eval-h-i32unop f s)))
		  (if (Stringp x) x (wasm-eval-h r (cadr x)))))
	       (:i64unop
		(let ((x (wasm-eval-h-i64unop f s)))
		  (if (Stringp x) x (wasm-eval-h r (cadr x)))))
	       (:i32binop
		(let ((x (wasm-eval-h-i32binop f s)))
		  (if (Stringp x) x (wasm-eval-h r (cadr x)))))
	       (:i64binop
		(let ((x (wasm-eval-h-i64binop f s)))
		  (if (Stringp x) x (wasm-eval-h r (cadr x)))))
	       (:nop (wasm-eval-h r s))))))

(definec wasm-eval (p :wasm-program) :val-or-error
  (wasm-eval-h p nil))
