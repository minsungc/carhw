;; WebAssembly 1.0 in ACL2
;; Minsung Cho, Michelle Thalakottur

;; We first define i32 and i64 types (no floats as ACL2 does not support them)

(defdata i32 (range integer (0 <= _ < (expt 2 32))))
(defdata i64 (range integer (0 <= _ < (expt 2 64))))

;; we can define instructions as either:

;; constants,

(defdata const (oneof i32 i64))

;; unary operations on 32-bit nums,
  
(defdata i32unop (enum '(clz32 ctz32 popcnt32)))

;; unary operations on 64-bit nums,

(defdata i64unop (enum '(clz64 ctz64 popcnt64)))

;; binary operations on 32-bit nums,

(defdata i32binop (enum '(add32 sub32 mul32 div_u32 rem_u32)))

;; binary operations on 64-bit nums,

(defdata i64binop (enum '(add64 sub64 mul64 div_u64 rem_u64)))

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

(definec wasm-eval-h-i32unop (i :i32unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not x) "not enough variables declared to do i32unop!"
      (match i
        ('clz32 "TODO")
        ('ctz32 "TODO")
        ('popcnt32 "TODO")))))

(definec wasm-eval-h-i64unop (i :i64unop s :stack) :wasm-eval-h-out
  (let ((x (car s)))
    (if (not x) "not enough variables declared to do i64unop!"
      (match i
        ('clz64 "TODO")
        ('ctz64 "TODO")
        ('popcnt64 "TODO")))))

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
  :timeout 180)

(definec wasm-eval (p :wasm-program) :val-or-error
  (wasm-eval-h p nil))
