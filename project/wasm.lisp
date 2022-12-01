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

(defdata wasm-ops-h-out (oneof String int))
(defdata wasm-eval-h-out (oneof String stack))

(defdata bitlist (listof (oneof 0 1)))

;; integer to bits as a tl 
(definec int-to-bits-helper (x :i64 b :bitlist) :bitlist
  (if (> x 1)
      (int-to-bits-helper (truncate x 2) (cons (rem x 2) b))
    (append (list x) b)))
(definec int-to-bits (x :i64) :bitlist
  (int-to-bits-helper x nil))

;; bits to integer 
(definec bits-to-int-helper (bits :bitlist ct :nat ret :int) :int
  (match bits
    (nil ret)
    ((f . r) (bits-to-int-helper r (+ ct 1) (+ ret (* f (expt 2 ct)))))))

(property use (bits :bitlist)
  (bitlistp (rev bits)))

(definec bits-to-int (bits :bitlist) :int
  (bits-to-int-helper (rev bits) 0 0))


(definec count-trailing-zeros-h (bits :bitlist) :nat
  (match bits
    (nil 0)
    ((f . r) (if (zerop f) (+ 1 (count-trailing-zeros-h r)) 0))))

(definec count-trailing-zeros (bits :bitlist) :nat
  (count-trailing-zeros-h (rev bits)))

(definec count-non-zero-bits (bits :bitlist) :nat
  (match bits
    (nil 0)
    ((f . r) (+ f (count-non-zero-bits r)))))

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
(definec invert-bits (bits :bitlist) :bitlist
  (if (consp bits)
      (if (= 0 (car bits))
	  (cons 1 (invert-bits (cdr bits)))
	  (cons 0 (invert-bits (cdr bits))))
      nil))

;; this takes the reverse of bits as input 
(definec twos-complement-helper (bits :bitlist carry :nat) :bitlist
  (if (consp bits)
      (if (= 0 (car bits)) ;; I should technically write this in match but i don't trust match 
	  (if (= 0 carry)
	      (append (twos-complement-helper (cdr bits) 0) '(0))
	    (append (twos-complement-helper (cdr bits) 0) '(1)))
	(if (= 0 carry)
	    (append (twos-complement-helper (cdr bits) 0) '(1))
          (append (twos-complement-helper (cdr bits) 1) '(0))))
    nil))
    
;; invert all the bits and then add 1
(definec twos-complement (bits :bitlist) :bitlist
  (twos-complement-helper (rev (invert-bits bits)) 1))

;; if the value is between 0 and 2^31 then return the value
;; else return the integer value of the twos complement of i
(definec sign-interpretation-32 (i :i32) :i32
  :skip-function-contractp t
  (if (and (>= i 0) (< i (expt 2 31)))
      i
    (bits-to-int (twos-complement (int-to-bits i)))))

(definec sign-interpretation-64 (i :i64) :i64
  :skip-function-contractp t
  (if (and (>= i 0) (< i (expt 2 63)))
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
(definec bits-and-h (bx :bitlist by :bitlist ret :bitlist) :int
  (match (list bx by)
    ((nil &) (bits-to-int ret))
    ((& nil) (bits-to-int ret))
    (((f . r) (g . s)) (bits-and-h r s (cons (* f g) ret)))))

(definec bits-and (x :i64 y :i64) :int
  (let ((bx (rev (int-to-bits x)))
        (by (rev (int-to-bits y))))
    (bits-and-h bx by nil)))

;; bitwise or
(definec bits-or-h (bx :bitlist by :bitlist ret :bitlist) :int
  (match (list bx by)
    ((nil nil) (bits-to-int ret))
    ((nil (g . s)) (bits-or-h nil s (cons g ret)))
    (((f . r) nil) (bits-or-h r nil (cons f ret)))
    (((f . r) (g . s)) (bits-or-h r s (cons (max f g) ret)))))

(definec bits-or (x :i64 y :i64) :int
  (let ((bx (rev (int-to-bits x)))
        (by (rev (int-to-bits y))))
    (bits-or-h bx by nil)))

;; bitwise xor
(definec bits-xor-h (bx :bitlist by :bitlist ret :bitlist) :int
  (match (list bx by)
    ((nil nil) (bits-to-int ret))
    ((nil (g . s)) (bits-xor-h nil s (cons g ret)))
    (((f . r) nil) (bits-xor-h r nil (cons f ret)))
    (((f . r) (g . s)) (bits-xor-h r s (cons (rem (+ f g) 2) ret)))))

(definec bits-xor (x :i64 y :i64) :int
  (let ((bx (rev (int-to-bits x)))
        (by (rev (int-to-bits y))))
    (bits-xor-h bx by nil)))

(definec wasm-eval-h-i32binop-arith (i :i32binop x :i32 y :i32) :wasm-ops-h-out
  (match i
    ('add32 (rem (+ x y) (expt 2 32)))
    ('sub32 (rem (+ (- x y) (expt 2 32)) (expt 2 32)))
    ('mul32 (rem (* x y) (expt 2 32)))
    ('div_u32 (if (zerop y) "div by 0 error" (truncate x y)))
    ('rem_u32 (if (zerop y) "rem by 0 error" (rem x y)))
    ('div_s32 (let ((sx (sign-interpretation-32 x)) (sy (sign-interpretation-32 y)))
		   (if (zerop sy) "div by 0 error"
		   (if (= (truncate sx sy) (expt 2 31)) "signed div by 0 error" (truncate sx sy)))))
    ('rem_s32 (let ((sx (sign-interpretation-32 x)) (sy (sign-interpretation-32 y)))
		(if (zerop sy) "rem by 0 error" (rem sx sy))))
    (& "this error shouldn't happen. in: wasm-eval-h-i32binop-arith")))

(definec wasm-eval-h-i32binop-bitwise (i :i32binop x :i32 y :i32) :wasm-ops-h-out
  (match i
    ('and32 (bits-and x y))
    ('or32 (bits-or x y))
    ('xor32 (bits-xor x y))
    (& "this error shouldn't happen. in: wasm-eval-h-i32binop-bitwise")))

(definec wasm-eval-h-i32binop-compare (i :i32binop x :i32 y :i32) :wasm-ops-h-out
  (match i
    ('eq32 (if (= x y) 1 0))
    ('ne32 (if (= x y) 0 1))
    ('lt_s32 (if (< (sign-interpretation-32 x) (sign-interpretation-32 y)) 1 0))
    ('lt_u32 (if (< x y) 1 0))
    ('gt_u32 (if (> x y) 1 0))
    ('gt_s32 (if (> (sign-interpretation-32 x) (sign-interpretation-32 y)) 1 0))
    ('le_u32 (if (<= x y) 1 0))
    ('le_s32 (if (<= (sign-interpretation-32 x) (sign-interpretation-32 y)) 1 0))
    ('ge_u32 (if (>= x y) 1 0))
    ('ge_s32 (if (>= (sign-interpretation-32 x) (sign-interpretation-32 y)) 1 0))
    (& "this error shouldn't happen. in: wasm-eval-h-i32binop-compare")))


(definec wasm-eval-h-i32binop (i :i32binop s :stack) :wasm-eval-h-out
  :skip-function-contractp t
  (match s
    (nil "not enough arguments!")
    ((x . k)
     (match k
       (nil "not enough arguments!")
       ((y . r) (if (and (i32p x) (i32p y))
                    (match i
	            ((:or 'add32 'sub32 'mul32 'div_u32 'rem_u32 'div_s32 'rem_s32)
	             (let ((res (wasm-eval-h-i32binop-arith i x y)))
		       (if (not (constp x)) "result was not a const"
			 (if (wasm-eval-h-outp res) res (cons res r)))))  
	            ((:or 'and32 'or32 'xor32)
	             (let ((res (wasm-eval-h-i32binop-bitwise i x y)))
		       (if (not (constp x)) "result was not a const"
			 (if (wasm-eval-h-outp res) res (cons res r)))))  
                   (& (let ((res (wasm-eval-h-i32binop-compare i x y)))
			(if (not (constp x)) "result was not a const"
			  (if (wasm-eval-h-outp res) res (cons res r)))))) 
	         "not i32 inputs!"))
       ))))


;; 64 bit binary ops
(definec wasm-eval-h-i64binop-arith (i :i64binop x :i64 y :i64) :wasm-ops-h-out
  (match i
    ('add32 (rem (+ x y) (expt 2 64)))
    ('sub32 (rem (+ (- x y) (expt 2 64)) (expt 2 64)))
    ('mul32 (rem (* x y) (expt 2 64)))
    ('div_u32 (if (zerop y) "div by 0 error" (truncate x y)))
    ('rem_u32 (if (zerop y) "rem by 0 error" (rem x y)))
    ('div_s32 (let ((sx (sign-interpretation-64 x)) (sy (sign-interpretation-64 y)))
		   (if (zerop sy) "div by 0 error"
		   (if (= (truncate sx sy) (expt 2 64)) "signed div by 0 error" (truncate sx sy)))))
    ('rem_s32 (let ((sx (sign-interpretation-64 x)) (sy (sign-interpretation-64 y)))
		(if (zerop sy) "rem by 0 error" (rem sx sy))))
    (& "this error shouldn't happen. in: wasm-eval-h-i64binop-arith")))

(definec wasm-eval-h-i64binop-bitwise (i :i64binop x :i64 y :i64) :wasm-ops-h-out
  (match i
    ('and64 (bits-and x y))
    ('or64 (bits-or x y))
    ('xor64 (bits-xor x y))
    (& "this error shouldn't happen. in: wasm-eval-h-i64binop-bitwise")))

(definec wasm-eval-h-i64binop-compare (i :i64binop x :i64 y :i64) :wasm-ops-h-out
  (match i
    ('eq64 (if (= x y) 1 0))
    ('ne64 (if (= x y) 0 1))
    ('lt_s64 (if (< (sign-interpretation-64 x) (sign-interpretation-64 y)) 1 0))
    ('lt_u64 (if (< x y) 1 0))
    ('gt_u64 (if (> x y) 1 0))
    ('gt_s64 (if (> (sign-interpretation-64 x) (sign-interpretation-64 y)) 1 0))
    ('le_u64 (if (<= x y) 1 0))
    ('le_s64 (if (<= (sign-interpretation-64 x) (sign-interpretation-64 y)) 1 0))
    ('ge_u64 (if (>= x y) 1 0))
    ('ge_s64 (if (>= (sign-interpretation-64 x) (sign-interpretation-64 y)) 1 0))
    (& "this error shouldn't happen. in: wasm-eval-h-i32binop-compare")))


(definec wasm-eval-h-i64binop (i :i64binop s :stack) :wasm-eval-h-out
  :skip-function-contractp t
  (match s
    (nil "not enough arguments!")
    ((x . k)
     (match k
       (nil "not enough arguments!")
       ((y . r) (if (and (i64p x) (i64p y))
                    (match i
	            ((:or 'add64 'sub64 'mul64 'div_u64 'rem_u64 'div_s64 'rem_s64)
	             (let ((res (wasm-eval-h-i64binop-arith i x y)))
		       (if (not (constp x)) "result was not a const"
			 (if (wasm-eval-h-outp res) res (cons res r)))))  
	            ((:or 'and64 'or64 'xor64)
	             (let ((res (wasm-eval-h-i64binop-bitwise i x y)))
		       (if (not (constp x)) "result was not a const"
			 (if (wasm-eval-h-outp res) res (cons res r)))))  
                   (& (let ((res (wasm-eval-h-i64binop-compare i x y)))
			(if (not (constp x)) "result was not a const"
			  (if (wasm-eval-h-outp res) res (cons res r)))))) 
	         "not i64 inputs!"))
    ))))


(property (s :stack)
  (implies (not (equal s nil)) (val-or-errorp (car s))))

(property (s :string)
  (val-or-errorp s))

(definec wasm-eval-h (p :wasm-function s :stack) :val-or-error
  :skip-function-contractp t
  :skip-body-contractsp t
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
	       (:nop (wasm-eval-h r s))))))

(definec wasm-eval (p :wasm-function) :val-or-error
  (wasm-eval-h p nil))


"pretty printing constants:
for i32: (_ bv32 n)
for i64; (_ bv64 n)"

(defdata z3-stack (listof String))
 
(definec pretty-print-const (c :const s :z3-stack) :z3-stack
  (let ((n (if (i32p c)
	 (string-append (string-append "(_ bv32 " (str::nat-to-dec-string c)) ")")
       (string-append (string-append "(_ bv64 " (str::nat-to-dec-string c)) ")"))))
    (append (list n) s)))
	  
(definec pretty-print-i32unop (c :i32unop s :z3-stack) :z3-stack
  (match s
    (nil '("this should not happen"))
    ((f . r)    
     (append 
      (list (string-append 
	     (match c
	       ('eqz32 "(= 0 ") 
	       ('clz32 "TODO")
	       ('ctz32 "TODO")
	       ('popcnt32 "TODO")
	       ('wrap64 "TODO but actually"))
	     f))
      r))))

(definec pretty-print-i64unop (c :i64unop s :z3-stack) :z3-stack 
  (match s
    (nil '("this should not happen"))
    ((f . r)
     (append
      (list
       (string-append 	
	(match c
	  ('eqz64 "=") 
	  ('clz64 "bvclz")
	  ('ctz64 "bvctz")
	  ('popcnt64 "TODO")
	  ('extend_s32 "TODO but actually")
	  ('extend_u32 "TODO but actually"))
	f))
      r))))

(definec pretty-print-i32binop (bin :i32binop s :z3-stack) :z3-stack
  (match s
    (nil '("this should not happen"))
    ((f . s )
     (match s
       (nil '("this should not happen"))
       ((s . r)
	(append
	 (list
	  (string-append
	  (string-append
	   (string-append
	    (string-append 
	    (match bin
	      ('add32 "(bvadd ")
	      ('sub32 "(bvsub ")
	      ('mul32 "(bvmul ")
	      ('div_u32 "(bvudiv ")
	      ('rem_u32 "(bvurem ")
	      ('div_s32 "(bvsdiv ")
	      ('rem_s32 "(bvsrem ")
	      ('and32 "(bvand ")
	      ('or32 "(bvor ")
	      ('xor32 "(bvxor ")
	      ('eq32 "(= ")
	      ('ne32 "(bvne ")
	      ('lt_s32 "(bvslt ")
	      ('lt_u32 "(bvult ")
	      ('gt_u32 "(bvugt ")
	      ('gt_s32 "(bvsgt ")
	      ('le_u32 "(bvule ")
	      ('le_s32 "(bvsle ")
	      ('ge_u32 "(bvuge ")
	      ('ge_s32 "(bvsge "))	    
	    f) " ")
	   s) ")"))
	 r))))))

(definec pretty-print-i64binop (bin :i64binop s :z3-stack) :z3-stack
  (match s
    (nil '("this should not happen"))
    ((f . s )
     (match s
       (nil '("this should not happen"))
       ((s . r)
	(append
	 (list
	  (string-append
	  (string-append
	   (string-append
	    (string-append 
	     (match bin
	      ('add64 "bvadd")
	      ('sub64 "bvsub")
	      ('mul64 "bvmul")
	      ('div_u64 "bvudiv")
	      ('rem_u64 "bvurem")
	      ('div_s64 "bvsdiv")
	      ('rem_s64 "bvsrem")
	      ('and64 "bvand")
	      ('or64 "bvor")
	      ('xor64 "bvxor")
	      ('eq64 "=")
	      ('ne64 "bvne")
	      ('lt_s64 "bvslt")
	      ('lt_u64 "bvult")
	      ('gt_u64 "bvugt")
	      ('gt_s64 "bvsgt")
	      ('le_u64 "bvule")
	      ('le_s64 "bvsle")
	      ('ge_u64 "bvuge")
	      ('ge_s64 "bvsge"))
	     f) " ")
	   s) ")"))
	 r))))))

 
(definec pretty-print-func (f :wasm-function s :z3-stack) :String
    :skip-function-contractp t
  (match f
    (nil

     
     (match s
       (nil "")
       (& (car s))))

    ((f . r)
     (pretty-print-func
      r
      (match f
	(:nop s)
	(:const (pretty-print-const f s))
	(:i32unop (pretty-print-i32unop f s))
	(:i64unop (pretty-print-i64unop f s))
	(:i32binop (pretty-print-i32binop f s))
	(:i64binop (pretty-print-i64binop f s)))))))



(pretty-print-func
 (list
  3
  42
  'add32)
 '())

(mv-let
  (channel state)
  (open-output-channel "z3-programs/exmp1" :object state)
  (pprogn (fms
	   (pretty-print-func
	    (list 3 42 'add32)
	    '())
	   (list)
               channel state nil)
          (close-output-channel channel state)))



;; Z3 Shenanigans

;:q

;(load "~/quicklisp/setup.lisp")
;(ql:quickload :lisp-z3)
;(defpackage :z3-bitvectors
;  (:use :cl :z3))

;(in-package :z3-bitvectors)

;(solver-init)

;(solver-push)
;(z3-assert
 ;; A bitvector variable must be given a length.
 ;(v (:bv 5))
 ;; the nil below indicates that we want to treat v as an unsigned
 ;; value when we convert it to an integer.
 ;(= (bv2int v nil) 20))
;; Bitvectors are converted to CL bitvector objects.
;(check-sat)
;(solver-pop)

;;(register-enum-sort :wasm-const val)

;(defstruct i32 integer) ; (setq v (make-i32 :integer 3))
;(defstruct i64 integer) ; (setq v (make-i64 :integer 3))

;; we can define instructions as either:
;; constants,
;(deftype const '(i32 i64))

;(defun z3-var (ind)
;  (intern (concatenate 'string "X" (write-to-string ind)))) 

;(defun wasm-specs (lst)
;  (match lst
;    ((type i32) `(,(z3-var lst) :bv32))
;    ((type i64) `(,(z3-var lst) :bv64))
;    ))

;(wasm-specs 0)

;(z3-assert-fn (wasm-specs 'S)
;              (wasm-constraints 'S))



;; const 3
;; const 42
;; i32.add

;; reduces to in Z3
;; X = 3 + 42
