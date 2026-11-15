;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/inner_product/inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_4_goal11:
;; the signed 32-bit upper-overflow bound for the next inner-product
;; accumulation under the stated index, memory, product, and partial-sum
;; bounds. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ip11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ip11-address-base (address)
  (car address))

(defun ip11-address-offset (address)
  (cdr address))

(defun ip11-shift (address amount)
  (cons
   (ip11-address-base address)
   (+ (ip11-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1 and allocation map t, together with the fixed region
;; function, linked predicate specialized to t, signed-32 conversion, and
;; logical inner-product function specialized to t_1.

(defstub ip11-integer-memory (address) t)
(defstub ip11-allocation (index) t)
(defstub ip11-region (base) t)
(defstub ip11-linked-op () t)
(defstub ip11-to-sint32 (value) t)
(defstub ip11-l-innerproduct (a b n init) t)

(defun-sk ip11-function-types-p ()
  (forall (address index base value a b n init)
    (and
     (implies
      (ip11-address-p address)
      (integerp (ip11-integer-memory address)))
     (implies
      (integerp index)
      (integerp (ip11-allocation index)))
     (implies
      (integerp base)
      (integerp (ip11-region base)))
     (implies
      (integerp value)
      (integerp (ip11-to-sint32 value)))
     (implies
      (and
       (ip11-address-p a)
       (ip11-address-p b)
       (integerp n)
       (integerp init))
      (integerp (ip11-l-innerproduct a b n init))))))

(defun ip11-linked-p ()
  (if (ip11-linked-op) t nil))

(defun ip11-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ip11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are the imported Cint laws is_to_sint32, id_sint32, and
;; proj_sint32 for the arbitrary signed-32 conversion function.

(defun-sk ip11-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ip11-is-sint32-p (ip11-to-sint32 value))
      (implies
       (ip11-is-sint32-p value)
       (equal (ip11-to-sint32 value) value))
      (equal
       (ip11-to-sint32 (ip11-to-sint32 value))
       (ip11-to-sint32 value))))))

;; These are the imported Q_InnerProductEmpty and Q_InnerProductNext laws,
;; specialized to the arbitrary integer memory above. They characterize every
;; nonnegative partial inner product used by this verification condition.

(defun-sk ip11-innerproduct-laws-p ()
  (forall (a b n init)
    (implies
     (and
      (ip11-address-p a)
      (ip11-address-p b)
      (integerp n)
      (integerp init)
      (ip11-is-sint32-p init))
     (and
      (implies
       (<= n 0)
       (equal
        (ip11-l-innerproduct a b n init)
        init))
      (implies
       (< 0 n)
       (equal
        (+
         (ip11-l-innerproduct a b (- n 1) init)
         (*
          (ip11-integer-memory (ip11-shift a (- n 1)))
          (ip11-integer-memory (ip11-shift b (- n 1)))))
        (ip11-l-innerproduct a b n init)))))))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun ip11-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (ip11-address-base address)))
    (<= 0 (ip11-address-offset address))
    (<=
     (+ (ip11-address-offset address) length)
     (ip11-allocation (ip11-address-base address))))))

;; Exact unfolding of Axiomatic1.p_productbounds over every mathematical
;; integer index.

(defun-sk ip11-productbounds-p (a b n)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= 0 index)
      (implies
       (< index n)
       (let
           ((product
             (*
              (ip11-integer-memory (ip11-shift a index))
              (ip11-integer-memory (ip11-shift b index)))))
         (and
          (<= -2147483648 product)
          (<= product 2147483647))))))))

;; Exact unfolding of Axiomatic1.p_innerproductbounds over every mathematical
;; integer index.

(defun-sk ip11-innerproductbounds-p (a b n init)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= index n)
      (implies
       (<= 0 index)
       (let
           ((partial
             (ip11-l-innerproduct a b index init)))
         (and
          (<= -2147483648 partial)
          (<= partial 2147483647))))))))

(defun-sk
    ntp4vc-inner-product-assert-rte-signed-overflow-4-goal11-statement ()
  (forall
   (a i2 a1 i1 i)
   (implies
    (and
     (ip11-address-p a)
     (integerp i2)
     (ip11-address-p a1)
     (integerp i1)
     (integerp i)
     (ip11-function-types-p)
     (ip11-to-sint32-laws-p)
     (ip11-innerproduct-laws-p))
    (let*
        ((x
          (ip11-integer-memory (ip11-shift a i2)))
         (x1
          (ip11-integer-memory (ip11-shift a1 i2)))
         (x2
          (ip11-l-innerproduct a1 a i2 i1)))
      (implies
       (and
        (<= i2 i)
        (<= 0 i2)
        (< i2 i)
        (<= (ip11-region (ip11-address-base a)) 0)
        (<= (ip11-region (ip11-address-base a1)) 0)
        (ip11-linked-p)
        (ip11-is-uint32-p i)
        (ip11-is-uint32-p i2)
        (ip11-is-sint32-p i1)
        (ip11-productbounds-p a1 a i)
        (ip11-is-sint32-p x)
        (ip11-is-sint32-p x1)
        (ip11-innerproductbounds-p a1 a i i1)
        (ip11-valid-rd-p (ip11-shift a 0) i)
        (ip11-valid-rd-p (ip11-shift a1 0) i)
        (ip11-is-sint32-p x2))
       (<=
        (+
         x2
         (ip11-to-sint32 (* x x1)))
        2147483647))))))

(value-triple :itpeval-statement-checked)

:q
