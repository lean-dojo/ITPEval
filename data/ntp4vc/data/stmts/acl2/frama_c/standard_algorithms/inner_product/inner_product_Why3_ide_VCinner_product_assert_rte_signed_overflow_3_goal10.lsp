;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/inner_product/inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_3_goal10:
;; the signed 32-bit lower-overflow bound for the next inner-product
;; accumulation under the stated index, memory, product, and partial-sum
;; bounds. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ip10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ip10-address-base (address)
  (car address))

(defun ip10-address-offset (address)
  (cdr address))

(defun ip10-shift (address amount)
  (cons
   (ip10-address-base address)
   (+ (ip10-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1 and allocation map t, together with the fixed region
;; function, linked predicate specialized to t, signed-32 conversion, and
;; logical inner-product function specialized to t_1.

(defstub ip10-integer-memory (address) t)
(defstub ip10-allocation (index) t)
(defstub ip10-region (base) t)
(defstub ip10-linked-op () t)
(defstub ip10-to-sint32 (value) t)
(defstub ip10-l-innerproduct (a b n init) t)

(defun-sk ip10-function-types-p ()
  (forall (address index base value a b n init)
    (and
     (implies
      (ip10-address-p address)
      (integerp (ip10-integer-memory address)))
     (implies
      (integerp index)
      (integerp (ip10-allocation index)))
     (implies
      (integerp base)
      (integerp (ip10-region base)))
     (implies
      (integerp value)
      (integerp (ip10-to-sint32 value)))
     (implies
      (and
       (ip10-address-p a)
       (ip10-address-p b)
       (integerp n)
       (integerp init))
      (integerp (ip10-l-innerproduct a b n init))))))

(defun ip10-linked-p ()
  (if (ip10-linked-op) t nil))

(defun ip10-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ip10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; These are the imported Cint laws is_to_sint32, id_sint32, and
;; proj_sint32 for the arbitrary signed-32 conversion function.

(defun-sk ip10-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ip10-is-sint32-p (ip10-to-sint32 value))
      (implies
       (ip10-is-sint32-p value)
       (equal (ip10-to-sint32 value) value))
      (equal
       (ip10-to-sint32 (ip10-to-sint32 value))
       (ip10-to-sint32 value))))))

;; These are the imported Q_InnerProductEmpty and Q_InnerProductNext laws,
;; specialized to the arbitrary integer memory above. They characterize every
;; nonnegative partial inner product used by this verification condition.

(defun-sk ip10-innerproduct-laws-p ()
  (forall (a b n init)
    (implies
     (and
      (ip10-address-p a)
      (ip10-address-p b)
      (integerp n)
      (integerp init)
      (ip10-is-sint32-p init))
     (and
      (implies
       (<= n 0)
       (equal
        (ip10-l-innerproduct a b n init)
        init))
      (implies
       (< 0 n)
       (equal
        (+
         (ip10-l-innerproduct a b (- n 1) init)
         (*
          (ip10-integer-memory (ip10-shift a (- n 1)))
          (ip10-integer-memory (ip10-shift b (- n 1)))))
        (ip10-l-innerproduct a b n init)))))))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun ip10-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (ip10-address-base address)))
    (<= 0 (ip10-address-offset address))
    (<=
     (+ (ip10-address-offset address) length)
     (ip10-allocation (ip10-address-base address))))))

;; Exact unfolding of Axiomatic1.p_productbounds over every mathematical
;; integer index.

(defun-sk ip10-productbounds-p (a b n)
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
              (ip10-integer-memory (ip10-shift a index))
              (ip10-integer-memory (ip10-shift b index)))))
         (and
          (<= -2147483648 product)
          (<= product 2147483647))))))))

;; Exact unfolding of Axiomatic1.p_innerproductbounds over every mathematical
;; integer index.

(defun-sk ip10-innerproductbounds-p (a b n init)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (<= index n)
      (implies
       (<= 0 index)
       (let
           ((partial
             (ip10-l-innerproduct a b index init)))
         (and
          (<= -2147483648 partial)
          (<= partial 2147483647))))))))

(defun-sk
    ntp4vc-inner-product-assert-rte-signed-overflow-3-goal10-statement ()
  (forall
   (a i2 a1 i1 i)
   (implies
    (and
     (ip10-address-p a)
     (integerp i2)
     (ip10-address-p a1)
     (integerp i1)
     (integerp i)
     (ip10-function-types-p)
     (ip10-to-sint32-laws-p)
     (ip10-innerproduct-laws-p))
    (let*
        ((x
          (ip10-integer-memory (ip10-shift a i2)))
         (x1
          (ip10-integer-memory (ip10-shift a1 i2)))
         (x2
          (ip10-l-innerproduct a1 a i2 i1)))
      (implies
       (and
        (<= i2 i)
        (<= 0 i2)
        (< i2 i)
        (<= (ip10-region (ip10-address-base a)) 0)
        (<= (ip10-region (ip10-address-base a1)) 0)
        (ip10-linked-p)
        (ip10-is-uint32-p i)
        (ip10-is-uint32-p i2)
        (ip10-is-sint32-p i1)
        (ip10-productbounds-p a1 a i)
        (ip10-is-sint32-p x)
        (ip10-is-sint32-p x1)
        (ip10-innerproductbounds-p a1 a i i1)
        (ip10-valid-rd-p (ip10-shift a 0) i)
        (ip10-valid-rd-p (ip10-shift a1 0) i)
        (ip10-is-sint32-p x2))
       (<=
        -2147483648
        (+
         x2
         (ip10-to-sint32 (* x x1)))))))))

(value-triple :itpeval-statement-checked)

:q
