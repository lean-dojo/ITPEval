;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_upper_bound_pre_sorted_goal28:
;; sortedness of the upper-bound search suffix after the Why3 quotient
;; midpoint, with exact C signed-32 address shifts, uint32 coercion laws,
;; integer bounds, linkedness, and memory-readability hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun er28-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun er28-address-base (address)
  (car address))

(defun er28-address-offset (address)
  (cdr address))

(defun er28-shift (address amount)
  (cons
   (er28-address-base address)
   (+ (er28-address-offset address) amount)))

;; Memory.shift_sint32 advances by one logical memory cell per array index.

(defun er28-shift-sint32 (address index)
  (er28-shift address index))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, uint32 conversion,
;; and linked predicate specialized to t.

(defstub er28-integer-memory (address) t)
(defstub er28-allocation (index) t)
(defstub er28-region (base) t)
(defstub er28-to-uint32 (value) t)
(defstub er28-linked-op () t)

(defun-sk er28-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (er28-address-p address)
      (integerp (er28-integer-memory address)))
     (implies
      (integerp index)
      (integerp (er28-allocation index)))
     (implies
      (integerp base)
      (integerp (er28-region base)))
     (implies
      (integerp value)
      (integerp (er28-to-uint32 value))))))

(defun er28-linked-p ()
  (if (er28-linked-op) t nil))

(defun er28-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun er28-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact imported Cint laws is_to_uint32, id_uint32, and proj_uint32 for the
;; arbitrary conversion function.

(defun-sk er28-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (er28-is-uint32-p (er28-to-uint32 value))
      (implies
       (er28-is-uint32-p value)
       (equal (er28-to-uint32 value) value))
      (equal
       (er28-to-uint32 (er28-to-uint32 value))
       (er28-to-uint32 value))))))

;; Why3 ComputerDivision.div truncates the mathematical-integer quotient
;; toward zero.

(defun er28-tdiv (numerator denominator)
  (if
      (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor (abs numerator) (abs denominator))))
        (if
            (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun er28-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (er28-address-base address)))
    (<= 0 (er28-address-offset address))
    (<=
     (+ (er28-address-offset address) length)
     (er28-allocation (er28-address-base address))))))

;; Exact unfoldings of the pinned Axiomatic.mlw range predicates. Every
;; source array index is translated through Memory.shift_sint32.

(defun-sk er28-sorted-range-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
     (< left right))
     (<=
      (er28-integer-memory (er28-shift a left))
      (er28-integer-memory (er28-shift a right))))))

(defun-sk er28-strict-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      (er28-integer-memory (er28-shift a index))
      value))))

(defun-sk er28-strict-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      value
      (er28-integer-memory (er28-shift a index))))))

(defun-sk er28-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      value
      (er28-integer-memory (er28-shift a index))))))

(defun-sk
    ntp4vc-equal-range-call-upper-bound-pre-sorted-goal28-statement ()
  (forall
   (i1 i4 i3 a i2 i)
   (implies
    (and
     (integerp i1)
     (integerp i4)
     (integerp i3)
     (er28-address-p a)
     (integerp i2)
     (integerp i)
     (er28-function-types-p)
     (er28-to-uint32-laws-p))
    (let*
        ((x (+ i1 i4))
         (x2 (- i3 i4))
         (x3 (er28-tdiv x2 2))
         (x4 (+ i4 x3))
         (a1 (er28-shift-sint32 a x4))
         (x5 (er28-integer-memory a1))
         (x6
          (+
           i4
           (er28-to-uint32
            (er28-tdiv (er28-to-uint32 x2) 2))))
         (a2 (er28-shift-sint32 a i4))
         (x7 (+ 1 i4 x3)))
      (implies
       (and
        (<= 0 i1)
        (<= i3 i2)
        (<= i4 i3)
        (<= 0 i4)
        (< i4 i3)
        (<= 0 x)
        (<= (er28-region (er28-address-base a)) 0)
        (<= 0 x3)
        (<= i1 x3)
        (< x4 i3)
        (<= x5 i)
        (<= 0 x6)
        (<= i x5)
        (<= x 4294967295)
        (<= i3 (+ 4294967295 i4))
        (<= x3 4294967295)
        (<= x4 4294967294)
        (<= i3 (+ 4294967296 i4 x3))
        (<= x6 4294967295)
        (er28-linked-p)
        (er28-is-uint32-p i1)
        (er28-is-uint32-p i2)
        (er28-is-uint32-p i3)
        (er28-is-uint32-p i4)
        (er28-is-sint32-p i)
        (er28-sorted-range-p a 0 i2)
        (er28-strict-upper-bound-p a 0 i4 i)
        (er28-strict-lower-bound-p a i3 i2 i)
        (er28-valid-rd-p (er28-shift-sint32 a 0) i2)
        (er28-valid-rd-p a2 x3)
        (er28-sorted-range-p a2 0 x3)
        (er28-is-uint32-p x4)
        (er28-is-uint32-p x7)
        (er28-is-sint32-p x5)
        (er28-valid-rd-p a1 1)
        (er28-strict-upper-bound-p a2 0 i1 x5)
        (er28-lower-bound-p a2 i1 x3 x5))
       (er28-sorted-range-p
        (er28-shift-sint32 a x7)
        0
        (- (- (- i3 1) i4) x3)))))))

(value-triple :itpeval-statement-checked)

:q
