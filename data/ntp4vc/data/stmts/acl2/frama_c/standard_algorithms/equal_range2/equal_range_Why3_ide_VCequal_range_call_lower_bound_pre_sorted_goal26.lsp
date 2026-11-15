;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_call_lower_bound_pre_sorted_goal26:
;; preservation of the sorted-range precondition for the lower-bound call,
;; with exact C signed-32 address shifts, integer division, uint32 coercion,
;; value bounds, linkedness, and memory-readability hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun er26-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun er26-address-base (address)
  (car address))

(defun er26-address-offset (address)
  (cdr address))

(defun er26-shift (address amount)
  (cons
   (er26-address-base address)
   (+ (er26-address-offset address) amount)))

;; Memory.shift_sint32 advances by one logical memory cell per array index.

(defun er26-shift-sint32 (address index)
  (er26-shift address index))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, uint32 conversion,
;; and linked predicate specialized to t.

(defstub er26-integer-memory (address) t)
(defstub er26-allocation (index) t)
(defstub er26-region (base) t)
(defstub er26-to-uint32 (value) t)
(defstub er26-linked-op () t)

;; Preserve the source function types over complete unbounded integer and
;; address domains.

(defun-sk er26-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (er26-address-p address)
      (integerp (er26-integer-memory address)))
     (implies
      (integerp index)
      (integerp (er26-allocation index)))
     (implies
      (integerp base)
      (integerp (er26-region base)))
     (implies
      (integerp value)
      (integerp (er26-to-uint32 value))))))

(defun er26-linked-p ()
  (if (er26-linked-op) t nil))

(defun er26-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun er26-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact imported Cint laws is_to_uint32, id_uint32, and proj_uint32 for the
;; arbitrary conversion function.

(defun-sk er26-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (er26-is-uint32-p (er26-to-uint32 value))
      (implies
       (er26-is-uint32-p value)
       (equal (er26-to-uint32 value) value))
      (equal
       (er26-to-uint32 (er26-to-uint32 value))
       (er26-to-uint32 value))))))

;; Why3 ComputerDivision.div truncates the mathematical-integer quotient
;; toward zero.

(defun er26-tdiv (numerator denominator)
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

(defun er26-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (er26-address-base address)))
    (<= 0 (er26-address-offset address))
    (<=
     (+ (er26-address-offset address) length)
     (er26-allocation (er26-address-base address))))))

;; Exact unfoldings of the pinned Axiomatic.mlw range predicates. Every
;; source array index is translated through Memory.shift_sint32.

(defun-sk er26-sorted-range-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (er26-integer-memory (er26-shift a left))
      (er26-integer-memory (er26-shift a right))))))

(defun-sk er26-strict-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      (er26-integer-memory (er26-shift a index))
      value))))

(defun-sk er26-strict-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      value
      (er26-integer-memory (er26-shift a index))))))

(defun-sk
    ntp4vc-equal-range-call-lower-bound-pre-sorted-goal26-statement ()
  (forall
   (i3 i2 i1 i a)
   (implies
    (and
     (integerp i3)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (er26-address-p a)
     (er26-function-types-p)
     (er26-to-uint32-laws-p))
    (let*
        ((x (- i2 i3))
         (x1 (er26-tdiv x 2))
         (x2 (+ i3 x1))
         (a1 (er26-shift-sint32 a x2))
         (x3 (er26-integer-memory a1))
         (x4
          (+
           i3
           (er26-to-uint32
            (er26-tdiv (er26-to-uint32 x) 2)))))
      (implies
       (and
        (<= i2 i1)
        (<= i3 i2)
        (<= 0 i3)
        (< i3 i2)
        (<= (er26-region (er26-address-base a)) 0)
        (<= 0 x1)
        (<= x3 i)
        (<= 0 x4)
        (<= i x3)
        (<= i2 (+ 4294967295 i3))
        (<= x1 4294967295)
        (<= x4 4294967295)
        (er26-linked-p)
        (er26-is-uint32-p i1)
        (er26-is-uint32-p i2)
        (er26-is-uint32-p i3)
        (er26-is-sint32-p i)
        (er26-sorted-range-p a 0 i1)
        (er26-strict-upper-bound-p a 0 i3 i)
        (er26-strict-lower-bound-p a i2 i1 i)
        (er26-valid-rd-p (er26-shift-sint32 a 0) i1)
        (er26-is-uint32-p x2)
        (er26-is-sint32-p x3)
        (er26-valid-rd-p a1 1))
       (er26-sorted-range-p
        (er26-shift-sint32 a i3)
        0
        x1))))))

(value-triple :itpeval-statement-checked)

:q
