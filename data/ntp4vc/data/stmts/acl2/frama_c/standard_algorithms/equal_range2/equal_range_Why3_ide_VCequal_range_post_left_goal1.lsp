;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_left_goal1:
;; the strict upper-bound property of the left prefix produced by an
;; equal-range midpoint step, with exact C signed-32 address shifts, Why3
;; integer division, uint32 conversion, sorted-range, value-bound, linkedness,
;; and memory-readability hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source size-type pairs and addresses are exactly pairs of mathematical
;; integers.

(defun erpl1-size-type-pair-p (pair)
  (and
   (consp pair)
   (integerp (car pair))
   (integerp (cdr pair))))

(defun erpl1-pair-first (pair)
  (car pair))

(defun erpl1-pair-second (pair)
  (cdr pair))

(defun erpl1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun erpl1-address-base (address)
  (car address))

(defun erpl1-address-offset (address)
  (cdr address))

(defun erpl1-shift (address amount)
  (cons
   (erpl1-address-base address)
   (+ (erpl1-address-offset address) amount)))

;; Memory.shift_sint32 advances by one logical memory cell per array index.

(defun erpl1-shift-sint32 (address index)
  (erpl1-shift address index))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, uint32 conversion,
;; and linked predicate specialized to t.

(defstub erpl1-integer-memory (address) t)
(defstub erpl1-allocation (index) t)
(defstub erpl1-region (base) t)
(defstub erpl1-to-uint32 (value) t)
(defstub erpl1-linked-op () t)

(defun-sk erpl1-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (erpl1-address-p address)
      (integerp (erpl1-integer-memory address)))
     (implies
      (integerp index)
      (integerp (erpl1-allocation index)))
     (implies
      (integerp base)
      (integerp (erpl1-region base)))
     (implies
      (integerp value)
      (integerp (erpl1-to-uint32 value))))))

(defun erpl1-linked-p ()
  (if (erpl1-linked-op) t nil))

(defun erpl1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun erpl1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun erpl1-is-size-type-pair-p (pair)
  (and
   (erpl1-is-uint32-p (erpl1-pair-first pair))
   (erpl1-is-uint32-p (erpl1-pair-second pair))))

;; Exact imported Cint laws is_to_uint32, id_uint32, and proj_uint32 for the
;; arbitrary conversion function.

(defun-sk erpl1-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (erpl1-is-uint32-p (erpl1-to-uint32 value))
      (implies
       (erpl1-is-uint32-p value)
       (equal (erpl1-to-uint32 value) value))
      (equal
       (erpl1-to-uint32 (erpl1-to-uint32 value))
       (erpl1-to-uint32 value))))))

;; Int.tdiv and Isabelle cdiv truncate the integer quotient toward zero.

(defun erpl1-tdiv (numerator denominator)
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

(defun erpl1-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (erpl1-address-base address)))
    (<= 0 (erpl1-address-offset address))
    (<=
     (+ (erpl1-address-offset address) length)
     (erpl1-allocation (erpl1-address-base address))))))

;; Exact unfoldings of the pinned Axiomatic range predicates over all
;; mathematical integer indices. Each source array index is translated
;; through Memory.shift_sint32.

(defun-sk erpl1-sorted-range-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
     (< left right))
     (<=
      (erpl1-integer-memory (erpl1-shift a left))
      (erpl1-integer-memory (erpl1-shift a right))))))

(defun-sk erpl1-strict-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      value
      (erpl1-integer-memory (erpl1-shift a index))))))

(defun-sk erpl1-strict-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      (erpl1-integer-memory (erpl1-shift a index))
      value))))

(defun-sk erpl1-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      value
      (erpl1-integer-memory (erpl1-shift a index))))))

(defun-sk erpl1-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      (erpl1-integer-memory (erpl1-shift a index))
      value))))

(defun-sk ntp4vc-equal-range-post-left-goal1-statement ()
  (forall
   (s i1 i3 a i2 i)
   (implies
    (and
     (erpl1-size-type-pair-p s)
     (integerp i1)
     (integerp i3)
     (erpl1-address-p a)
     (integerp i2)
     (integerp i)
     (erpl1-function-types-p)
     (erpl1-to-uint32-laws-p))
    (let*
        ((x (erpl1-pair-second s))
         (x1 (erpl1-pair-first s))
         (x2 (+ i1 i3))
         (x4 (- (+ i1 i3) x1))
         (x5 (erpl1-tdiv x4 2))
         (x6 (+ x1 x5))
         (x7
          (+
           x1
           (erpl1-to-uint32
            (erpl1-tdiv (erpl1-to-uint32 x4) 2))))
         (x9 (- (+ x1 x5) i1))
         (a1 (erpl1-shift-sint32 a x9))
         (x10 (erpl1-integer-memory a1))
         (x11 (- x1 i1))
         (a2 (erpl1-shift-sint32 a x11))
         (x12 (- (+ 1 x1 x5) i1))
         (x14 (- (- (- (+ i1 x) 1) x1) x5))
         (a3 (erpl1-shift-sint32 a x12))
         (x15 (- (- (- (+ i1 i3) 1) x1) x5)))
      (implies
       (and
        (<= 0 i1)
        (<= i3 i2)
        (<= x i3)
        (<= 0 x1)
        (<= i1 x1)
        (<= 0 x)
        (< x1 x2)
        (<= (erpl1-region (erpl1-address-base a)) 0)
        (<= 0 x5)
        (<= i1 x5)
        (< x6 x2)
        (< x6 (+ i1 x))
        (<= i1 x7)
        (<= x10 i)
        (<= i x10)
        (<= x1 4294967295)
        (<= x 4294967295)
        (<= x2 (+ 4294967295 x1))
        (<= x5 4294967295)
        (<= x6 (+ 4294967294 i1))
        (<= x2 (+ 4294967296 x1 x5))
        (<= x7 (+ 4294967295 i1))
        (erpl1-is-size-type-pair-p s)
        (erpl1-linked-p)
        (erpl1-is-uint32-p i1)
        (erpl1-is-uint32-p i2)
        (erpl1-is-uint32-p i3)
        (erpl1-is-sint32-p i)
        (erpl1-is-uint32-p x1)
        (erpl1-is-uint32-p x)
        (erpl1-sorted-range-p a 0 i2)
        (erpl1-is-uint32-p x11)
        (erpl1-strict-lower-bound-p a i3 i2 i)
        (erpl1-valid-rd-p (erpl1-shift-sint32 a 0) i2)
        (erpl1-strict-upper-bound-p a 0 x11 i)
        (erpl1-valid-rd-p a2 x5)
        (erpl1-sorted-range-p a2 0 x5)
        (erpl1-is-uint32-p x9)
        (erpl1-is-uint32-p x12)
        (erpl1-is-uint32-p x14)
        (erpl1-is-sint32-p x10)
        (erpl1-valid-rd-p a1 1)
        (erpl1-valid-rd-p a3 x15)
        (erpl1-sorted-range-p a3 0 x15)
        (erpl1-strict-upper-bound-p a2 0 i1 x10)
        (erpl1-strict-lower-bound-p a3 x14 x15 x10)
        (erpl1-lower-bound-p a2 i1 x5 x10)
        (erpl1-upper-bound-p a3 0 x14 x10))
       (erpl1-strict-upper-bound-p a 0 x1 x10))))))

(value-triple :itpeval-statement-checked)

:q
