;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_right_goal3:
;; the strict lower-bound property of the right suffix produced by an
;; equal-range midpoint step, preserving exact C signed-32 address shifts,
;; Why3 integer division, abstract uint32 conversion laws, sorted/value bounds,
;; linkedness, branch state, and memory readability. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source size-type pairs and addresses are exactly pairs of mathematical
;; integers.

(defun erpr3-size-type-pair-p (pair)
  (and
   (consp pair)
   (integerp (car pair))
   (integerp (cdr pair))))

(defun erpr3-pair-first (pair)
  (car pair))

(defun erpr3-pair-second (pair)
  (cdr pair))

(defun erpr3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun erpr3-address-base (address)
  (car address))

(defun erpr3-address-offset (address)
  (cdr address))

(defun erpr3-shift (address amount)
  (cons
   (erpr3-address-base address)
   (+ (erpr3-address-offset address) amount)))

;; Memory.shift_sint32 advances by one logical memory cell per array index.

(defun erpr3-shift-sint32 (address index)
  (erpr3-shift address index))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, and linked predicate
;; specialized to t, together with the imported Cint.to_uint32 operation.

(defstub erpr3-integer-memory (address) t)
(defstub erpr3-allocation (index) t)
(defstub erpr3-region (base) t)
(defstub erpr3-linked-op () t)
(defstub erpr3-to-uint32 (value) t)

(defun-sk erpr3-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (erpr3-address-p address)
      (integerp (erpr3-integer-memory address)))
     (implies
      (integerp index)
      (integerp (erpr3-allocation index)))
     (implies
      (integerp base)
      (integerp (erpr3-region base)))
     (implies
      (integerp value)
      (integerp (erpr3-to-uint32 value))))))

(defun erpr3-linked-p ()
  (if (erpr3-linked-op) t nil))

(defun erpr3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun erpr3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun erpr3-is-size-type-pair-p (pair)
  (and
   (erpr3-is-uint32-p (erpr3-pair-first pair))
   (erpr3-is-uint32-p (erpr3-pair-second pair))))

;; Exact imported Cint laws is_to_uint32, id_uint32, and proj_uint32 for the
;; arbitrary conversion function.

(defun-sk erpr3-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (erpr3-is-uint32-p (erpr3-to-uint32 value))
      (implies
       (erpr3-is-uint32-p value)
       (equal (erpr3-to-uint32 value) value))
      (equal
       (erpr3-to-uint32 (erpr3-to-uint32 value))
       (erpr3-to-uint32 value))))))

;; Int.tdiv and Isabelle cdiv truncate the integer quotient toward zero.

(defun erpr3-tdiv (numerator denominator)
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

(defun erpr3-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (erpr3-address-base address)))
    (<= 0 (erpr3-address-offset address))
    (<=
     (+ (erpr3-address-offset address) length)
     (erpr3-allocation (erpr3-address-base address))))))

;; Exact unfoldings of the pinned Axiomatic range predicates over all
;; mathematical integer indices. Each source array index is translated
;; through Memory.shift_sint32.

(defun-sk erpr3-sorted-range-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
     (< left right))
     (<=
      (erpr3-integer-memory (erpr3-shift a left))
      (erpr3-integer-memory (erpr3-shift a right))))))

(defun-sk erpr3-strict-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      value
      (erpr3-integer-memory (erpr3-shift a index))))))

(defun-sk erpr3-strict-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      (erpr3-integer-memory (erpr3-shift a index))
      value))))

(defun-sk erpr3-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      value
      (erpr3-integer-memory (erpr3-shift a index))))))

(defun-sk erpr3-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      (erpr3-integer-memory (erpr3-shift a index))
      value))))

(defun-sk ntp4vc-equal-range-post-right-goal3-statement ()
  (forall
   (s i8 i10 a i7 i11 i1 i2 i3 i4 i5 i6 i9 i p1 p2 p3 p)
   (implies
    (and
     (erpr3-size-type-pair-p s)
     (integerp i8)
     (integerp i10)
     (erpr3-address-p a)
     (integerp i7)
     (integerp i11)
     (integerp i1)
     (integerp i2)
     (integerp i3)
     (integerp i4)
     (integerp i5)
     (integerp i6)
     (integerp i9)
     (integerp i)
     (booleanp p1)
     (booleanp p2)
     (booleanp p3)
     (booleanp p)
     (erpr3-function-types-p)
     (erpr3-to-uint32-laws-p))
    (let*
        ((x (erpr3-pair-first s))
         (x2 (- i8 i10))
         (x3 (erpr3-tdiv x2 2))
         (x4 (+ i10 x3))
         (x5 (erpr3-pair-second s))
         (a1 (erpr3-shift-sint32 a x4))
         (x6 (erpr3-integer-memory a1))
         (x7
          (+
           i10
            (erpr3-to-uint32
            (erpr3-tdiv (erpr3-to-uint32 x2) 2))))
         (a2 (erpr3-shift-sint32 a i10))
         (a3 (erpr3-shift-sint32 a (+ 1 i10 x3)))
         (x9 (- (- (- i8 1) i10) x3))
         (x10 (- x i10))
         (x11 (- (- (- x5 1) i10) x3)))
      (implies
       (and
        (<= i8 i7)
        (<= i11 i8)
        (<= 0 i11)
        (<= (erpr3-region (erpr3-address-base a)) 0)
        (erpr3-is-size-type-pair-p s)
        (erpr3-linked-p)
        (erpr3-is-uint32-p i1)
        (erpr3-is-uint32-p i2)
        (erpr3-is-uint32-p i3)
        (erpr3-is-uint32-p i4)
        (erpr3-is-uint32-p i5)
        (erpr3-is-uint32-p i6)
        (erpr3-is-uint32-p i7)
        (erpr3-is-uint32-p i8)
        (erpr3-is-uint32-p i9)
        (erpr3-is-uint32-p i10)
        (erpr3-is-uint32-p i11)
        (erpr3-is-sint32-p i)
        (erpr3-sorted-range-p a 0 i7)
        (erpr3-strict-upper-bound-p a 0 i11 i)
        (erpr3-strict-lower-bound-p a i8 i7 i)
        (erpr3-valid-rd-p (erpr3-shift-sint32 a 0) i7)
        (if
            (< i11 i8)
            (and
             (equal p1 nil)
             (equal p2 nil)
             (equal p3 nil)
             (equal i2 i1)
             (equal i5 i4)
             (equal i10 i9)
             (equal i11 i10)
             (equal x (+ i3 i10))
             (equal x (+ i6 i10))
             (equal x4 i4)
             (equal x4 i5)
             (equal x5 (+ 1 i1 i10 x3))
             (equal x5 (+ 1 i2 i10 x3))
             (<= x5 i8)
             (<= 0 x)
             (<= i10 x)
             (<= 0 x5)
             (<= 0 x3)
             (< x4 i8)
             (<= x x4)
             (< x4 x5)
             (<= x6 i)
             (<= 0 x7)
             (<= i x6)
             (<= x 4294967295)
             (<= x5 4294967295)
             (<= i8 (+ 4294967295 i10))
             (<= x3 4294967295)
             (<= x4 4294967294)
             (<= i8 (+ 4294967296 i10 x3))
             (<= x7 4294967295)
             (erpr3-valid-rd-p a2 x3)
             (erpr3-sorted-range-p a2 0 x3)
             (erpr3-valid-rd-p a1 1)
             (erpr3-valid-rd-p a3 x9)
             (erpr3-sorted-range-p a3 0 x9)
             (erpr3-strict-upper-bound-p a2 0 x10 x6)
             (erpr3-strict-lower-bound-p a3 x11 x9 x6)
             (erpr3-lower-bound-p a2 x10 x3 x6)
             (erpr3-upper-bound-p a3 0 x11 x6))
          (and
           (equal p nil)
           (equal x i11)
           (equal x5 x))))
       (erpr3-strict-lower-bound-p a x5 i7 i))))))

(value-triple :itpeval-statement-checked)

:q
