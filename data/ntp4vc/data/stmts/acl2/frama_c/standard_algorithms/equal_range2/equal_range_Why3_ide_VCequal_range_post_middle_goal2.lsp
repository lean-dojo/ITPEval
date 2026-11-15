;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/equal_range2/equal_range_Why3_ide_VCequal_range_post_middle_goal2:
;; constancy of the middle range produced by an equal-range midpoint step,
;; preserving exact C signed-32 address shifts, Why3 integer division, abstract
;; uint32 conversion laws, sorted/value bounds, linkedness, branch state, and
;; memory readability. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source size-type pairs and addresses are exactly pairs of mathematical
;; integers.

(defun erpm2-size-type-pair-p (pair)
  (and
   (consp pair)
   (integerp (car pair))
   (integerp (cdr pair))))

(defun erpm2-pair-first (pair)
  (car pair))

(defun erpm2-pair-second (pair)
  (cdr pair))

(defun erpm2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun erpm2-address-base (address)
  (car address))

(defun erpm2-address-offset (address)
  (cdr address))

(defun erpm2-shift (address amount)
  (cons
   (erpm2-address-base address)
   (+ (erpm2-address-offset address) amount)))

(defun erpm2-shift-sint32 (address index)
  (erpm2-shift address index))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, allocation map t, region function, linked predicate
;; specialized to t, and imported Cint.to_uint32 operation.

(defstub erpm2-integer-memory (address) t)
(defstub erpm2-allocation (index) t)
(defstub erpm2-region (base) t)
(defstub erpm2-linked-op () t)
(defstub erpm2-to-uint32 (value) t)

(defun-sk erpm2-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (erpm2-address-p address)
      (integerp (erpm2-integer-memory address)))
     (implies
     (integerp index)
      (integerp (erpm2-allocation index)))
     (implies
      (integerp base)
      (integerp (erpm2-region base)))
     (implies
      (integerp value)
      (integerp (erpm2-to-uint32 value))))))

(defun erpm2-linked-p ()
  (if (erpm2-linked-op) t nil))

(defun erpm2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun erpm2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun erpm2-is-size-type-pair-p (pair)
  (and
   (erpm2-is-uint32-p (erpm2-pair-first pair))
   (erpm2-is-uint32-p (erpm2-pair-second pair))))

;; Exact imported Cint laws: is_to_uint32, id_uint32, and proj_uint32.

(defun-sk erpm2-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (erpm2-is-uint32-p (erpm2-to-uint32 value))
      (implies
       (erpm2-is-uint32-p value)
       (equal (erpm2-to-uint32 value) value))
      (equal
       (erpm2-to-uint32 (erpm2-to-uint32 value))
       (erpm2-to-uint32 value))))))

;; Int.tdiv and Isabelle cdiv truncate the integer quotient toward zero.

(defun erpm2-tdiv (numerator denominator)
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

(defun erpm2-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (erpm2-address-base address)))
    (<= 0 (erpm2-address-offset address))
    (<=
     (+ (erpm2-address-offset address) length)
     (erpm2-allocation (erpm2-address-base address))))))

;; Exact unfoldings of the source range predicates over all mathematical
;; integer indices.

(defun-sk erpm2-sorted-range-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
     (< left right))
     (<=
      (erpm2-integer-memory (erpm2-shift a left))
      (erpm2-integer-memory (erpm2-shift a right))))))

(defun-sk erpm2-strict-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      value
      (erpm2-integer-memory (erpm2-shift a index))))))

(defun-sk erpm2-strict-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<
      (erpm2-integer-memory (erpm2-shift a index))
      value))))

(defun-sk erpm2-lower-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      value
      (erpm2-integer-memory (erpm2-shift a index))))))

(defun-sk erpm2-upper-bound-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (<=
      (erpm2-integer-memory (erpm2-shift a index))
      value))))

(defun-sk erpm2-constant-range-p (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
     (< index upper))
     (equal
      (erpm2-integer-memory (erpm2-shift a index))
      value))))

(defun-sk ntp4vc-equal-range-post-middle-goal2-statement ()
  (forall
   (s i8 i10 a i7 i11 i1 i2 i3 i4 i5 i6 i9 i p1 p2 p3 p)
   (implies
    (and
     (erpm2-size-type-pair-p s)
     (integerp i8)
     (integerp i10)
     (erpm2-address-p a)
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
     (erpm2-function-types-p)
     (erpm2-to-uint32-laws-p))
    (let*
        ((x (erpm2-pair-first s))
         (x2 (- i8 i10))
         (x3 (erpm2-tdiv x2 2))
         (x4 (+ i10 x3))
         (x5 (erpm2-pair-second s))
         (a1 (erpm2-shift-sint32 a x4))
         (x6 (erpm2-integer-memory a1))
         (x7
          (+
           i10
           (erpm2-to-uint32
            (erpm2-tdiv (erpm2-to-uint32 x2) 2))))
         (a2 (erpm2-shift-sint32 a i10))
         (a3 (erpm2-shift-sint32 a (+ 1 i10 x3)))
         (x9 (- (- (- i8 1) i10) x3))
         (x10 (- x i10))
         (x11 (- (- (- x5 1) i10) x3)))
      (implies
       (and
        (<= i8 i7)
        (<= i11 i8)
        (<= 0 i11)
        (<= (erpm2-region (erpm2-address-base a)) 0)
        (erpm2-is-size-type-pair-p s)
        (erpm2-linked-p)
        (erpm2-is-uint32-p i1)
        (erpm2-is-uint32-p i2)
        (erpm2-is-uint32-p i3)
        (erpm2-is-uint32-p i4)
        (erpm2-is-uint32-p i5)
        (erpm2-is-uint32-p i6)
        (erpm2-is-uint32-p i7)
        (erpm2-is-uint32-p i8)
        (erpm2-is-uint32-p i9)
        (erpm2-is-uint32-p i10)
        (erpm2-is-uint32-p i11)
        (erpm2-is-sint32-p i)
        (erpm2-sorted-range-p a 0 i7)
        (erpm2-strict-upper-bound-p a 0 i11 i)
        (erpm2-strict-lower-bound-p a i8 i7 i)
        (erpm2-valid-rd-p (erpm2-shift-sint32 a 0) i7)
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
             (erpm2-valid-rd-p a2 x3)
             (erpm2-sorted-range-p a2 0 x3)
             (erpm2-valid-rd-p a1 1)
             (erpm2-valid-rd-p a3 x9)
             (erpm2-sorted-range-p a3 0 x9)
             (erpm2-strict-upper-bound-p a2 0 x10 x6)
             (erpm2-strict-lower-bound-p a3 x11 x9 x6)
             (erpm2-lower-bound-p a2 x10 x3 x6)
             (erpm2-upper-bound-p a3 0 x11 x6))
          (and
           (equal p nil)
           (equal x i11)
           (equal x5 x))))
       (erpm2-constant-range-p a x x5 i))))))

(value-triple :itpeval-statement-checked)

:q
