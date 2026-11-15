;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/reverse/reverse_Why3_ide_VCreverse_loop_inv_right_preserved_goal7:
;; preservation of the right-hand reverse loop invariant after swapping two
;; values in a havoc-derived integer memory, under the stated bounds,
;; linkedness, validity, integer-range, unchanged-range, and prior reverse
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun rrg7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rrg7-address-base (address)
  (car address))

(defun rrg7-address-offset (address)
  (cdr address))

;; Compound.shift_sint32 is defined in the pinned source as Memory.shift,
;; so one logical array step adds one to the address offset.

(defun rrg7-shift (address amount)
  (cons
   (rrg7-address-base address)
   (+ (rrg7-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub rrg7-t1 (address) t)
(defstub rrg7-t2 (address) t)
(defstub rrg7-allocation (index) t)
(defstub rrg7-region (base) t)
(defstub rrg7-linked-op () t)
(defstub rrg7-to-uint32 (value) t)

(defun-sk rrg7-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (rrg7-address-p address)
      (and
       (integerp (rrg7-t1 address))
       (integerp (rrg7-t2 address))))
     (implies
      (integerp index)
      (integerp (rrg7-allocation index)))
     (implies
      (integerp base)
      (integerp (rrg7-region base)))
     (implies
      (integerp value)
      (integerp (rrg7-to-uint32 value))))))

(defun rrg7-linked-p ()
  (if (rrg7-linked-op) t nil))

(defun rrg7-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun rrg7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Imported Cint laws is_to_uint32, id_uint32, and proj_uint32.

(defun-sk rrg7-to-uint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (rrg7-is-uint32-p (rrg7-to-uint32 value))
      (implies
       (rrg7-is-uint32-p value)
       (equal (rrg7-to-uint32 value) value))
      (equal
       (rrg7-to-uint32 (rrg7-to-uint32 value))
       (rrg7-to-uint32 value))))))

;; The pinned Why3 int.ComputerDivision.div truncates toward zero.

(defun rrg7-tdiv (numerator denominator)
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

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun rrg7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rrg7-address-base address))
    (<= 0 (rrg7-address-offset address))
    (<=
     (+ (rrg7-address-offset address) length)
     (rrg7-allocation (rrg7-address-base address))))))

(defun rrg7-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (rrg7-address-base left)
     (rrg7-address-base right)))
   (<=
    (+ (rrg7-address-offset right) right-length)
    (rrg7-address-offset left))
   (<=
    (+ (rrg7-address-offset left) left-length)
    (rrg7-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_1 t_2 (shift a 0) i_1, using Memory.havoc_access.

(defun rrg7-a2-read (a i1 query)
  (if
      (rrg7-separated-p
       query 1 (rrg7-shift a 0) i1)
      (rrg7-t2 query)
    (rrg7-t1 query)))

;; Exact pointwise value of
;; a_6 = update (update a_2 a_3 i) a_4 a_5.
;; The outer update at a_4 takes precedence when a_3 = a_4.

(defun rrg7-a6-read (a i1 i2 i query)
  (let*
      ((x1 (- (- i1 1) i2))
       (a3 (rrg7-shift a x1))
       (a4 (rrg7-shift a i2))
       (a5 (rrg7-a2-read a i1 a3)))
    (if (equal query a4)
        a5
      (if (equal query a3)
          i
        (rrg7-a2-read a i1 query)))))

;; The only two derived memories used as the first argument of p_reverse_4'.

(defun rrg7-view-read (view a i1 i2 i query)
  (if (equal view 0)
      (rrg7-a2-read a i1 query)
    (rrg7-a6-read a i1 i2 i query)))

;; Exact unfolding of Axiomatic.p_unchanged_1' over all mathematical integer
;; indices.

(defun-sk rrg7-unchanged-a2-t2-p
    (a i1 lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (rrg7-t2 (rrg7-shift a index))
      (rrg7-a2-read a i1 (rrg7-shift a index))))))

;; Exact unfolding of Axiomatic.p_reverse_4'.  View 0 denotes a_2 and view 1
;; denotes a_6; the second memory is t_2 in every occurrence in this VC.

(defun-sk rrg7-reverse-p
    (view a i1 i2 i lower upper destination-offset)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (- upper lower)))
     (equal
      (rrg7-view-read
       view a i1 i2 i
       (rrg7-shift
        (rrg7-shift a destination-offset)
        (- (- (- upper lower) 1) index)))
      (rrg7-t2
       (rrg7-shift
        (rrg7-shift a lower)
        index))))))

(defun-sk
    ntp4vc-reverse-loop-inv-right-preserved-goal7-statement ()
  (forall
   (a i1 i2 i)
   (implies
    (and
     (rrg7-address-p a)
     (integerp i1)
     (integerp i2)
     (integerp i)
     (rrg7-function-types-p)
     (rrg7-to-uint32-laws-p))
    (let*
        ((a1 (rrg7-shift a 0))
         (x1 (- (- i1 1) i2))
         (a3 (rrg7-shift a x1))
         (a4 (rrg7-shift a i2))
         (a5 (rrg7-a2-read a i1 a3))
         (a7 (rrg7-a6-read a i1 i2 i a3))
         (a8 (rrg7-a2-read a i1 a4))
         (x2 (rrg7-tdiv i1 2))
         (x3 (rrg7-to-uint32 (- i1 1)))
         (x4 (- i1 i2)))
      (implies
       (and
        (equal a7 a8)
        (< 0 i1)
        (<= 0 i2)
        (< i2 x2)
        (<= i2 x2)
        (<= (rrg7-region (rrg7-address-base a)) 0)
        (<= (+ i2 x2) i1)
        (<= i2 x3)
        (<= i2 4294967294)
        (<= x3 (+ 4294967295 i2))
        (rrg7-linked-p)
        (rrg7-is-uint32-p i1)
        (rrg7-is-uint32-p i2)
        (rrg7-is-uint32-p x2)
        (rrg7-is-uint32-p (+ 1 i2))
        (rrg7-valid-rw-p a1 i1)
        (rrg7-valid-rw-p a4 1)
        (rrg7-is-sint32-p a8)
        (rrg7-is-sint32-p a5)
        (rrg7-valid-rw-p a3 1)
        (rrg7-is-sint32-p a7)
        (rrg7-unchanged-a2-t2-p a i1 i2 x4)
        (rrg7-reverse-p 0 a i1 i2 i 0 i2 x4)
        (rrg7-reverse-p 0 a i1 i2 i x4 i1 0))
       (rrg7-reverse-p
        1 a i1 i2 i x1 i1 0))))))

(value-triple :itpeval-statement-checked)

:q
