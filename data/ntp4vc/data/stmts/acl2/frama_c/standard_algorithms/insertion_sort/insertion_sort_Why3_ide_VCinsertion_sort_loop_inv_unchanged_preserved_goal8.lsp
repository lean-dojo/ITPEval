;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_unchanged_preserved_goal8:
;; preservation of the insertion-sort unchanged-suffix loop invariant under
;; the stated integer bounds, memory validity, sortedness, multiset, bound,
;; equal-range, and prior unchanged-range hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun is8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun is8-address-base (address)
  (car address))

(defun is8-address-offset (address)
  (cdr address))

(defun is8-shift (address amount)
  (cons
   (is8-address-base address)
   (+ (is8-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memory
;; functions t_1, t_3, t_2, the allocation map t, and the fixed region and
;; linked symbols.

(defstub is8-t1 (address) t)
(defstub is8-t3 (address) t)
(defstub is8-t2 (address) t)
(defstub is8-allocation (index) t)
(defstub is8-region (base) t)
(defstub is8-linked-op () t)

(defun-sk is8-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (is8-address-p address)
      (and
       (integerp (is8-t1 address))
       (integerp (is8-t3 address))
       (integerp (is8-t2 address))))
     (implies
      (integerp index)
      (integerp (is8-allocation index)))
     (implies
      (integerp base)
      (integerp (is8-region base))))))

(defun is8-linked-p ()
  (if (is8-linked-op) t nil))

(defun is8-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun is8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun is8-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun is8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (is8-address-base address))
    (<= 0 (is8-address-offset address))
    (<=
     (+ (is8-address-offset address) length)
     (is8-allocation (is8-address-base address))))))

(defun is8-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (is8-address-base address)))
    (<= 0 (is8-address-offset address))
    (<=
     (+ (is8-address-offset address) length)
     (is8-allocation (is8-address-base address))))))

(defun is8-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (is8-address-base left)
     (is8-address-base right)))
   (<=
    (+ (is8-address-offset right) right-length)
    (is8-address-offset left))
   (<=
    (+ (is8-address-offset left) left-length)
    (is8-address-offset right))))

;; Pointwise forms of a_4 = havoc t_1 t_3 (shift a 0) i and
;; a_6 = havoc t_2 a_4 (shift a i_1) (1 + i_2 - i_1), using the source
;; havoc_access equation.

(defun is8-a4-value (a i query)
  (if
      (is8-separated-p
       query 1 (is8-shift a 0) i)
      (is8-t3 query)
    (is8-t1 query)))

(defun is8-a6-value (a i i1 i2 query)
  (if
      (is8-separated-p
       query 1
       (is8-shift a i1)
       (+ 1 i2 (- i1)))
      (is8-a4-value a i query)
    (is8-t2 query)))

;; Exact finite interval counts induced by A_Count.l_count_1'.  The source
;; recursion counts occurrences on [first,last), returning zero when the
;; interval is empty.

(defun is8-count-t3-span (a first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (is8-t3
           (is8-shift a (+ first (1- span))))
          value)
         1
       0)
     (is8-count-t3-span a first (1- span) value))))

(defun is8-count-t3 (a first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (is8-count-t3-span a first (- last first) value)
    0))

(defun is8-count-a4-span (a i first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (is8-a4-value
           a i
           (is8-shift a (+ first (1- span))))
          value)
         1
       0)
     (is8-count-a4-span a i first (1- span) value))))

(defun is8-count-a4 (a i first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (is8-count-a4-span a i first (- last first) value)
    0))

;; Exact unfoldings of the insertion-sort predicates used by this VC.

(defun-sk is8-sorted-a4-p (a i upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right))
     (implies
      (and
       (< right upper)
       (<= 0 left)
       (< left right))
      (<=
       (is8-a4-value a i (is8-shift a left))
       (is8-a4-value a i (is8-shift a right)))))))

(defun-sk is8-a4-t3-unchanged-p (a i lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (is8-t3 (is8-shift a index))
       (is8-a4-value a i (is8-shift a index)))))))

(defun-sk is8-multiset-unchanged-p (a i first last)
  (forall (value)
    (implies
     (integerp value)
     (implies
      (is8-is-sint32-p value)
      (equal
       (is8-count-t3 a first last value)
       (is8-count-a4 a i first last value))))))

(defun-sk is8-upperbound-a4-p (a i lower upper value)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<=
       (is8-a4-value a i (is8-shift a index))
       value)))))

(defun-sk is8-strictlowerbound-a4-p
    (a i lower upper value)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (<
       value
       (is8-a4-value a i (is8-shift a index)))))))

;; p_equalranges_4' a_6 a_4 base m n p says that a_4 on
;; shift(base,m)+[0,n-m) equals a_6 on shift(base,p)+[0,n-m).

(defun-sk is8-equalranges-a6-a4-p
    (a i i1 i2 base lower upper offset)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (- upper lower)))
      (equal
       (is8-a4-value
        a i
        (is8-shift
         (is8-shift base lower)
         index))
       (is8-a6-value
        a i i1 i2
        (is8-shift
         (is8-shift base offset)
         index)))))))

(defun-sk is8-a6-t3-unchanged-p
    (a i i1 i2 lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (is8-t3 (is8-shift a index))
       (is8-a6-value
        a i i1 i2
        (is8-shift a index)))))))

(defun is8-goal-body (i2 i1 a i)
  (implies
   (and
    (is8-function-types-p)
    (integerp i2)
    (integerp i1)
    (is8-address-p a)
    (integerp i))
   (let*
       ((x1 (- i2 i1))
        (x2 (+ 1 i2))
        (a1 (is8-shift a 0))
        (a2 (is8-shift a i2))
        (a3 (is8-shift a i1))
        (x3 (+ 1 i2 (- i1)))
        (a5 (is8-a4-value a i a2)))
     (implies
      (and
       (<= i2 i)
       (<= 0 i1)
       (<= 0 i2)
       (< i2 i)
       (<= i1 i2)
       (<= (is8-region (is8-address-base a)) 0)
       (<= i2 4294967294)
       (<= i2 (+ 4294967295 i1))
       (<= (is8-to-uint32 x1) 4294967294)
       (is8-linked-p)
       (is8-is-uint32-p i)
       (is8-is-uint32-p i1)
       (is8-is-uint32-p i2)
       (is8-is-uint32-p x2)
       (is8-valid-rd-p a1 i2)
       (is8-valid-rd-p a2 1)
       (is8-valid-rw-p a1 i)
       (is8-valid-rw-p a3 x3)
       (is8-is-sint32-p a5)
       (is8-sorted-a4-p a i i2)
       (is8-a4-t3-unchanged-p a i i2 i)
       (is8-multiset-unchanged-p a i 0 i2)
       (is8-upperbound-a4-p a i 0 i1 a5)
       (is8-strictlowerbound-a4-p
        a i i1 i2 a5)
       (is8-equalranges-a6-a4-p
        a i i1 i2 a3 0 x1 1)
       (is8-equalranges-a6-a4-p
        a i i1 i2 a3 x1 x3 0))
      (is8-a6-t3-unchanged-p
       a i i1 i2 x2 i)))))

(defun-sk
    ntp4vc-insertion-sort-loop-inv-unchanged-preserved-goal8-statement
    ()
  (forall (i2 i1 a i)
    (is8-goal-body i2 i1 a i)))

(value-triple :itpeval-statement-checked)

:q
