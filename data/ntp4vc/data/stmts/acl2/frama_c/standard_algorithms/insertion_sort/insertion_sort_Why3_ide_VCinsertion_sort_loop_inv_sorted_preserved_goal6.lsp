;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_sorted_preserved_goal6:
;; preservation of the insertion-sort sortedness invariant after the stated
;; havoc-based memory rearrangement, under the integer-bound, memory-validity,
;; unchanged-range, multiset, and value-bound hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun isg6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun isg6-address-base (address)
  (car address))

(defun isg6-address-offset (address)
  (cdr address))

(defun isg6-shift (address amount)
  (cons
   (isg6-address-base address)
   (+ (isg6-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_2, t_3, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub isg6-t1 (address) t)
(defstub isg6-t2 (address) t)
(defstub isg6-t3 (address) t)
(defstub isg6-allocation (index) t)
(defstub isg6-region (base) t)
(defstub isg6-linked-op () t)

(defun-sk isg6-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (isg6-address-p address)
      (and
       (integerp (isg6-t1 address))
       (integerp (isg6-t2 address))
       (integerp (isg6-t3 address))))
     (implies
      (integerp index)
      (integerp (isg6-allocation index)))
     (implies
      (integerp base)
      (integerp (isg6-region base))))))

(defun isg6-linked-p ()
  (if (isg6-linked-op) t nil))

(defun isg6-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun isg6-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun isg6-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun isg6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (isg6-address-base address))
    (<= 0 (isg6-address-offset address))
    (<=
     (+ (isg6-address-offset address) length)
     (isg6-allocation (isg6-address-base address))))))

(defun isg6-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (isg6-address-base address)))
    (<= 0 (isg6-address-offset address))
    (<=
     (+ (isg6-address-offset address) length)
     (isg6-allocation (isg6-address-base address))))))

(defun isg6-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (isg6-address-base left)
     (isg6-address-base right)))
   (<=
    (+ (isg6-address-offset right) right-length)
    (isg6-address-offset left))
   (<=
    (+ (isg6-address-offset left) left-length)
    (isg6-address-offset right))))

;; Exact pointwise values of
;; a_4 = havoc t_1 t_3 (shift a 0) i and
;; a_6 = havoc t_2 a_4 (shift a i_1) (1 + i_2 - i_1).

(defun isg6-a4-read (address a i)
  (if
      (isg6-separated-p
       address 1 (isg6-shift a 0) i)
      (isg6-t3 address)
    (isg6-t1 address)))

(defun isg6-a6-read (address a i1 i2 i)
  (let*
      ((a3 (isg6-shift a i1))
       (x3 (- (+ 1 i2) i1)))
    (if
        (isg6-separated-p address 1 a3 x3)
        (isg6-a4-read address a i)
      (isg6-t2 address))))

;; The two memory views occurring in the source occurrence-count predicate.

(defun isg6-view-read (view address a i1 i2 i)
  (declare (ignore i1 i2))
  (if
      (equal view 0)
      (isg6-t3 address)
    (isg6-a4-read address a i)))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is the exact characterization given by the
;; source empty, hit, and miss equations.

(defun isg6-count
    (view a i1 i2 i lower upper value)
  (declare
   (xargs
    :measure (nfix (- upper lower))))
  (if
      (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (let ((last (- upper 1)))
        (+
         (if
             (equal
              (isg6-view-read
               view (isg6-shift a last) a i1 i2 i)
              value)
             1
           0)
         (isg6-count
          view a i1 i2 i lower last value)))
    0))

;; Exact unfoldings of the sorted, unchanged, bound, equal-range, and
;; multiset-unchanged predicates over all mathematical integer indices.

(defun-sk isg6-sorted-a4-p (a upper i)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= 0 left)
      (< left right))
     (<=
      (isg6-a4-read (isg6-shift a left) a i)
      (isg6-a4-read (isg6-shift a right) a i)))))

(defun-sk isg6-sorted-a6-p (a upper i1 i2 i)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= 0 left)
      (< left right))
     (<=
      (isg6-a6-read (isg6-shift a left) a i1 i2 i)
      (isg6-a6-read (isg6-shift a right) a i1 i2 i)))))

(defun-sk isg6-unchanged-a4-t3-p (a lower upper i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (isg6-t3 (isg6-shift a index))
      (isg6-a4-read (isg6-shift a index) a i)))))

(defun-sk isg6-upper-bound-a4-p
    (a lower upper value i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (isg6-a4-read (isg6-shift a index) a i)
      value))))

(defun-sk isg6-strict-lower-bound-a4-p
    (a lower upper value i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      value
      (isg6-a4-read (isg6-shift a index) a i)))))

(defun-sk isg6-equalranges-a6-a4-p
    (base lower upper source-offset a i1 i2 i)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (- upper lower)))
     (equal
      (isg6-a4-read
       (isg6-shift
        (isg6-shift base lower)
        index)
       a i)
      (isg6-a6-read
       (isg6-shift
        (isg6-shift base source-offset)
        index)
       a i1 i2 i)))))

(defun-sk isg6-multiset-a4-t3-p
    (a lower upper i1 i2 i)
  (forall (value)
    (implies
     (and
      (integerp value)
      (isg6-is-sint32-p value))
     (equal
      (isg6-count 1 a i1 i2 i lower upper value)
      (isg6-count 0 a i1 i2 i lower upper value)))))

(defun-sk
    ntp4vc-insertion-sort-loop-inv-sorted-preserved-goal6-statement ()
  (forall
   (i2 i1 a i)
   (implies
    (and
     (integerp i2)
     (integerp i1)
     (isg6-address-p a)
     (integerp i)
     (isg6-function-types-p))
    (let*
        ((x1 (- i2 i1))
         (x2 (+ 1 i2))
         (a1 (isg6-shift a 0))
         (a2 (isg6-shift a i2))
         (a3 (isg6-shift a i1))
         (x3 (- (+ 1 i2) i1))
         (a5 (isg6-a4-read a2 a i)))
      (implies
       (and
        (<= i2 i)
        (<= 0 i1)
        (<= 0 i2)
        (< i2 i)
        (<= i1 i2)
        (<= (isg6-region (isg6-address-base a)) 0)
        (<= i2 4294967294)
        (<= i2 (+ 4294967295 i1))
        (<= (isg6-to-uint32 x1) 4294967294)
        (isg6-linked-p)
        (isg6-is-uint32-p i)
        (isg6-is-uint32-p i1)
        (isg6-is-uint32-p i2)
        (isg6-is-uint32-p x2)
        (isg6-valid-rd-p a1 i2)
        (isg6-valid-rd-p a2 1)
        (isg6-valid-rw-p a1 i)
        (isg6-valid-rw-p a3 x3)
        (isg6-is-sint32-p a5)
        (isg6-sorted-a4-p a i2 i)
        (isg6-unchanged-a4-t3-p a i2 i i)
        (isg6-multiset-a4-t3-p a 0 i2 i1 i2 i)
        (isg6-upper-bound-a4-p a 0 i1 a5 i)
        (isg6-strict-lower-bound-a4-p
         a i1 i2 a5 i)
        (isg6-equalranges-a6-a4-p
         a3 0 x1 1 a i1 i2 i)
        (isg6-equalranges-a6-a4-p
         a3 x1 x3 0 a i1 i2 i))
       (isg6-sorted-a6-p
        a x2 i1 i2 i))))))

(value-triple :itpeval-statement-checked)

:q
