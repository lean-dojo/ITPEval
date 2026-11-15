;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_post_sorted_goal0:
;; sortedness of the initialized selection-sort prefix after havocing the
;; same array segment, under the stated index bounds, memory validity,
;; integer ranges, prior sortedness, multiset, and conditional lower-bound
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ssps0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ssps0-address-base (address)
  (car address))

(defun ssps0-address-offset (address)
  (cdr address))

(defun ssps0-shift (address amount)
  (cons
   (ssps0-address-base address)
   (+ (ssps0-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub ssps0-t1 (address) t)
(defstub ssps0-t2 (address) t)
(defstub ssps0-allocation (index) t)
(defstub ssps0-region (base) t)
(defstub ssps0-linked-op () t)

(defun-sk ssps0-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (ssps0-address-p address)
      (and
       (integerp (ssps0-t1 address))
       (integerp (ssps0-t2 address))))
     (implies
      (integerp index)
      (integerp (ssps0-allocation index)))
     (implies
      (integerp base)
      (integerp (ssps0-region base))))))

(defun ssps0-linked-p ()
  (if (ssps0-linked-op) t nil))

(defun ssps0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ssps0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun ssps0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ssps0-address-base address))
    (<= 0 (ssps0-address-offset address))
    (<=
     (+ (ssps0-address-offset address) length)
     (ssps0-allocation (ssps0-address-base address))))))

(defun ssps0-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (ssps0-address-base left)
     (ssps0-address-base right)))
   (<=
    (+ (ssps0-address-offset right) right-length)
    (ssps0-address-offset left))
   (<=
    (+ (ssps0-address-offset left) left-length)
    (ssps0-address-offset right))))

;; Exact pointwise value of Memory.havoc t_1 t_2 (shift a 0) length,
;; using the source havoc_access equation.

(defun ssps0-havoc-read (query a length)
  (if
      (ssps0-separated-p
       query 1 (ssps0-shift a 0) length)
      (ssps0-t2 query)
    (ssps0-t1 query)))

;; Exact unfolding of Axiomatic1.p_sorted_1' over every pair of
;; mathematical integer indices.

(defun-sk ssps0-sorted-p (a lower upper length)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (ssps0-havoc-read
       (ssps0-shift a left) a length)
      (ssps0-havoc-read
       (ssps0-shift a right) a length)))))

;; Exact unfolding of Axiomatic1.p_lowerbound_1' over every mathematical
;; integer index.

(defun-sk ssps0-lower-bound-p
    (a lower upper value length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (ssps0-havoc-read
       (ssps0-shift a index) a length)))))

;; The two memory views occurring in p_multisetunchanged_1': t_2 and the
;; havoced view a_2.

(defun ssps0-view-read (view query a length)
  (if
      (equal view 0)
      (ssps0-t2 query)
    (ssps0-havoc-read query a length)))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun ssps0-count
    (view a length lower upper value)
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
              (ssps0-view-read
               view (ssps0-shift a last) a length)
              value)
             1
           0)
         (ssps0-count
          view a length lower last value)))
    0))

(defun-sk ssps0-multiset-unchanged-p
    (a length lower upper)
  (forall (value)
    (implies
     (ssps0-is-sint32-p value)
     (equal
      (ssps0-count 0 a length lower upper value)
      (ssps0-count 1 a length lower upper value)))))

(defun-sk ntp4vc-selection-sort-post-sorted-goal0-statement ()
  (forall
   (a i i1)
   (implies
    (and
     (ssps0-address-p a)
     (integerp i)
     (integerp i1)
     (ssps0-function-types-p))
    (let*
        ((a1 (ssps0-shift a 0))
         (a3
          (ssps0-havoc-read
           (ssps0-shift a (- i1 1)) a i)))
      (implies
       (and
        (<= i1 i)
        (<= 0 i1)
        (<= i i1)
        (<= (ssps0-region (ssps0-address-base a)) 0)
        (ssps0-linked-p)
        (ssps0-is-uint32-p i)
        (ssps0-is-uint32-p i1)
        (ssps0-is-sint32-p
         (ssps0-t2 (ssps0-shift a -1)))
        (ssps0-valid-rw-p a1 i)
        (ssps0-is-sint32-p a3)
        (ssps0-sorted-p a 0 i1 i)
        (ssps0-multiset-unchanged-p a i 0 i)
        (implies
         (< 0 i1)
         (ssps0-lower-bound-p a i1 i a3 i)))
       (ssps0-sorted-p a 0 i1 i1))))))

(value-triple :itpeval-statement-checked)

:q
