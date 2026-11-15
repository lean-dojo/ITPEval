;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1:
;; the partial-sort postcondition that the final memory is partitioned at the
;; selected index, under the stated bounds, memory, heap, sortedness,
;; multiset, unchanged-range, and upper/lower-bound hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun pspp1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun pspp1-address-base (address)
  (car address))

(defun pspp1-address-offset (address)
  (cdr address))

(defun pspp1-shift (address amount)
  (cons
   (pspp1-address-base address)
   (+ (pspp1-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_6, t_3, t_5, t_2, t_8, t_4, and t_7; the allocation maps t and t_1;
;; the region function; and the linked predicate specialized to t.

(defstub pspp1-t6 (address) t)
(defstub pspp1-t3 (address) t)
(defstub pspp1-t5 (address) t)
(defstub pspp1-t2 (address) t)
(defstub pspp1-t8 (address) t)
(defstub pspp1-t4 (address) t)
(defstub pspp1-t7 (address) t)
(defstub pspp1-allocation (index) t)
(defstub pspp1-allocation1 (index) t)
(defstub pspp1-region (base) t)
(defstub pspp1-linked-op () t)

(defun-sk pspp1-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (pspp1-address-p address)
      (and
       (integerp (pspp1-t6 address))
       (integerp (pspp1-t3 address))
       (integerp (pspp1-t5 address))
       (integerp (pspp1-t2 address))
       (integerp (pspp1-t8 address))
       (integerp (pspp1-t4 address))
       (integerp (pspp1-t7 address))))
     (implies
      (integerp index)
      (and
       (integerp (pspp1-allocation index))
       (integerp (pspp1-allocation1 index))))
     (implies
      (integerp base)
      (integerp (pspp1-region base))))))

(defun pspp1-linked-p ()
  (if (pspp1-linked-op) t nil))

(defun pspp1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun pspp1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun pspp1-valid-rw-p (allocation-view address length)
  (implies
   (< 0 length)
   (and
    (< 0 (pspp1-address-base address))
    (<= 0 (pspp1-address-offset address))
    (<=
     (+ (pspp1-address-offset address) length)
     (if (equal allocation-view 1)
         (pspp1-allocation1
          (pspp1-address-base address))
       (pspp1-allocation
        (pspp1-address-base address)))))))

(defun pspp1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (pspp1-address-base left)
     (pspp1-address-base right)))
   (<=
    (+ (pspp1-address-offset right) right-length)
    (pspp1-address-offset left))
   (<=
    (+ (pspp1-address-offset left) left-length)
    (pspp1-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_3 t_5 (shift a 0) i_2,
;; using the source havoc_access equation.

(defun pspp1-a2-read (query a i2)
  (if
      (pspp1-separated-p
       query 1 (pspp1-shift a 0) i2)
      (pspp1-t5 query)
    (pspp1-t3 query)))

;; Source equalities between function values are represented extensionally on
;; their complete typed domains.

(defun-sk pspp1-allocation1-equals-allocation-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal
      (pspp1-allocation1 index)
      (pspp1-allocation index)))))

(defun-sk pspp1-havoc-t2-t8-equals-t5-p (a i1)
  (forall (query)
    (implies
     (pspp1-address-p query)
     (equal
      (if
          (pspp1-separated-p
           query 1 (pspp1-shift a 0) i1)
          (pspp1-t8 query)
        (pspp1-t2 query))
      (pspp1-t5 query)))))

(defun-sk pspp1-havoc-t3-t5-equals-t6-p (a length)
  (forall (query)
    (implies
     (pspp1-address-p query)
     (equal
      (if
          (pspp1-separated-p
           query 1 (pspp1-shift a 0) length)
          (pspp1-t5 query)
        (pspp1-t3 query))
      (pspp1-t6 query)))))

(defun-sk pspp1-havoc-t4-a2-equals-t7-p (a i1 i2)
  (forall (query)
    (implies
     (pspp1-address-p query)
     (equal
      (if
          (pspp1-separated-p
           query 1 (pspp1-shift a 0) i1)
          (pspp1-a2-read query a i2)
        (pspp1-t4 query))
      (pspp1-t7 query)))))

(defun-sk pspp1-t8-equals-t7-p ()
  (forall (query)
    (implies
     (pspp1-address-p query)
     (equal
      (pspp1-t8 query)
      (pspp1-t7 query)))))

;; Tags name exactly the memory functions needed by occurrence counts:
;; 2=a_2, 5=t_5, 6=t_6, 7=t_7, and 8=t_8.

(defun pspp1-memory-read (view query a i2)
  (cond
   ((equal view 2)
    (pspp1-a2-read query a i2))
   ((equal view 5)
    (pspp1-t5 query))
   ((equal view 6)
    (pspp1-t6 query))
   ((equal view 7)
    (pspp1-t7 query))
   (t
    (pspp1-t8 query))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun pspp1-count
    (view a i2 lower upper value)
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
              (pspp1-memory-read
               view (pspp1-shift a last) a i2)
              value)
             1
           0)
         (pspp1-count
          view a i2 lower last value)))
    0))

;; Exact unfoldings of the source sortedness, heap, multiset, unchanged-range,
;; upper-bound, lower-bound, and partition predicates. Every typed source
;; quantifier remains over all mathematical integers.

(defun-sk pspp1-sorted-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (pspp1-t7 (pspp1-shift a left))
      (pspp1-t7 (pspp1-shift a right))))))

(defun-sk pspp1-isheap-p (view a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (pspp1-memory-read
       view (pspp1-shift a child) a upper)
      (pspp1-memory-read
       view
       (pspp1-shift
        a (floor (- child 1) 2))
       a upper)))))

(defun-sk pspp1-multiset-unchanged-p
    (first-view second-view a lower upper i2)
  (forall (value)
    (implies
     (pspp1-is-sint32-p value)
     (equal
      (pspp1-count
       second-view a i2 lower upper value)
      (pspp1-count
       first-view a i2 lower upper value)))))

(defun-sk pspp1-unchanged-p
    (first-view second-view a lower upper i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (pspp1-memory-read
       second-view (pspp1-shift a index) a i2)
      (pspp1-memory-read
       first-view (pspp1-shift a index) a i2)))))

(defun-sk pspp1-upperbound-p
    (view a lower upper value i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (pspp1-memory-read
       view (pspp1-shift a index) a i2)
      value))))

(defun-sk pspp1-lowerbound-p
    (view a lower upper value i2)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (pspp1-memory-read
       view (pspp1-shift a index) a i2)))))

(defun-sk pspp1-partition-p (a middle upper)
  (forall (left right)
    (implies
     (and
      (<= 0 middle)
      (<= middle upper)
      (integerp left)
      (integerp right)
      (<= middle right)
      (< right upper)
      (<= 0 left)
      (< left middle))
     (<=
      (pspp1-t7 (pspp1-shift a left))
      (pspp1-t7 (pspp1-shift a right))))))

(defun-sk
    ntp4vc-partial-sort-post-partition-goal1-statement ()
  (forall
   (a i2 i1 i p)
   (implies
    (and
     (pspp1-address-p a)
     (integerp i2)
     (integerp i1)
     (integerp i)
     (booleanp p)
     (pspp1-function-types-p))
    (let*
        ((a1 (pspp1-shift a 0))
         (x (pspp1-t6 a1)))
      (implies
       (and
        (<= i1 i)
        (<= 0 i1)
        (<=
         (pspp1-region (pspp1-address-base a))
         0)
        (pspp1-linked-p)
        (pspp1-is-uint32-p i)
        (pspp1-is-uint32-p i1)
        (pspp1-is-uint32-p i2)
        (pspp1-is-sint32-p (pspp1-t5 a1))
        (pspp1-is-sint32-p x)
        (pspp1-valid-rw-p 0 a1 i)
        (if (< 0 i1)
            (and
             (equal p nil)
             (pspp1-allocation1-equals-allocation-p)
             (pspp1-havoc-t2-t8-equals-t5-p
              a i1)
             (pspp1-havoc-t3-t5-equals-t6-p
              a i)
             (pspp1-havoc-t4-a2-equals-t7-p
              a i1 i2)
             (<= i2 i)
             (<= i i2)
             (<= i1 i2)
             (pspp1-sorted-p a 0 i1)
             (pspp1-isheap-p 5 a i1)
             (pspp1-isheap-p 6 a i1)
             (pspp1-multiset-unchanged-p
              5 8 a 0 i1 i2)
             (pspp1-multiset-unchanged-p
              6 8 a 0 i2 i2)
             (pspp1-unchanged-p
              6 8 a i2 i i2)
             (pspp1-valid-rw-p 1 a1 i1)
             (pspp1-upperbound-p
              6 a 0 i1 x i2)
             (pspp1-lowerbound-p
              6 a i1 i2 x i2)
             (pspp1-multiset-unchanged-p
              7 2 a 0 i1 i2))
          (pspp1-t8-equals-t7-p)))
       (pspp1-partition-p a i1 i))))))

(value-triple :itpeval-statement-checked)

:q
