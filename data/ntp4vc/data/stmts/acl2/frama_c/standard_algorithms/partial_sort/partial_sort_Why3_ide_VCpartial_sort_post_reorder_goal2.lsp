;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_post_reorder_goal2:
;; the partial-sort postcondition that the reordered final memory preserves
;; the multiset of signed 32-bit values on the full range, under the stated
;; bounds, memory, heap, sortedness, unchanged-range, and value hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun psr2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun psr2-address-base (address)
  (car address))

(defun psr2-address-offset (address)
  (cdr address))

(defun psr2-shift (address amount)
  (cons
   (psr2-address-base address)
   (+ (psr2-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_6, t_3, t_5, t_2, t_8, t_4, and t_7; the allocation maps t and t_1;
;; the region function; and the linked predicate specialized to t.

(defstub psr2-t6 (address) t)
(defstub psr2-t3 (address) t)
(defstub psr2-t5 (address) t)
(defstub psr2-t2 (address) t)
(defstub psr2-t8 (address) t)
(defstub psr2-t4 (address) t)
(defstub psr2-t7 (address) t)
(defstub psr2-allocation (index) t)
(defstub psr2-allocation1 (index) t)
(defstub psr2-region (base) t)
(defstub psr2-linked-op () t)

(defun-sk psr2-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (psr2-address-p address)
      (and
       (integerp (psr2-t6 address))
       (integerp (psr2-t3 address))
       (integerp (psr2-t5 address))
       (integerp (psr2-t2 address))
       (integerp (psr2-t8 address))
       (integerp (psr2-t4 address))
       (integerp (psr2-t7 address))))
     (implies
      (integerp index)
      (and
       (integerp (psr2-allocation index))
       (integerp (psr2-allocation1 index))))
     (implies
      (integerp base)
      (integerp (psr2-region base))))))

(defun psr2-linked-p ()
  (if (psr2-linked-op) t nil))

(defun psr2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun psr2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun psr2-valid-rw-p (allocation-view address length)
  (implies
   (< 0 length)
   (and
    (< 0 (psr2-address-base address))
    (<= 0 (psr2-address-offset address))
    (<=
     (+ (psr2-address-offset address) length)
     (if (equal allocation-view 1)
         (psr2-allocation1
          (psr2-address-base address))
       (psr2-allocation
        (psr2-address-base address)))))))

(defun psr2-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (psr2-address-base left)
     (psr2-address-base right)))
   (<=
    (+ (psr2-address-offset right) right-length)
    (psr2-address-offset left))
   (<=
    (+ (psr2-address-offset left) left-length)
    (psr2-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_3 t_5 (shift a 0) i_3,
;; using the source havoc_access equation.

(defun psr2-a2-read (query a i3)
  (if
      (psr2-separated-p
       query 1 (psr2-shift a 0) i3)
      (psr2-t5 query)
    (psr2-t3 query)))

;; Source equalities between function values are represented extensionally on
;; their complete typed domains.

(defun-sk psr2-allocation1-equals-allocation-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal
      (psr2-allocation1 index)
      (psr2-allocation index)))))

(defun-sk psr2-havoc-t2-t8-equals-t5-p (a i2)
  (forall (query)
    (implies
     (psr2-address-p query)
     (equal
      (if
          (psr2-separated-p
           query 1 (psr2-shift a 0) i2)
          (psr2-t8 query)
        (psr2-t2 query))
      (psr2-t5 query)))))

(defun-sk psr2-havoc-t3-t5-equals-t6-p (a length)
  (forall (query)
    (implies
     (psr2-address-p query)
     (equal
      (if
          (psr2-separated-p
           query 1 (psr2-shift a 0) length)
          (psr2-t5 query)
        (psr2-t3 query))
      (psr2-t6 query)))))

(defun-sk psr2-havoc-t4-a2-equals-t7-p (a i2 i3)
  (forall (query)
    (implies
     (psr2-address-p query)
     (equal
      (if
          (psr2-separated-p
           query 1 (psr2-shift a 0) i2)
          (psr2-a2-read query a i3)
        (psr2-t4 query))
      (psr2-t7 query)))))

(defun-sk psr2-t8-equals-t7-p ()
  (forall (query)
    (implies
     (psr2-address-p query)
     (equal
      (psr2-t8 query)
      (psr2-t7 query)))))

;; Tags name exactly the memory functions needed by the quantified predicates:
;; 2=a_2, 5=t_5, 6=t_6, 7=t_7, and 8=t_8.

(defun psr2-memory-read (view query a i3)
  (cond
   ((equal view 2)
    (psr2-a2-read query a i3))
   ((equal view 5)
    (psr2-t5 query))
   ((equal view 6)
    (psr2-t6 query))
   ((equal view 7)
    (psr2-t7 query))
   (t
    (psr2-t8 query))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun psr2-count
    (view a i3 lower upper value)
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
              (psr2-memory-read
               view (psr2-shift a last) a i3)
              value)
             1
           0)
         (psr2-count
          view a i3 lower last value)))
    0))

;; Exact unfoldings of the source sortedness, heap, multiset, unchanged-range,
;; upper-bound, and lower-bound predicates. Every typed source quantifier
;; remains over all mathematical integers.

(defun-sk psr2-sorted-p (a lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (psr2-t7 (psr2-shift a left))
      (psr2-t7 (psr2-shift a right))))))

(defun-sk psr2-isheap-p (view a upper i3)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (psr2-memory-read
       view (psr2-shift a child) a i3)
      (psr2-memory-read
       view
       (psr2-shift
        a (floor (- child 1) 2))
       a i3)))))

(defun-sk psr2-multiset-unchanged-p
    (first-view second-view a lower upper i3)
  (forall (value)
    (implies
     (psr2-is-sint32-p value)
     (equal
      (psr2-count
       second-view a i3 lower upper value)
      (psr2-count
       first-view a i3 lower upper value)))))

(defun-sk psr2-unchanged-p
    (first-view second-view a lower upper i3)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (psr2-memory-read
       second-view (psr2-shift a index) a i3)
      (psr2-memory-read
       first-view (psr2-shift a index) a i3)))))

(defun-sk psr2-upperbound-p
    (view a lower upper value i3)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (psr2-memory-read
       view (psr2-shift a index) a i3)
      value))))

(defun-sk psr2-lowerbound-p
    (view a lower upper value i3)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (psr2-memory-read
       view (psr2-shift a index) a i3)))))

(defun-sk
    ntp4vc-partial-sort-post-reorder-goal2-statement ()
  (forall
   (a i3 i1 i i2 p)
   (implies
    (and
     (psr2-address-p a)
     (integerp i3)
     (integerp i1)
     (integerp i)
     (integerp i2)
     (booleanp p)
     (psr2-function-types-p))
    (let*
        ((a1 (psr2-shift a 0))
         (x (psr2-t6 a1)))
      (implies
       (and
        (<= i1 i)
        (<= 0 i1)
        (<=
         (psr2-region (psr2-address-base a))
         0)
        (psr2-linked-p)
        (psr2-is-uint32-p i)
        (psr2-is-uint32-p i1)
        (psr2-is-uint32-p i2)
        (psr2-is-uint32-p i3)
        (psr2-is-sint32-p (psr2-t5 a1))
        (psr2-is-sint32-p x)
        (psr2-valid-rw-p 0 a1 i)
        (if (< 0 i1)
            (and
             (equal p nil)
             (equal i2 i1)
             (psr2-allocation1-equals-allocation-p)
             (psr2-havoc-t2-t8-equals-t5-p
              a i2)
             (psr2-havoc-t3-t5-equals-t6-p
              a i)
             (psr2-havoc-t4-a2-equals-t7-p
              a i2 i3)
             (<= i3 i)
             (<= i i3)
             (<= i2 i3)
             (psr2-sorted-p a 0 i2)
             (psr2-isheap-p 5 a i2 i3)
             (psr2-isheap-p 6 a i2 i3)
             (psr2-multiset-unchanged-p
              5 8 a 0 i2 i3)
             (psr2-multiset-unchanged-p
              6 8 a 0 i3 i3)
             (psr2-unchanged-p
              6 8 a i3 i i3)
             (psr2-valid-rw-p 1 a1 i2)
             (psr2-upperbound-p
              6 a 0 i2 x i3)
             (psr2-lowerbound-p
              6 a i2 i3 x i3)
             (psr2-multiset-unchanged-p
              7 2 a 0 i2 i3))
          (psr2-t8-equals-t7-p)))
       (psr2-multiset-unchanged-p
        7 8 a 0 i i3))))))

(value-triple :itpeval-statement-checked)

:q
