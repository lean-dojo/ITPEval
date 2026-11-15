;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_reorder_goal3:
;; the pop-heap postcondition that the final memory preserves the multiset of
;; signed 32-bit values on the heap range, under the stated heap, update,
;; memory-validity, integer-range, linkedness, and branch hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phg3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phg3-address-base (address)
  (car address))

(defun phg3-address-offset (address)
  (cdr address))

(defun phg3-shift (address amount)
  (cons
   (phg3-address-base address)
   (+ (phg3-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories.
;; Memory views 2, 3, 4, and 5 denote t_2, t_3, t_4, and t_5. Allocation
;; views 0 and 1 denote t and t_1.

(defstub phg3-memory (view address) t)
(defstub phg3-allocation (view index) t)
(defstub phg3-region (base) t)
(defstub phg3-linked-op () t)

(defun-sk phg3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phg3-address-p address)
      (and
       (integerp (phg3-memory 2 address))
       (integerp (phg3-memory 3 address))
       (integerp (phg3-memory 4 address))
       (integerp (phg3-memory 5 address))))
     (implies
      (integerp index)
      (and
       (integerp (phg3-allocation 0 index))
       (integerp (phg3-allocation 1 index))))
     (implies
      (integerp base)
      (integerp (phg3-region base))))))

(defun phg3-linked-p ()
  (if (phg3-linked-op) t nil))

(defun phg3-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phg3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phg3-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3 integer division truncates toward zero.

(defun phg3-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phg3-heap-parent (index)
  (phg3-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rd and Memory.valid_rw.

(defun phg3-valid-rd-p (allocation-view address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg3-address-base address)))
    (<= 0 (phg3-address-offset address))
    (<=
     (+ (phg3-address-offset address) length)
     (phg3-allocation
      allocation-view
      (phg3-address-base address))))))

(defun phg3-valid-rw-p (allocation-view address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg3-address-base address))
    (<= 0 (phg3-address-offset address))
    (<=
     (+ (phg3-address-offset address) length)
     (phg3-allocation
      allocation-view
      (phg3-address-base address))))))

;; Exact unfolding of Memory.separated.

(defun phg3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (phg3-address-base left)
     (phg3-address-base right)))
   (<=
    (+ (phg3-address-offset right) right-length)
    (phg3-address-offset left))
   (<=
    (+ (phg3-address-offset left) left-length)
    (phg3-address-offset right))))

;; Exact pointwise value of havoc t_2 t_4 (shift a 0) length, using the
;; source havoc_access equation.

(defun phg3-havoc-read (a length query)
  (if
      (phg3-separated-p
       query 1 (phg3-shift a 0) length)
      (phg3-memory 4 query)
    (phg3-memory 2 query)))

;; Source equalities between functions are represented extensionally over
;; every element of their complete typed domains.

(defun-sk phg3-t1-equals-t-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal
      (phg3-allocation 1 index)
      (phg3-allocation 0 index)))))

(defun-sk phg3-havoc-equals-t3-p (a length)
  (forall (query)
    (implies
     (phg3-address-p query)
     (equal
      (phg3-havoc-read a length query)
      (phg3-memory 3 query)))))

(defun phg3-updated-t3-read
    (a2 a4 x x2 query)
  (if (equal query a2)
      x
    (if (equal query a4)
        x2
      (phg3-memory 3 query))))

(defun-sk phg3-updated-t3-equals-t5-p
    (a2 a4 x x2)
  (forall (query)
    (implies
     (phg3-address-p query)
     (equal
      (phg3-updated-t3-read
       a2 a4 x x2 query)
      (phg3-memory 5 query)))))

(defun-sk phg3-t5-equals-t4-p ()
  (forall (query)
    (implies
     (phg3-address-p query)
     (equal
      (phg3-memory 5 query)
      (phg3-memory 4 query)))))

;; Exact unfolding of Axiomatic.p_isheap.

(defun-sk phg3-isheap-p (memory-view a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phg3-memory
       memory-view (phg3-shift a child))
      (phg3-memory
       memory-view
       (phg3-shift
        a (phg3-heap-parent child)))))))

;; Exact unfolding of Axiomatic1.p_heapmaximumchild.

(defun phg3-heap-maximum-child-p
    (memory-view a upper parent child)
  (let*
      ((left (+ 1 (* 2 parent)))
       (child-value
        (phg3-memory
         memory-view (phg3-shift a child)))
       (right (+ 2 (* 2 parent))))
    (and
     (<= 0 parent)
     (<= (+ 2 parent) upper)
     (implies
      (<= parent 2147483646)
      (equal (phg3-heap-parent child) parent))
     (implies
      (<= (+ 2 left) upper)
      (<=
       (phg3-memory
        memory-view (phg3-shift a left))
       child-value))
     (implies
      (<= (+ 2 right) upper)
      (<=
       (phg3-memory
        memory-view (phg3-shift a right))
       child-value)))))

;; Exact unfolding of Axiomatic.p_upperbound_1'.

(defun-sk phg3-upperbound-p
    (memory-view a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (phg3-memory
       memory-view (phg3-shift a index))
      value))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun phg3-count
    (memory-view a lower upper value)
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
              (phg3-memory
               memory-view
               (phg3-shift a last))
              value)
             1
           0)
         (phg3-count
          memory-view a lower last value)))
    0))

;; Exact unfolding of Axiomatic1.p_multisetunchanged_1' for t_5 and t_4.

(defun-sk phg3-multiset-unchanged-t5-t4-p
    (a lower upper)
  (forall (value)
    (implies
     (phg3-is-sint32-p value)
     (equal
      (phg3-count 4 a lower upper value)
      (phg3-count 5 a lower upper value)))))

(defun-sk phg3-branch-count-balance-p
    (a upper a4 x)
  (forall (value)
    (implies
     (phg3-is-sint32-p value)
     (equal
      (+
       (phg3-count 4 a 0 upper value)
       (if
           (equal (phg3-memory 3 a4) value)
           1
         0))
      (+
       (phg3-count 3 a 0 upper value)
       (if (equal x value) 1 0))))))

(defun-sk ntp4vc-pop-heap-post-reorder-goal3-statement ()
  (forall
   (a i i1 i3 i2 p p1)
   (implies
    (and
     (phg3-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (integerp i2)
     (booleanp p)
     (booleanp p1)
     (phg3-function-types-p))
    (let*
        ((a1 (phg3-shift a 0))
         (x (phg3-memory 4 a1))
         (x1 (- i 1))
         (a2 (phg3-shift a x1))
         (a3
          (phg3-shift
           a (phg3-to-uint32 x1)))
         (a4 (phg3-shift a i1))
         (x2 (phg3-memory 3 a2))
         (a5 (phg3-shift a i3)))
      (implies
       (and
        (< 0 i)
        (<=
         (phg3-region
          (phg3-address-base a))
         0)
        (phg3-linked-p)
        (phg3-is-uint32-p i)
        (phg3-is-uint32-p i1)
        (phg3-is-uint32-p i2)
        (phg3-is-uint32-p i3)
        (phg3-isheap-p 4 a i)
        (phg3-is-sint32-p x)
        (phg3-valid-rw-p 0 a1 i)
        (phg3-is-sint32-p
         (phg3-memory 5 a2))
        (if (<= 2 i)
            (and
             (phg3-valid-rd-p 0 a1 1)
             (phg3-valid-rd-p 0 a3 1)
             (if (< (phg3-memory 4 a2) x)
                 (and
                  (equal p nil)
                  (equal p1 nil)
                  (phg3-t1-equals-t-p)
                  (phg3-havoc-equals-t3-p
                   a x1)
                  (phg3-updated-t3-equals-t5-p
                   a2 a4 x x2)
                  (< 0 i2)
                  (<= 0 i1)
                  (< i1 i3)
                  (<
                   x2
                   (phg3-memory
                    3
                    (phg3-shift
                     a
                     (phg3-heap-parent i1))))
                  (<= (+ 2 i1) i)
                  (phg3-isheap-p 3 a i)
                  (phg3-heap-maximum-child-p
                   3 a i i1 i3)
                  (phg3-heap-maximum-child-p
                   4 a i 0 i2)
                  (phg3-valid-rw-p 1 a1 i)
                  (phg3-valid-rw-p 1 a4 1)
                  (phg3-upperbound-p
                   3 a 0 i x)
                  (phg3-valid-rd-p 1 a3 1)
                  (phg3-valid-rw-p 1 a3 1)
                  (implies
                   (<= (+ 2 i2) i)
                   (equal
                    (phg3-heap-parent i2)
                    0))
                  (implies
                   (<= (+ 2 i3) i)
                   (equal
                    (phg3-heap-parent i3)
                    i1))
                  (or
                   (<= i (+ 1 i3))
                   (and
                    (<=
                     (phg3-memory 3 a5)
                     x2)
                    (phg3-valid-rd-p
                     1 a5 1)))
                  (phg3-branch-count-balance-p
                   a i a4 x))
               (phg3-t5-equals-t4-p)))
          (phg3-t5-equals-t4-p)))
       (phg3-multiset-unchanged-t5-t4-p
        a 0 i))))))

(value-triple :itpeval-statement-checked)

:q
