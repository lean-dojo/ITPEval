;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_result_goal1:
;; the pop-heap postcondition that the final entry equals the original heap
;; root value, under the stated heap, update, memory-validity, integer-range,
;; linkedness, and branch hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phr1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phr1-address-base (address)
  (car address))

(defun phr1-address-offset (address)
  (cdr address))

(defun phr1-shift (address amount)
  (cons
   (phr1-address-base address)
   (+ (phr1-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_5, t_4, t_3, and t_2; allocation maps t and t_1; the region function;
;; and the linked predicate specialized to t.

(defstub phr1-t5 (address) t)
(defstub phr1-t4 (address) t)
(defstub phr1-t3 (address) t)
(defstub phr1-t2 (address) t)
(defstub phr1-allocation-t (index) t)
(defstub phr1-allocation-t1 (index) t)
(defstub phr1-region (base) t)
(defstub phr1-linked-op () t)

(defun-sk phr1-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phr1-address-p address)
      (and
       (integerp (phr1-t5 address))
       (integerp (phr1-t4 address))
       (integerp (phr1-t3 address))
       (integerp (phr1-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (phr1-allocation-t index))
       (integerp (phr1-allocation-t1 index))))
     (implies
      (integerp base)
      (integerp (phr1-region base))))))

(defun phr1-linked-p ()
  (if (phr1-linked-op) t nil))

(defun phr1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phr1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phr1-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3 integer division truncates toward zero.

(defun phr1-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phr1-heap-parent (index)
  (phr1-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rd and Memory.valid_rw for allocation
;; maps t and t_1.

(defun phr1-valid-rd-t-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phr1-address-base address)))
    (<= 0 (phr1-address-offset address))
    (<=
     (+ (phr1-address-offset address) length)
     (phr1-allocation-t
      (phr1-address-base address))))))

(defun phr1-valid-rw-t-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phr1-address-base address))
    (<= 0 (phr1-address-offset address))
    (<=
     (+ (phr1-address-offset address) length)
     (phr1-allocation-t
      (phr1-address-base address))))))

(defun phr1-valid-rd-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phr1-address-base address)))
    (<= 0 (phr1-address-offset address))
    (<=
     (+ (phr1-address-offset address) length)
     (phr1-allocation-t1
      (phr1-address-base address))))))

(defun phr1-valid-rw-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phr1-address-base address))
    (<= 0 (phr1-address-offset address))
    (<=
     (+ (phr1-address-offset address) length)
     (phr1-allocation-t1
      (phr1-address-base address))))))

;; Exact unfolding of Memory.separated.

(defun phr1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (phr1-address-base left)
     (phr1-address-base right)))
   (<=
    (+ (phr1-address-offset right) right-length)
    (phr1-address-offset left))
   (<=
    (+ (phr1-address-offset left) left-length)
    (phr1-address-offset right))))

;; Exact pointwise value of havoc t_2 t_5 (shift a 0) length, using the
;; source havoc_access equation.

(defun phr1-havoc-read (a length query)
  (if
      (phr1-separated-p
       query 1 (phr1-shift a 0) length)
      (phr1-t5 query)
    (phr1-t2 query)))

;; Source equalities between functions are represented extensionally over
;; every element of their complete typed domains.

(defun-sk phr1-t1-equals-t-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal
      (phr1-allocation-t1 index)
      (phr1-allocation-t index)))))

(defun-sk phr1-havoc-equals-t3-p (a length)
  (forall (query)
    (implies
     (phr1-address-p query)
     (equal
      (phr1-havoc-read a length query)
      (phr1-t3 query)))))

(defun phr1-updated-t3-read
    (a2 a4 x x3 query)
  (if (equal query a2)
      x
    (if (equal query a4)
        x3
      (phr1-t3 query))))

(defun-sk phr1-updated-t3-equals-t4-p
    (a2 a4 x x3)
  (forall (query)
    (implies
     (phr1-address-p query)
     (equal
      (phr1-updated-t3-read
       a2 a4 x x3 query)
      (phr1-t4 query)))))

(defun-sk phr1-t5-equals-t4-p ()
  (forall (query)
    (implies
     (phr1-address-p query)
     (equal
      (phr1-t5 query)
      (phr1-t4 query)))))

;; Exact unfoldings of Axiomatic.p_isheap for t_5 and t_3.

(defun-sk phr1-isheap-t5-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phr1-t5 (phr1-shift a child))
      (phr1-t5
       (phr1-shift
        a (phr1-heap-parent child)))))))

(defun-sk phr1-isheap-t3-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phr1-t3 (phr1-shift a child))
      (phr1-t3
       (phr1-shift
        a (phr1-heap-parent child)))))))

;; Exact unfoldings of Axiomatic1.p_heapmaximumchild.

(defun phr1-heap-maximum-child-t3-p
    (a upper parent child)
  (let*
      ((left (+ 1 (* 2 parent)))
       (child-value
        (phr1-t3 (phr1-shift a child)))
       (right (+ 2 (* 2 parent))))
    (and
     (<= 0 parent)
     (<= (+ 2 parent) upper)
     (implies
      (<= parent 2147483646)
      (equal (phr1-heap-parent child) parent))
     (implies
      (<= (+ 2 left) upper)
      (<=
       (phr1-t3 (phr1-shift a left))
       child-value))
     (implies
      (<= (+ 2 right) upper)
      (<=
       (phr1-t3 (phr1-shift a right))
       child-value)))))

(defun phr1-heap-maximum-child-t5-p
    (a upper parent child)
  (let*
      ((left (+ 1 (* 2 parent)))
       (child-value
        (phr1-t5 (phr1-shift a child)))
       (right (+ 2 (* 2 parent))))
    (and
     (<= 0 parent)
     (<= (+ 2 parent) upper)
     (implies
      (<= parent 2147483646)
      (equal (phr1-heap-parent child) parent))
     (implies
      (<= (+ 2 left) upper)
      (<=
       (phr1-t5 (phr1-shift a left))
       child-value))
     (implies
      (<= (+ 2 right) upper)
      (<=
       (phr1-t5 (phr1-shift a right))
       child-value)))))

;; Exact unfolding of Axiomatic.p_upperbound_1' for t_3.

(defun-sk phr1-upperbound-t3-p
    (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (phr1-t3 (phr1-shift a index))
      value))))

;; A_Count.l_count_2' is uniquely characterized on signed-32 values by its
;; source empty, hit, and miss equations. The selector is used only for the
;; source memories t_5 (view 5) and t_3 (view 3).

(defun phr1-count-memory (view address)
  (if (equal view 5)
      (phr1-t5 address)
    (phr1-t3 address)))

(defun phr1-count
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
              (phr1-count-memory
               memory-view
               (phr1-shift a last))
              value)
             1
           0)
         (phr1-count
          memory-view a lower last value)))
    0))

(defun-sk phr1-branch-count-balance-p
    (a upper a4 x)
  (forall (value)
    (implies
     (phr1-is-sint32-p value)
     (equal
      (+
       (phr1-count 5 a 0 upper value)
       (if (equal (phr1-t3 a4) value) 1 0))
      (+
       (phr1-count 3 a 0 upper value)
       (if (equal x value) 1 0))))))

(defun-sk ntp4vc-pop-heap-post-result-goal1-statement ()
  (forall
   (a i i1 i3 i2 p p1)
   (implies
    (and
     (phr1-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (integerp i2)
     (booleanp p)
     (booleanp p1)
     (phr1-function-types-p))
    (let*
        ((a1 (phr1-shift a 0))
         (x (phr1-t5 a1))
         (x1 (- i 1))
         (a2 (phr1-shift a x1))
         (x2 (phr1-t4 a2))
         (a3
          (phr1-shift
           a (phr1-to-uint32 x1)))
         (a4 (phr1-shift a i1))
         (x3 (phr1-t3 a2))
         (a5 (phr1-shift a i3)))
      (implies
       (and
        (< 0 i)
        (<=
         (phr1-region
          (phr1-address-base a))
         0)
        (phr1-linked-p)
        (phr1-is-uint32-p i)
        (phr1-is-uint32-p i1)
        (phr1-is-uint32-p i2)
        (phr1-is-uint32-p i3)
        (phr1-isheap-t5-p a i)
        (phr1-is-sint32-p x)
        (phr1-valid-rw-t-p a1 i)
        (phr1-is-sint32-p x2)
        (if (<= 2 i)
            (and
             (phr1-valid-rd-t-p a1 1)
             (phr1-valid-rd-t-p a3 1)
             (if (< (phr1-t5 a2) x)
                 (and
                  (equal p nil)
                  (equal p1 nil)
                  (phr1-t1-equals-t-p)
                  (phr1-havoc-equals-t3-p
                   a x1)
                  (phr1-updated-t3-equals-t4-p
                   a2 a4 x x3)
                  (< 0 i2)
                  (<= 0 i1)
                  (< i1 i3)
                  (<
                   x3
                   (phr1-t3
                    (phr1-shift
                     a
                     (phr1-heap-parent i1))))
                  (<= (+ 2 i1) i)
                  (phr1-isheap-t3-p a i)
                  (phr1-heap-maximum-child-t3-p
                   a i i1 i3)
                  (phr1-heap-maximum-child-t5-p
                   a i 0 i2)
                  (phr1-valid-rw-t1-p a1 i)
                  (phr1-valid-rw-t1-p a4 1)
                  (phr1-upperbound-t3-p
                   a 0 i x)
                  (phr1-valid-rd-t1-p a3 1)
                  (phr1-valid-rw-t1-p a3 1)
                  (implies
                   (<= (+ 2 i2) i)
                   (equal
                    (phr1-heap-parent i2)
                    0))
                  (implies
                   (<= (+ 2 i3) i)
                   (equal
                    (phr1-heap-parent i3)
                    i1))
                  (or
                   (<= i (+ 1 i3))
                   (and
                    (<= (phr1-t3 a5) x3)
                    (phr1-valid-rd-t1-p
                     a5 1)))
                  (phr1-branch-count-balance-p
                   a i a4 x))
               (phr1-t5-equals-t4-p)))
          (phr1-t5-equals-t4-p)))
       (equal x2 x))))))

(value-triple :itpeval-statement-checked)

:q
