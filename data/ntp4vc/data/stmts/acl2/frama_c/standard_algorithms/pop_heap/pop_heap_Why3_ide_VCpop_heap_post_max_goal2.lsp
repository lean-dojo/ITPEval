;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_max_goal2:
;; the pop-heap postcondition that the original final entry is a maximum of
;; the resulting prefix, under the stated heap, update, memory-validity,
;; integer-range, linkedness, and branch hypotheses. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phg2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phg2-address-base (address)
  (car address))

(defun phg2-address-offset (address)
  (cdr address))

(defun phg2-shift (address amount)
  (cons
   (phg2-address-base address)
   (+ (phg2-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_4, t_3, t_5, and t_2; allocation maps t and t_1; the region function;
;; and the linked predicate specialized to t.

(defstub phg2-t4 (address) t)
(defstub phg2-t3 (address) t)
(defstub phg2-t5 (address) t)
(defstub phg2-t2 (address) t)
(defstub phg2-allocation-t (index) t)
(defstub phg2-allocation-t1 (index) t)
(defstub phg2-region (base) t)
(defstub phg2-linked-op () t)

(defun-sk phg2-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phg2-address-p address)
      (and
       (integerp (phg2-t4 address))
       (integerp (phg2-t3 address))
       (integerp (phg2-t5 address))
       (integerp (phg2-t2 address))))
     (implies
      (integerp index)
      (and
       (integerp (phg2-allocation-t index))
       (integerp (phg2-allocation-t1 index))))
     (implies
      (integerp base)
      (integerp (phg2-region base))))))

(defun phg2-linked-p ()
  (if (phg2-linked-op) t nil))

(defun phg2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phg2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phg2-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3 integer division truncates toward zero.

(defun phg2-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phg2-heap-parent (index)
  (phg2-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rd and Memory.valid_rw for allocation
;; maps t and t_1.

(defun phg2-valid-rd-t-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg2-address-base address)))
    (<= 0 (phg2-address-offset address))
    (<=
     (+ (phg2-address-offset address) length)
     (phg2-allocation-t
      (phg2-address-base address))))))

(defun phg2-valid-rw-t-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg2-address-base address))
    (<= 0 (phg2-address-offset address))
    (<=
     (+ (phg2-address-offset address) length)
     (phg2-allocation-t
      (phg2-address-base address))))))

(defun phg2-valid-rd-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg2-address-base address)))
    (<= 0 (phg2-address-offset address))
    (<=
     (+ (phg2-address-offset address) length)
     (phg2-allocation-t1
      (phg2-address-base address))))))

(defun phg2-valid-rw-t1-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg2-address-base address))
    (<= 0 (phg2-address-offset address))
    (<=
     (+ (phg2-address-offset address) length)
     (phg2-allocation-t1
      (phg2-address-base address))))))

;; Exact unfolding of Memory.separated.

(defun phg2-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (phg2-address-base left)
     (phg2-address-base right)))
   (<=
    (+ (phg2-address-offset right) right-length)
    (phg2-address-offset left))
   (<=
    (+ (phg2-address-offset left) left-length)
    (phg2-address-offset right))))

;; Exact pointwise value of havoc t_2 t_4 (shift a 0) length, using the
;; source havoc_access equation.

(defun phg2-havoc-read (a length query)
  (if
      (phg2-separated-p
       query 1 (phg2-shift a 0) length)
      (phg2-t4 query)
    (phg2-t2 query)))

;; Source equalities between functions are represented extensionally over
;; every element of their typed domains.

(defun-sk phg2-t1-equals-t-p ()
  (forall (index)
    (implies
     (integerp index)
     (equal
      (phg2-allocation-t1 index)
      (phg2-allocation-t index)))))

(defun-sk phg2-havoc-equals-t3-p (a length)
  (forall (query)
    (implies
     (phg2-address-p query)
     (equal
      (phg2-havoc-read a length query)
      (phg2-t3 query)))))

(defun phg2-updated-t3-read
    (a2 a4 x x2 query)
  (if (equal query a2)
      x
    (if (equal query a4)
        x2
      (phg2-t3 query))))

(defun-sk phg2-updated-t3-equals-t5-p
    (a2 a4 x x2)
  (forall (query)
    (implies
     (phg2-address-p query)
     (equal
      (phg2-updated-t3-read
       a2 a4 x x2 query)
      (phg2-t5 query)))))

(defun-sk phg2-t5-equals-t4-p ()
  (forall (query)
    (implies
     (phg2-address-p query)
     (equal
      (phg2-t5 query)
      (phg2-t4 query)))))

;; Exact unfoldings of Axiomatic.p_isheap for t_4 and t_3.

(defun-sk phg2-isheap-t4-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phg2-t4 (phg2-shift a child))
      (phg2-t4
       (phg2-shift
        a (phg2-heap-parent child)))))))

(defun-sk phg2-isheap-t3-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phg2-t3 (phg2-shift a child))
      (phg2-t3
       (phg2-shift
        a (phg2-heap-parent child)))))))

;; Exact unfoldings of Axiomatic1.p_heapmaximumchild.

(defun phg2-heap-maximum-child-t3-p
    (a upper parent child)
  (let*
      ((left (+ 1 (* 2 parent)))
       (child-value
        (phg2-t3 (phg2-shift a child)))
       (right (+ 2 (* 2 parent))))
    (and
     (<= 0 parent)
     (<= (+ 2 parent) upper)
     (implies
      (<= parent 2147483646)
      (equal (phg2-heap-parent child) parent))
     (implies
      (<= (+ 2 left) upper)
      (<=
       (phg2-t3 (phg2-shift a left))
       child-value))
     (implies
      (<= (+ 2 right) upper)
      (<=
       (phg2-t3 (phg2-shift a right))
       child-value)))))

(defun phg2-heap-maximum-child-t4-p
    (a upper parent child)
  (let*
      ((left (+ 1 (* 2 parent)))
       (child-value
        (phg2-t4 (phg2-shift a child)))
       (right (+ 2 (* 2 parent))))
    (and
     (<= 0 parent)
     (<= (+ 2 parent) upper)
     (implies
      (<= parent 2147483646)
      (equal (phg2-heap-parent child) parent))
     (implies
      (<= (+ 2 left) upper)
      (<=
       (phg2-t4 (phg2-shift a left))
       child-value))
     (implies
      (<= (+ 2 right) upper)
      (<=
       (phg2-t4 (phg2-shift a right))
       child-value)))))

;; Exact unfoldings of Axiomatic.p_upperbound_1' for t_3 and t_5.

(defun-sk phg2-upperbound-t3-p
    (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (phg2-t3 (phg2-shift a index))
      value))))

(defun-sk phg2-upperbound-t5-p
    (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (phg2-t5 (phg2-shift a index))
      value))))

;; Exact unfolding of Axiomatic.p_maxelement.

(defun phg2-maxelement-t5-p
    (a upper max-index)
  (and
   (<= 0 max-index)
   (< max-index upper)
   (phg2-upperbound-t5-p
    a 0 upper
    (phg2-t5
     (phg2-shift a max-index)))))

;; A_Count.l_count_2' is uniquely characterized on signed-32 values by its
;; source empty, hit, and miss equations. The selector is used only for the
;; source memories t_4 (view 4) and t_3 (view 3).

(defun phg2-count-memory (view address)
  (if (equal view 4)
      (phg2-t4 address)
    (phg2-t3 address)))

(defun phg2-count
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
              (phg2-count-memory
               memory-view
               (phg2-shift a last))
              value)
             1
           0)
         (phg2-count
          memory-view a lower last value)))
    0))

(defun-sk phg2-branch-count-balance-p
    (a upper a4 x)
  (forall (value)
    (implies
     (phg2-is-sint32-p value)
     (equal
      (+
       (phg2-count 4 a 0 upper value)
       (if (equal (phg2-t3 a4) value) 1 0))
      (+
       (phg2-count 3 a 0 upper value)
       (if (equal x value) 1 0))))))

(defun-sk ntp4vc-pop-heap-post-max-goal2-statement ()
  (forall
   (a i i1 i3 i2 p p1)
   (implies
    (and
     (phg2-address-p a)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (integerp i2)
     (booleanp p)
     (booleanp p1)
     (phg2-function-types-p))
    (let*
        ((a1 (phg2-shift a 0))
         (x (phg2-t4 a1))
         (x1 (- i 1))
         (a2 (phg2-shift a x1))
         (a3
          (phg2-shift
           a (phg2-to-uint32 x1)))
         (a4 (phg2-shift a i1))
         (x2 (phg2-t3 a2))
         (a5 (phg2-shift a i3)))
      (implies
       (and
        (< 0 i)
        (<=
         (phg2-region
          (phg2-address-base a))
         0)
        (phg2-linked-p)
        (phg2-is-uint32-p i)
        (phg2-is-uint32-p i1)
        (phg2-is-uint32-p i2)
        (phg2-is-uint32-p i3)
        (phg2-isheap-t4-p a i)
        (phg2-is-sint32-p x)
        (phg2-valid-rw-t-p a1 i)
        (phg2-is-sint32-p (phg2-t5 a2))
        (if (<= 2 i)
            (and
             (phg2-valid-rd-t-p a1 1)
             (phg2-valid-rd-t-p a3 1)
             (if (< (phg2-t4 a2) x)
                 (and
                  (equal p nil)
                  (equal p1 nil)
                  (phg2-t1-equals-t-p)
                  (phg2-havoc-equals-t3-p
                   a x1)
                  (phg2-updated-t3-equals-t5-p
                   a2 a4 x x2)
                  (< 0 i2)
                  (<= 0 i1)
                  (< i1 i3)
                  (<
                   x2
                   (phg2-t3
                    (phg2-shift
                     a
                     (phg2-heap-parent i1))))
                  (<= (+ 2 i1) i)
                  (phg2-isheap-t3-p a i)
                  (phg2-heap-maximum-child-t3-p
                   a i i1 i3)
                  (phg2-heap-maximum-child-t4-p
                   a i 0 i2)
                  (phg2-valid-rw-t1-p a1 i)
                  (phg2-valid-rw-t1-p a4 1)
                  (phg2-upperbound-t3-p
                   a 0 i x)
                  (phg2-valid-rd-t1-p a3 1)
                  (phg2-valid-rw-t1-p a3 1)
                  (implies
                   (<= (+ 2 i2) i)
                   (equal
                    (phg2-heap-parent i2)
                    0))
                  (implies
                   (<= (+ 2 i3) i)
                   (equal
                    (phg2-heap-parent i3)
                    i1))
                  (or
                   (<= i (+ 1 i3))
                   (and
                    (<= (phg2-t3 a5) x2)
                    (phg2-valid-rd-t1-p
                     a5 1)))
                  (phg2-branch-count-balance-p
                   a i a4 x))
               (phg2-t5-equals-t4-p)))
          (phg2-t5-equals-t4-p)))
       (phg2-maxelement-t5-p
        a i x1))))))

(value-triple :itpeval-statement-checked)

:q
