;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_loop_inv_max_established_goal9:
;; establishment of the pop-heap loop's root upper-bound invariant under the
;; stated index, heap, maximum-child, memory-validity, signed-value, linkedness,
;; conversion, and region hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phg9-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phg9-address-base (address)
  (car address))

(defun phg9-address-offset (address)
  (cdr address))

(defun phg9-shift (address amount)
  (cons
   (phg9-address-base address)
   (+ (phg9-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source integer
;; memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub phg9-memory (address) t)
(defstub phg9-allocation (index) t)
(defstub phg9-region (base) t)
(defstub phg9-linked-op () t)

(defun-sk phg9-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phg9-address-p address)
      (integerp (phg9-memory address)))
     (implies
      (integerp index)
      (integerp (phg9-allocation index)))
     (implies
      (integerp base)
      (integerp (phg9-region base))))))

(defun phg9-linked-p ()
  (if (phg9-linked-op) t nil))

(defun phg9-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phg9-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phg9-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3's integer division truncates toward zero. This exact definition is
;; needed at index zero as well as at the positive heap-child indices.

(defun phg9-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phg9-heap-parent (index)
  (phg9-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rd and Memory.valid_rw for the arbitrary
;; allocation map t.

(defun phg9-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg9-address-base address)))
    (<= 0 (phg9-address-offset address))
    (<=
     (+ (phg9-address-offset address) length)
     (phg9-allocation (phg9-address-base address))))))

(defun phg9-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg9-address-base address))
    (<= 0 (phg9-address-offset address))
    (<=
     (+ (phg9-address-offset address) length)
     (phg9-allocation (phg9-address-base address))))))

;; Exact unfolding of Axiomatic.p_isheap over every mathematical integer
;; child index.

(defun-sk phg9-isheap-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phg9-memory (phg9-shift a child))
      (phg9-memory
       (phg9-shift a (phg9-heap-parent child)))))))

;; Exact unfolding of Axiomatic1.p_heapmaximumchild.

(defun phg9-heap-maximum-child-p
    (a upper parent child)
  (let*
      ((left (+ 1 (* 2 parent)))
       (child-value
        (phg9-memory (phg9-shift a child)))
       (right (+ 2 (* 2 parent))))
    (and
     (<= 0 parent)
     (<= (+ 2 parent) upper)
     (implies
      (<= parent 2147483646)
      (equal (phg9-heap-parent child) parent))
     (implies
      (<= (+ 2 left) upper)
      (<=
       (phg9-memory (phg9-shift a left))
       child-value))
     (implies
      (<= (+ 2 right) upper)
      (<=
       (phg9-memory (phg9-shift a right))
       child-value)))))

;; Exact unfolding of Axiomatic.p_upperbound_1' over every mathematical
;; integer index in [lower, upper).

(defun-sk phg9-upperbound-p
    (a lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (phg9-memory (phg9-shift a index))
      value))))

(defun-sk
    ntp4vc-pop-heap-loop-inv-max-established-goal9-statement ()
  (forall
   (i a i1)
   (implies
    (and
     (integerp i)
     (phg9-address-p a)
     (integerp i1)
     (phg9-function-types-p))
    (let*
        ((x (- i 1))
         (x1 (phg9-memory (phg9-shift a x)))
         (a1 (phg9-shift a 0))
         (x2 (phg9-memory a1)))
      (implies
       (and
        (< 0 i)
        (< 0 i1)
        (<= (phg9-region (phg9-address-base a)) 0)
        (< x1 x2)
        (<= 2 i)
        (phg9-linked-p)
        (phg9-is-uint32-p i)
        (phg9-is-uint32-p i1)
        (phg9-isheap-p a i)
        (phg9-is-sint32-p x2)
        (phg9-heap-maximum-child-p a i 0 i1)
        (phg9-valid-rd-p a1 1)
        (phg9-valid-rw-p a1 i)
        (phg9-is-sint32-p
         (phg9-memory
          (phg9-shift a (phg9-heap-parent 0))))
        (phg9-is-sint32-p x1)
        (phg9-valid-rd-p
         (phg9-shift a (phg9-to-uint32 x))
         1)
        (implies
         (<= (+ 2 i1) i)
         (equal (phg9-heap-parent i1) 0)))
       (phg9-upperbound-p a 0 i x2))))))

(value-triple :itpeval-statement-checked)

:q
