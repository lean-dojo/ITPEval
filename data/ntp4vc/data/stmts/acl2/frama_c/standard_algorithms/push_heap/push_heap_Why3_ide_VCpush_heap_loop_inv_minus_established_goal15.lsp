;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_minus_established_goal15:
;; establishment of the push-heap loop's multiset-minus invariant after
;; replacing the final element by its heap parent's value, under the stated
;; heap, integer-range, memory-validity, linkedness, and ordering hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phg15-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phg15-address-base (address)
  (car address))

(defun phg15-address-offset (address)
  (cdr address))

(defun phg15-shift (address amount)
  (cons
   (phg15-address-base address)
   (+ (phg15-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source integer
;; memory t_1, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub phg15-memory (address) t)
(defstub phg15-allocation (index) t)
(defstub phg15-region (base) t)
(defstub phg15-linked-op () t)

(defun-sk phg15-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phg15-address-p address)
      (integerp (phg15-memory address)))
     (implies
      (integerp index)
      (integerp (phg15-allocation index)))
     (implies
      (integerp base)
      (integerp (phg15-region base))))))

(defun phg15-linked-p ()
  (if (phg15-linked-op) t nil))

(defun phg15-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phg15-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phg15-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3 integer division truncates toward zero.

(defun phg15-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phg15-heap-parent (index)
  (phg15-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rd and Memory.valid_rw for the arbitrary
;; allocation map t.

(defun phg15-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg15-address-base address)))
    (<= 0 (phg15-address-offset address))
    (<=
     (+ (phg15-address-offset address) length)
     (phg15-allocation (phg15-address-base address))))))

(defun phg15-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg15-address-base address))
    (<= 0 (phg15-address-offset address))
    (<=
     (+ (phg15-address-offset address) length)
     (phg15-allocation (phg15-address-base address))))))

;; Exact pointwise value of m = Function.update t_1 a_2 x_2.

(defun phg15-updated-read (a2 x2 query)
  (if (equal query a2)
      x2
    (phg15-memory query)))

;; Exact unfolding of Axiomatic.p_isheap over every mathematical integer
;; child index.

(defun-sk phg15-isheap-p (a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phg15-memory (phg15-shift a child))
      (phg15-memory
       (phg15-shift a (phg15-heap-parent child)))))))

;; A_Count.l_count_1' counts occurrences on [first,last). This recursion gives
;; its exact finite-interval characterization from the source empty, hit, and
;; miss equations. View 0 is t_1 and view 1 is the updated memory m.

(defun phg15-view-read (view a2 x2 query)
  (if (equal view 0)
      (phg15-memory query)
    (phg15-updated-read a2 x2 query)))

(defun phg15-count-span
    (view a a2 x2 first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (phg15-view-read
           view a2 x2
           (phg15-shift a (+ first (1- span))))
          value)
         1
       0)
     (phg15-count-span
      view a a2 x2 first (1- span) value))))

(defun phg15-count
    (view a a2 x2 first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (phg15-count-span
       view a a2 x2 first (- last first) value)
    0))

;; Exact unfolding of
;; Axiomatic1.p_multisetminus m t_1 a length value.

(defun phg15-multiset-minus-p
    (a a2 x2 length value)
  (equal
   (+ 1 (phg15-count 1 a a2 x2 0 length value))
   (phg15-count 0 a a2 x2 0 length value)))

(defun-sk
    ntp4vc-push-heap-loop-inv-minus-established-goal15-statement ()
  (forall
   (i a)
   (implies
    (and
     (integerp i)
     (phg15-address-p a)
     (phg15-function-types-p))
    (let*
        ((x (- i 1))
         (x1 (phg15-heap-parent x))
         (a1 (phg15-shift a x1))
         (x2 (phg15-memory a1))
         (a2 (phg15-shift a x))
         (x3 (phg15-memory a2))
         (a3
          (phg15-shift a (phg15-to-uint32 x)))
         (x4 (phg15-updated-read a2 x2 a1)))
      (implies
       (and
        (< 0 i)
        (<= (phg15-region (phg15-address-base a)) 0)
        (< 0 x1)
        (< x2 x3)
        (<= 2 i)
        (phg15-linked-p)
        (phg15-is-uint32-p i)
        (phg15-valid-rw-p (phg15-shift a 0) i)
        (phg15-is-uint32-p x1)
        (phg15-isheap-p a x)
        (phg15-is-uint32-p
         (phg15-heap-parent x1))
        (phg15-is-sint32-p x3)
        (phg15-is-sint32-p x2)
        (phg15-valid-rd-p a3 1)
        (phg15-valid-rd-p a1 1)
        (phg15-valid-rw-p a3 1)
        (phg15-is-sint32-p x4))
       (phg15-multiset-minus-p
        a a2 x2 i x3))))))

(value-triple :itpeval-statement-checked)

:q
