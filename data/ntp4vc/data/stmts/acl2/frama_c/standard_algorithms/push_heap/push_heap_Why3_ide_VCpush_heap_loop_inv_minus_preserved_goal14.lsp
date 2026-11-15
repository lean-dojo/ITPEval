;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_minus_preserved_goal14:
;; preservation of the push-heap multiset-minus loop invariant after a
;; havoc-based memory update and replacement of an element by its heap
;; parent's value, under the stated heap, bounds, validity, ordering, and
;; multiset hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phg14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phg14-address-base (address)
  (car address))

(defun phg14-address-offset (address)
  (cdr address))

(defun phg14-shift (address amount)
  (cons
   (phg14-address-base address)
   (+ (phg14-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source integer
;; memories t_1 and t_2, allocation map t, region function, and linked
;; predicate specialized to t.

(defstub phg14-t1 (address) t)
(defstub phg14-t2 (address) t)
(defstub phg14-allocation (index) t)
(defstub phg14-region (base) t)
(defstub phg14-linked-op () t)

(defun-sk phg14-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phg14-address-p address)
      (and
       (integerp (phg14-t1 address))
       (integerp (phg14-t2 address))))
     (implies
      (integerp index)
      (integerp (phg14-allocation index)))
     (implies
      (integerp base)
      (integerp (phg14-region base))))))

(defun phg14-linked-p ()
  (if (phg14-linked-op) t nil))

(defun phg14-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phg14-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phg14-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3 integer division truncates toward zero.

(defun phg14-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phg14-heap-parent (index)
  (phg14-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated for the arbitrary allocation map t.

(defun phg14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg14-address-base address))
    (<= 0 (phg14-address-offset address))
    (<=
     (+ (phg14-address-offset address) length)
     (phg14-allocation (phg14-address-base address))))))

(defun phg14-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg14-address-base address)))
    (<= 0 (phg14-address-offset address))
    (<=
     (+ (phg14-address-offset address) length)
     (phg14-allocation (phg14-address-base address))))))

(defun phg14-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (phg14-address-base left)
     (phg14-address-base right)))
   (<=
    (+ (phg14-address-offset right) right-length)
    (phg14-address-offset left))
   (<=
    (+ (phg14-address-offset left) left-length)
    (phg14-address-offset right))))

;; Pointwise form of
;; m = update t_2 (shift a (i - 1))
;;                  (t_2 (shift a (parent (i - 1)))).

(defun phg14-m-value (a i query)
  (let*
      ((x (- i 1))
       (x1 (phg14-heap-parent x))
       (a1 (phg14-shift a x1))
       (x2 (phg14-t2 a1))
       (a2 (phg14-shift a x)))
    (if (equal query a2)
        x2
      (phg14-t2 query))))

;; Pointwise form of a_4 = havoc t_1 m (shift a 0) i, using the source
;; havoc_access equation.

(defun phg14-a4-value (a i query)
  (if
      (phg14-separated-p
       query 1 (phg14-shift a 0) i)
      (phg14-m-value a i query)
    (phg14-t1 query)))

;; Pointwise form of
;; a_10 = update a_4 (shift a i_1)
;;                     (a_4 (shift a (parent i_1))).

(defun phg14-a10-value (a i i1 query)
  (let*
      ((a5 (phg14-shift a i1))
       (a7
        (phg14-shift a (phg14-heap-parent i1)))
       (a8 (phg14-a4-value a i a7)))
    (if (equal query a5)
        a8
      (phg14-a4-value a i query))))

;; Exact finite interval occurrence counts induced by A_Count.l_count_1'.
;; View 0 is t_2, view 1 is a_4, and view 2 is a_10.

(defun phg14-view-value (view a i i1 query)
  (cond
   ((equal view 0)
    (phg14-t2 query))
   ((equal view 1)
    (phg14-a4-value a i query))
   (t
    (phg14-a10-value a i i1 query))))

(defun phg14-count-span
    (view a i i1 first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (phg14-view-value
           view a i i1
           (phg14-shift a (+ first (1- span))))
          value)
         1
       0)
     (phg14-count-span
      view a i i1 first (1- span) value))))

(defun phg14-count
    (view a i i1 first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (phg14-count-span
       view a i i1 first (- last first) value)
    0))

;; Exact unfoldings of the two heap predicates in the VC.

(defun-sk phg14-isheap-t2-p (a upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (phg14-t2 (phg14-shift a index))
      (phg14-t2
       (phg14-shift a (phg14-heap-parent index)))))))

(defun-sk phg14-isheap-a4-p (a i upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (phg14-a4-value a i (phg14-shift a index))
      (phg14-a4-value
       a i
       (phg14-shift a (phg14-heap-parent index)))))))

;; Exact unfoldings of p_multisetminus, p_multisetadd,
;; p_multisetretainrest_3', and the concluding p_multisetminus.

(defun phg14-multisetminus-a4-t2-p (a i i1 value)
  (equal
   (+ 1 (phg14-count 1 a i i1 0 i value))
   (phg14-count 0 a i i1 0 i value)))

(defun phg14-multisetadd-a4-t2-p (a i i1 value)
  (equal
   (+ 1 (phg14-count 0 a i i1 0 i value))
   (phg14-count 1 a i i1 0 i value)))

(defun-sk phg14-multisetretainrest-a4-t2-p
    (a i i1 removed added)
  (forall (value)
    (implies
     (and
      (integerp value)
      (not (equal value removed))
      (not (equal value added))
      (phg14-is-sint32-p value))
     (equal
      (phg14-count 0 a i i1 0 i value)
      (phg14-count 1 a i i1 0 i value)))))

(defun phg14-multisetminus-a10-t2-p
    (a i i1 value)
  (equal
   (+ 1 (phg14-count 2 a i i1 0 i value))
   (phg14-count 0 a i i1 0 i value)))

(defun-sk
    ntp4vc-push-heap-loop-inv-minus-preserved-goal14-statement ()
  (forall
   (i a i1)
   (implies
    (and
     (integerp i)
     (phg14-address-p a)
     (integerp i1)
     (phg14-function-types-p))
    (let*
        ((x (- i 1))
         (x1 (phg14-heap-parent x))
         (a1 (phg14-shift a x1))
         (x2 (phg14-t2 a1))
         (a2 (phg14-shift a x))
         (x3 (phg14-t2 a2))
         (a3 (phg14-shift a 0))
         (a5 (phg14-shift a i1))
         (a6 (phg14-a4-value a i a5))
         (x4 (phg14-heap-parent i1))
         (a7 (phg14-shift a x4))
         (a8 (phg14-a4-value a i a7))
         (a9
          (phg14-shift a (phg14-to-uint32 x))))
      (implies
       (and
        (< 0 i)
        (< 0 i1)
        (<= 0 i1)
        (<= (phg14-region (phg14-address-base a)) 0)
        (< 0 x1)
        (< x2 x3)
        (< a6 x3)
        (< a6 a8)
        (< a8 x3)
        (<= 2 i)
        (<= (+ 2 i1) i)
        (phg14-linked-p)
        (phg14-is-uint32-p i)
        (phg14-is-uint32-p i1)
        (phg14-is-uint32-p x4)
        (phg14-valid-rd-p a5 1)
        (phg14-valid-rw-p a3 i)
        (phg14-valid-rw-p a5 1)
        (phg14-is-uint32-p x1)
        (phg14-isheap-t2-p a x)
        (phg14-valid-rd-p a7 1)
        (phg14-is-uint32-p
         (phg14-heap-parent x1))
        (phg14-is-sint32-p x3)
        (phg14-is-sint32-p x2)
        (phg14-valid-rd-p a9 1)
        (phg14-valid-rd-p a1 1)
        (phg14-valid-rw-p a9 1)
        (phg14-is-sint32-p
         (phg14-m-value a i a1))
        (phg14-is-sint32-p a6)
        (phg14-is-sint32-p a8)
        (phg14-isheap-a4-p a i i)
        (phg14-is-sint32-p
         (phg14-a10-value a i i1 a7))
        (phg14-multisetminus-a4-t2-p
         a i i1 x3)
        (phg14-multisetadd-a4-t2-p
         a i i1 a6)
        (phg14-multisetretainrest-a4-t2-p
         a i i1 x3 a6))
       (phg14-multisetminus-a10-t2-p
        a i i1 x3))))))

(value-triple :itpeval-statement-checked)

:q
