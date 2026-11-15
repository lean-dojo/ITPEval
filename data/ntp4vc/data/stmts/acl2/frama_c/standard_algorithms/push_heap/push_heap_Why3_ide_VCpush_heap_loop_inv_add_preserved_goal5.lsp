;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_add_preserved_goal5:
;; preservation of the push-heap multiset-add loop invariant after a
;; havoc-based memory update and a conditional parent-value update, under the
;; stated heap, bounds, validity, and multiset hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phg5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phg5-address-base (address)
  (car address))

(defun phg5-address-offset (address)
  (cdr address))

(defun phg5-shift (address amount)
  (cons
   (phg5-address-base address)
   (+ (phg5-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_2, t_3, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub phg5-t1 (address) t)
(defstub phg5-t2 (address) t)
(defstub phg5-t3 (address) t)
(defstub phg5-allocation (index) t)
(defstub phg5-region (base) t)
(defstub phg5-linked-op () t)

(defun-sk phg5-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (phg5-address-p address)
      (and
       (integerp (phg5-t1 address))
       (integerp (phg5-t2 address))
       (integerp (phg5-t3 address))))
     (implies
      (integerp index)
      (integerp (phg5-allocation index)))
     (implies
      (integerp base)
      (integerp (phg5-region base))))))

(defun phg5-linked-p ()
  (if (phg5-linked-op) t nil))

(defun phg5-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phg5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phg5-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; For every positive argument used by this VC and its heap predicates,
;; floor((index - 1)/2) is exactly the source truncating division.

(defun phg5-heap-parent (index)
  (floor (- index 1) 2))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun phg5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phg5-address-base address))
    (<= 0 (phg5-address-offset address))
    (<=
     (+ (phg5-address-offset address) length)
     (phg5-allocation (phg5-address-base address))))))

(defun phg5-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phg5-address-base address)))
    (<= 0 (phg5-address-offset address))
    (<=
     (+ (phg5-address-offset address) length)
     (phg5-allocation (phg5-address-base address))))))

(defun phg5-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (phg5-address-base left)
     (phg5-address-base right)))
   (<=
    (+ (phg5-address-offset right) right-length)
    (phg5-address-offset left))
   (<=
    (+ (phg5-address-offset left) left-length)
    (phg5-address-offset right))))

;; Pointwise form of
;; m = update t_2 (shift a (i - 1)) (t_2 (shift a (parent (i - 1)))).

(defun phg5-m-value (a i query)
  (let*
      ((x (- i 1))
       (x1 (phg5-heap-parent x))
       (a1 (phg5-shift a x1))
       (x2 (phg5-t2 a1))
       (a2 (phg5-shift a x)))
    (if (equal query a2)
        x2
      (phg5-t2 query))))

;; Pointwise form of a_4 = havoc t_1 m (shift a 0) i, using the source
;; havoc_access equation.

(defun phg5-a4-value (a i query)
  (if
      (phg5-separated-p
       query 1 (phg5-shift a 0) i)
      (phg5-m-value a i query)
    (phg5-t1 query)))

;; Exact finite interval occurrence counts induced by A_Count.l_count_1'.

(defun phg5-view-value (view a i query)
  (cond
   ((equal view 0)
    (phg5-t2 query))
   ((equal view 1)
    (phg5-a4-value a i query))
   (t
    (phg5-t3 query))))

(defun phg5-count-span (view a i first span value)
  (if (zp span)
      0
    (+
     (if
         (equal
          (phg5-view-value
           view a i
           (phg5-shift a (+ first (1- span))))
          value)
         1
       0)
     (phg5-count-span
      view a i first (1- span) value))))

(defun phg5-count (view a i first last value)
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (phg5-count-span
       view a i first (- last first) value)
    0))

;; Exact unfoldings of the two heap predicates in the VC.

(defun-sk phg5-isheap-t2-p (a upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (phg5-t2 (phg5-shift a index))
      (phg5-t2
       (phg5-shift a (phg5-heap-parent index)))))))

(defun-sk phg5-isheap-a4-p (a i upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< 0 index)
      (< index upper))
     (<=
      (phg5-a4-value a i (phg5-shift a index))
      (phg5-a4-value
       a i
       (phg5-shift a (phg5-heap-parent index)))))))

;; Exact unfoldings of p_multisetminus, p_multisetadd,
;; p_multisetretainrest_3', and the concluding p_multisetadd.

(defun phg5-multisetminus-a4-t2-p (a i value)
  (equal
   (+ 1 (phg5-count 1 a i 0 i value))
   (phg5-count 0 a i 0 i value)))

(defun phg5-multisetadd-a4-t2-p (a i value)
  (equal
   (+ 1 (phg5-count 0 a i 0 i value))
   (phg5-count 1 a i 0 i value)))

(defun-sk phg5-multisetretainrest-a4-t2-p
    (a i removed added)
  (forall (value)
    (implies
     (and
      (integerp value)
      (not (equal value removed))
      (not (equal value added))
      (phg5-is-sint32-p value))
     (equal
      (phg5-count 0 a i 0 i value)
      (phg5-count 1 a i 0 i value)))))

(defun phg5-multisetadd-t3-t2-p (a i value)
  (equal
   (+ 1 (phg5-count 0 a i 0 i value))
   (phg5-count 2 a i 0 i value)))

;; Source function equalities are represented extensionally over every
;; source address.

(defun-sk phg5-a4-equals-t3-p (a i)
  (forall (address)
    (implies
     (phg5-address-p address)
     (equal
      (phg5-a4-value a i address)
      (phg5-t3 address)))))

(defun-sk phg5-updated-a4-equals-t3-p
    (a i update-address update-value)
  (forall (address)
    (implies
     (phg5-address-p address)
     (equal
      (if (equal address update-address)
          update-value
        (phg5-a4-value a i address))
      (phg5-t3 address)))))

(defun-sk
    ntp4vc-push-heap-loop-inv-add-preserved-goal5-statement ()
  (forall
   (i a i1)
   (implies
    (and
     (integerp i)
     (phg5-address-p a)
     (integerp i1)
     (phg5-function-types-p))
    (let*
        ((x (- i 1))
         (x1 (phg5-heap-parent x))
         (a1 (phg5-shift a x1))
         (x2 (phg5-t2 a1))
         (a2 (phg5-shift a x))
         (x3 (phg5-t2 a2))
         (a3 (phg5-shift a 0))
         (a5 (phg5-shift a i1))
         (a6 (phg5-a4-value a i a5))
         (x4 (phg5-heap-parent i1))
         (a7 (phg5-shift a x4))
         (a8 (phg5-a4-value a i a7))
         (x5 (phg5-t3 a7))
         (a9 (phg5-shift a (phg5-to-uint32 x))))
      (implies
       (and
        (< 0 i)
        (< 0 i1)
        (<= 0 i1)
        (<= (phg5-region (phg5-address-base a)) 0)
        (< 0 x1)
        (< x2 x3)
        (< a6 x3)
        (< a8 x3)
        (<= 2 i)
        (<= (+ 2 i1) i)
        (phg5-linked-p)
        (phg5-is-uint32-p i)
        (phg5-is-uint32-p i1)
        (phg5-is-uint32-p x4)
        (phg5-valid-rd-p a5 1)
        (phg5-valid-rw-p a3 i)
        (phg5-is-uint32-p x1)
        (phg5-isheap-t2-p a x)
        (phg5-is-sint32-p x5)
        (phg5-valid-rd-p a7 1)
        (phg5-is-uint32-p (phg5-heap-parent x1))
        (phg5-is-sint32-p x3)
        (phg5-is-sint32-p x2)
        (phg5-valid-rd-p a9 1)
        (phg5-valid-rd-p a1 1)
        (phg5-valid-rw-p a9 1)
        (phg5-is-sint32-p (phg5-m-value a i a1))
        (phg5-is-sint32-p a6)
        (phg5-is-sint32-p a8)
        (phg5-isheap-a4-p a i i)
        (phg5-multisetminus-a4-t2-p a i x3)
        (phg5-multisetadd-a4-t2-p a i a6)
        (phg5-multisetretainrest-a4-t2-p
         a i x3 a6)
        (if (< a6 a8)
            (and
             (phg5-updated-a4-equals-t3-p
              a i a5 a8)
             (phg5-valid-rw-p a5 1))
          (phg5-a4-equals-t3-p a i)))
       (phg5-multisetadd-t3-t2-p
        a i x5))))))

(value-triple :itpeval-statement-checked)

:q
