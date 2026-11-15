;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/remove_copy/remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5:
;; preservation of the remove-copy multiset-retain-rest loop invariant after
;; a havoc-based memory update and a conditional output write, under the
;; stated bounds, validity, separation, unchanged-range, and prior multiset
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun rcg5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rcg5-address-base (address)
  (car address))

(defun rcg5-address-offset (address)
  (cdr address))

(defun rcg5-shift (address amount)
  (cons
   (rcg5-address-base address)
   (+ (rcg5-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary integer memories
;; t_1, t_2, t_3, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub rcg5-t1 (address) t)
(defstub rcg5-t2 (address) t)
(defstub rcg5-t3 (address) t)
(defstub rcg5-allocation (index) t)
(defstub rcg5-region (base) t)
(defstub rcg5-linked-op () t)

(defun-sk rcg5-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (rcg5-address-p address)
      (and
       (integerp (rcg5-t1 address))
       (integerp (rcg5-t2 address))
       (integerp (rcg5-t3 address))))
     (implies
      (integerp index)
      (integerp (rcg5-allocation index)))
     (implies
      (integerp base)
      (integerp (rcg5-region base))))))

(defun rcg5-linked-p ()
  (if (rcg5-linked-op) t nil))

(defun rcg5-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun rcg5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated.

(defun rcg5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rcg5-address-base address))
    (<= 0 (rcg5-address-offset address))
    (<=
     (+ (rcg5-address-offset address) length)
     (rcg5-allocation (rcg5-address-base address))))))

(defun rcg5-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (rcg5-address-base address)))
    (<= 0 (rcg5-address-offset address))
    (<=
     (+ (rcg5-address-offset address) length)
     (rcg5-allocation (rcg5-address-base address))))))

(defun rcg5-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (rcg5-address-base left)
     (rcg5-address-base right)))
   (<=
    (+ (rcg5-address-offset right) right-length)
    (rcg5-address-offset left))
   (<=
    (+ (rcg5-address-offset left) left-length)
    (rcg5-address-offset right))))

;; Exact pointwise value of
;; a_5 = havoc t_1 t_3 (shift a 0) i_2, using the source havoc_access
;; equation.

(defun rcg5-a5-value (a i2 query)
  (if
      (rcg5-separated-p
       query 1 (rcg5-shift a 0) i2)
      (rcg5-t3 query)
    (rcg5-t1 query)))

;; The source occurrence-count function on a finite integer interval.
;; View 0 is t_3, view 1 is a_5, and view 2 is t_2.

(defun rcg5-view-value (view a i2 query)
  (cond
   ((equal view 0)
    (rcg5-t3 query))
   ((equal view 1)
    (rcg5-a5-value a i2 query))
   (t
    (rcg5-t2 query))))

(defun rcg5-count
    (view a i2 base first last value)
  (declare
   (xargs
    :measure (nfix (- last first))))
  (if
      (and
       (integerp first)
       (integerp last)
       (< first last))
      (let ((final-index (- last 1)))
        (+
         (if
             (equal
              (rcg5-view-value
               view a i2
               (rcg5-shift base final-index))
              value)
             1
           0)
         (rcg5-count
          view a i2 base first final-index value)))
    0))

;; Exact unfoldings of p_hasvalue_1', p_unchanged_1', and
;; p_multisetretainrest_1' over all mathematical integer indices and all
;; signed 32-bit values.

(defun-sk rcg5-no-hasvalue-a5-p
    (a i2 lower upper value)
  (forall (index)
    (implies
     (integerp index)
     (not
      (and
       (equal
        (rcg5-a5-value
         a i2 (rcg5-shift a index))
        value)
       (<= lower index)
       (< index upper))))))

(defun-sk rcg5-unchanged-a5-t3-p
    (a i2 base lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (rcg5-t3 (rcg5-shift base index))
      (rcg5-a5-value
       a i2 (rcg5-shift base index))))))

(defun-sk rcg5-retain-a5-t3-p
    (a a1 i2 i5 x2 removed)
  (forall (value)
    (implies
     (and
      (integerp value)
      (not (equal value removed))
      (rcg5-is-sint32-p value))
     (equal
      (rcg5-count 0 a i2 a1 0 i5 value)
      (rcg5-count 1 a i2 a 0 x2 value)))))

(defun-sk rcg5-retain-t2-t3-p
    (a a1 i2 x1 i4 removed)
  (forall (value)
    (implies
     (and
      (integerp value)
      (not (equal value removed))
      (rcg5-is-sint32-p value))
     (equal
      (rcg5-count 0 a i2 a1 0 x1 value)
      (rcg5-count 2 a i2 a 0 i4 value)))))

;; Source equalities between addr -> int functions are represented
;; extensionally over every source address.

(defun-sk rcg5-a5-equals-t2-p (a i2)
  (forall (address)
    (implies
     (rcg5-address-p address)
     (equal
      (rcg5-a5-value a i2 address)
      (rcg5-t2 address)))))

(defun-sk rcg5-updated-a5-equals-t2-p
    (a i2 update-address update-value)
  (forall (address)
    (implies
     (rcg5-address-p address)
     (equal
      (if (equal address update-address)
          update-value
        (rcg5-a5-value a i2 address))
      (rcg5-t2 address)))))

(defun-sk
    ntp4vc-remove-copy-loop-inv-retain-preserved-goal5-statement
    ()
  (forall
   (a1 i5 i a i2 i1 i3 i4 p)
   (implies
    (and
     (rcg5-address-p a1)
     (integerp i5)
     (integerp i)
     (rcg5-address-p a)
     (integerp i2)
     (integerp i1)
     (integerp i3)
     (integerp i4)
     (booleanp p)
     (rcg5-function-types-p))
    (let*
        ((x (rcg5-count 0 a i2 a1 0 i5 i))
         (x1 (+ 1 i5))
         (a2 (rcg5-shift a1 0))
         (a3 (rcg5-shift a1 i5))
         (a4 (rcg5-shift a 0))
         (x2 (- i5 x))
         (a6 (rcg5-a5-value a i2 a3))
         (a7 (rcg5-shift a x2)))
      (implies
       (and
        (<= i5 i2)
        (< i5 i2)
        (<= (rcg5-region (rcg5-address-base a)) 0)
        (<= (rcg5-region (rcg5-address-base a1)) 0)
        (<= x i5)
        (<= 0 x)
        (<= i5 4294967294)
        (rcg5-linked-p)
        (rcg5-is-uint32-p i1)
        (rcg5-is-uint32-p i2)
        (rcg5-is-uint32-p i3)
        (rcg5-is-uint32-p i4)
        (rcg5-is-uint32-p i5)
        (rcg5-is-sint32-p i)
        (rcg5-is-uint32-p x1)
        (rcg5-valid-rd-p a2 i2)
        (rcg5-valid-rd-p a3 1)
        (rcg5-valid-rw-p a4 i2)
        (rcg5-separated-p a2 i2 a 1)
        (rcg5-is-uint32-p x2)
        (rcg5-is-sint32-p a6)
        (rcg5-no-hasvalue-a5-p a i2 0 x2 i)
        (rcg5-unchanged-a5-t3-p
         a i2 a1 i5 i2)
        (rcg5-unchanged-a5-t3-p
         a i2 a x2 i2)
        (rcg5-retain-a5-t3-p
         a a1 i2 i5 x2 i)
        (if (equal a6 i)
            (and
             (rcg5-a5-equals-t2-p a i2)
             (equal
              (+ i4
                 (rcg5-count
                  0 a i2 a1 0 i5
                  (rcg5-t2 a3)))
              i5))
          (and
           (equal p nil)
           (equal i3 i1)
           (equal (+ i1 x) i5)
           (equal (+ i3 x) i5)
           (equal (+ i4 x) x1)
           (rcg5-updated-a5-equals-t2-p
            a i2 a7 a6)
           (<= i5 (+ 4294967294 x))
           (rcg5-valid-rw-p a7 1))))
       (rcg5-retain-t2-t3-p
        a a1 i2 x1 i4 i))))))

(value-triple :itpeval-statement-checked)

:q
