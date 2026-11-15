;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/random_shuffle/random_shuffle_Why3_ide_VCrandom_shuffle_loop_inv_reorder_preserved_goal2:
;; preservation of the random-shuffle array-segment multiset invariant after
;; two point updates, under the stated bounds, memory-validity, linkedness,
;; unchanged-range, value-range, and prior multiset hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun rsg2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun rsg2-address-base (address)
  (car address))

(defun rsg2-address-offset (address)
  (cdr address))

(defun rsg2-shift (address amount)
  (cons
   (rsg2-address-base address)
   (+ (rsg2-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source memories
;; t_1 and t_2, allocation map t, region function, and linked predicate
;; specialized to t.

(defstub rsg2-t1 (address) t)
(defstub rsg2-t2 (address) t)
(defstub rsg2-allocation (index) t)
(defstub rsg2-region (base) t)
(defstub rsg2-linked-op () t)

(defun-sk rsg2-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (rsg2-address-p address)
      (and
       (integerp (rsg2-t1 address))
       (integerp (rsg2-t2 address))))
     (implies
      (integerp index)
      (integerp (rsg2-allocation index)))
     (implies
      (integerp base)
      (integerp (rsg2-region base))))))

(defun rsg2-linked-p ()
  (if (rsg2-linked-op) t nil))

(defun rsg2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun rsg2-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun rsg2-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun rsg2-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (rsg2-address-base address))
    (<= 0 (rsg2-address-offset address))
    (<=
     (+ (rsg2-address-offset address) length)
     (rsg2-allocation (rsg2-address-base address))))))

(defun rsg2-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (rsg2-address-base left)
     (rsg2-address-base right)))
   (<=
    (+ (rsg2-address-offset right) right-length)
    (rsg2-address-offset left))
   (<=
    (+ (rsg2-address-offset left) left-length)
    (rsg2-address-offset right))))

;; Exact pointwise value of
;; a_2 = havoc t_1 t_2 (shift a 0) i_2, using the source havoc_access
;; equation.

(defun rsg2-a2-read (query a i2)
  (if
      (rsg2-separated-p
       query 1 (rsg2-shift a 0) i2)
      (rsg2-t2 query)
    (rsg2-t1 query)))

;; Exact pointwise value of
;; a_6 = update (update a_2 a_3 i) a_4 a_5.  The second update has
;; precedence when a_3 and a_4 coincide.

(defun rsg2-a6-read (query a i1 i2 i3 i)
  (let*
      ((a3 (rsg2-shift a i3))
       (a4
        (rsg2-shift
         a (rsg2-to-uint32 (+ 1 i1))))
       (a5 (rsg2-a2-read a3 a i2)))
    (if (equal query a4)
        a5
      (if (equal query a3)
          i
        (rsg2-a2-read query a i2)))))

;; The three memory views occurring in the source occurrence-count
;; predicates: t_2, a_2, and a_6.

(defun rsg2-view-read
    (view query a i1 i2 i3 i)
  (cond
   ((equal view 0)
    (rsg2-t2 query))
   ((equal view 1)
    (rsg2-a2-read query a i2))
   (t
    (rsg2-a6-read query a i1 i2 i3 i))))

;; A_Count.l_count_1' counts occurrences on the finite integer interval
;; [lower, upper). This recursion is its exact characterization from the
;; source empty, hit, and miss equations for signed-32 values.

(defun rsg2-count
    (view a i1 i2 i3 i lower upper value)
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
              (rsg2-view-read
               view
               (rsg2-shift a last)
               a i1 i2 i3 i)
              value)
             1
           0)
         (rsg2-count
          view a i1 i2 i3 i
          lower last value)))
    0))

;; Exact unfoldings of Axiomatic.p_unchanged_1' and
;; Axiomatic1.p_multisetunchanged_1' over all mathematical integer indices
;; and all signed 32-bit values.

(defun-sk rsg2-unchanged-a2-t2-p
    (a i2 lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (equal
      (rsg2-t2 (rsg2-shift a index))
      (rsg2-a2-read (rsg2-shift a index) a i2)))))

(defun-sk rsg2-multiset-a2-t2-p
    (a i1 i2 i3 i lower upper)
  (forall (value)
    (implies
     (rsg2-is-sint32-p value)
     (equal
      (rsg2-count
       0 a i1 i2 i3 i lower upper value)
      (rsg2-count
       1 a i1 i2 i3 i lower upper value)))))

(defun-sk rsg2-multiset-a6-t2-p
    (a i1 i2 i3 i lower upper)
  (forall (value)
    (implies
     (rsg2-is-sint32-p value)
     (equal
      (rsg2-count
       0 a i1 i2 i3 i lower upper value)
      (rsg2-count
       2 a i1 i2 i3 i lower upper value)))))

(defun-sk
    ntp4vc-random-shuffle-loop-inv-reorder-preserved-goal2-statement
    ()
  (forall
   (a i2 i3 i1 i)
   (implies
    (and
     (rsg2-address-p a)
     (integerp i2)
     (integerp i3)
     (integerp i1)
     (integerp i)
     (rsg2-function-types-p))
    (let*
        ((a1 (rsg2-shift a 0))
         (a3 (rsg2-shift a i3))
         (a4
          (rsg2-shift
           a (rsg2-to-uint32 (+ 1 i1))))
         (a5 (rsg2-a2-read a3 a i2))
         (a7 (rsg2-a6-read a3 a i1 i2 i3 i))
         (a8 (rsg2-a2-read a4 a i2)))
      (implies
       (and
        (equal a7 a8)
        (< 0 i2)
        (< 0 i3)
        (<= 0 i1)
        (< i1 i3)
        (<= i3 i2)
        (< i3 i2)
        (<= (rsg2-region (rsg2-address-base a)) 0)
        (rsg2-linked-p)
        (rsg2-is-uint32-p i1)
        (rsg2-is-uint32-p i2)
        (rsg2-is-uint32-p i3)
        (rsg2-valid-rw-p a1 i2)
        (rsg2-valid-rw-p a3 1)
        (rsg2-is-sint32-p a5)
        (rsg2-is-sint32-p a8)
        (rsg2-valid-rw-p a4 1)
        (rsg2-is-sint32-p a7)
        (rsg2-unchanged-a2-t2-p a i2 i3 i2)
        (rsg2-multiset-a2-t2-p
         a i1 i2 i3 i 0 i3))
       (rsg2-multiset-a6-t2-p
        a i1 i2 i3 i 0
        (rsg2-to-uint32 (+ 1 i3))))))))

(value-triple :itpeval-statement-checked)

:q
