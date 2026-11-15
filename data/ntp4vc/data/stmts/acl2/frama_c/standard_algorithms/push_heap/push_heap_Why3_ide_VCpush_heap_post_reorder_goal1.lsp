;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_post_reorder_goal1:
;; preservation of the signed-32-bit multiset on the push-heap range after
;; the stated conditional memory updates, under the heap, bounds, linkedness,
;; memory-validity, havoc, and multiset hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun phpost1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun phpost1-address-base (address)
  (car address))

(defun phpost1-address-offset (address)
  (cdr address))

(defun phpost1-shift (address amount)
  (cons
   (phpost1-address-base address)
   (+ (phpost1-address-offset address) amount)))

;; Conservative interfaces for the universally arbitrary source integer
;; memories t_1, t_2, t_3, t_4, allocation map t, region function, and
;; linked predicate specialized to t.

(defstub phpost1-memory (view address) t)
(defstub phpost1-allocation (index) t)
(defstub phpost1-region (base) t)
(defstub phpost1-linked-op () t)
(defstub phpost1-arbitrary-count
    (memory-view address lower upper value) t)

(defun phpost1-count-view-p (view)
  (or
   (equal view 2)
   (equal view 3)
   (equal view 4)))

(defun-sk phpost1-function-types-p ()
  (forall
   (address index base memory-view lower upper value)
    (and
     (implies
      (phpost1-address-p address)
      (and
       (integerp (phpost1-memory 1 address))
       (integerp (phpost1-memory 2 address))
       (integerp (phpost1-memory 3 address))
       (integerp (phpost1-memory 4 address))))
     (implies
      (integerp index)
      (integerp (phpost1-allocation index)))
     (implies
      (integerp base)
      (integerp (phpost1-region base)))
     (implies
      (and
       (phpost1-count-view-p memory-view)
       (phpost1-address-p address)
       (integerp lower)
       (integerp upper)
       (integerp value))
      (integerp
       (phpost1-arbitrary-count
        memory-view address lower upper value))))))

(defun phpost1-linked-p ()
  (if (phpost1-linked-op) t nil))

(defun phpost1-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun phpost1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Cint.to_uint32 is the canonical residue in [0, 2^32).

(defun phpost1-to-uint32 (value)
  (if (integerp value)
      (mod value 4294967296)
    0))

;; Why3 integer division truncates toward zero.

(defun phpost1-tdiv-by-two (value)
  (if (integerp value)
      (if (< value 0)
          (- (floor (- value) 2))
        (floor value 2))
    0))

(defun phpost1-heap-parent (index)
  (phpost1-tdiv-by-two (- index 1)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and
;; Memory.separated for the arbitrary allocation map t.

(defun phpost1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (phpost1-address-base address))
    (<= 0 (phpost1-address-offset address))
    (<=
     (+ (phpost1-address-offset address) length)
     (phpost1-allocation
      (phpost1-address-base address))))))

(defun phpost1-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (phpost1-address-base address)))
    (<= 0 (phpost1-address-offset address))
    (<=
     (+ (phpost1-address-offset address) length)
     (phpost1-allocation
      (phpost1-address-base address))))))

(defun phpost1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (phpost1-address-base left)
     (phpost1-address-base right)))
   (<=
    (+ (phpost1-address-offset right) right-length)
    (phpost1-address-offset left))
   (<=
    (+ (phpost1-address-offset left) left-length)
    (phpost1-address-offset right))))

;; Exact pointwise value of
;; m = Function.update t_4 (shift a (i_1 - 1)) (t_4 (shift a i_5)).

(defun phpost1-m-read (a i1 i5 query)
  (let*
      ((x (- i1 1))
       (a2 (phpost1-shift a i5))
       (x1 (phpost1-memory 4 a2))
       (a4 (phpost1-shift a x)))
    (if (equal query a4)
        x1
      (phpost1-memory 4 query))))

;; Exact pointwise value of havoc t_1 m (shift a 0) i_1, using the source
;; havoc_access equation.

(defun phpost1-havoc-read (a i1 i5 query)
  (if
      (phpost1-separated-p
       query 1 (phpost1-shift a 0) i1)
      (phpost1-m-read a i1 i5 query)
    (phpost1-memory 1 query)))

;; Source equalities between addr -> int functions are represented
;; extensionally over every source address.

(defun-sk phpost1-updated-t2-equals-t3-p
    (a i3 update-value)
  (forall (query)
    (implies
     (phpost1-address-p query)
     (equal
      (if (equal query (phpost1-shift a i3))
          update-value
        (phpost1-memory 2 query))
      (phpost1-memory 3 query)))))

(defun-sk phpost1-havoc-equals-t2-p (a i1 i5)
  (forall (query)
    (implies
     (phpost1-address-p query)
     (equal
      (phpost1-havoc-read a i1 i5 query)
      (phpost1-memory 2 query)))))

(defun-sk phpost1-m-equals-t2-p (a i1 i5)
  (forall (query)
    (implies
     (phpost1-address-p query)
     (equal
      (phpost1-m-read a i1 i5 query)
      (phpost1-memory 2 query)))))

(defun-sk phpost1-t4-equals-t3-p ()
  (forall (query)
    (implies
     (phpost1-address-p query)
     (equal
      (phpost1-memory 4 query)
      (phpost1-memory 3 query)))))

;; The source count operator receives a memory function as an argument, so
;; extensionally equal source memories have equal arbitrary count results.

(defun-sk phpost1-memory-views-equal-p
    (left-view right-view)
  (forall (query)
    (implies
     (phpost1-address-p query)
     (equal
      (phpost1-memory left-view query)
      (phpost1-memory right-view query)))))

(defun-sk phpost1-arbitrary-count-extensional-p ()
  (forall
   (left-view right-view address lower upper value)
   (implies
    (and
     (phpost1-count-view-p left-view)
     (phpost1-count-view-p right-view)
     (phpost1-address-p address)
     (integerp lower)
     (integerp upper)
     (integerp value)
     (not (phpost1-is-sint32-p value))
     (phpost1-memory-views-equal-p
      left-view right-view))
    (equal
     (phpost1-arbitrary-count
      left-view address lower upper value)
     (phpost1-arbitrary-count
      right-view address lower upper value)))))

;; Exact unfolding of Axiomatic.p_isheap.

(defun-sk phpost1-isheap-p (memory-view a upper)
  (forall (child)
    (implies
     (and
      (integerp child)
      (< 0 child)
      (< child upper))
     (<=
      (phpost1-memory
       memory-view (phpost1-shift a child))
      (phpost1-memory
       memory-view
       (phpost1-shift
        a (phpost1-heap-parent child)))))))

;; The A_Count axioms characterize l_count_1' recursively only for signed
;; 32-bit query values. For those values, this is the exact finite-interval
;; count on [lower, upper). Outside that domain, the source leaves the integer
;; result arbitrary, represented by phpost1-arbitrary-count. Views 2, 3, and
;; 4 denote t_2, t_3, and t_4.

(defun phpost1-signed-count
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
              (phpost1-memory
               memory-view
               (phpost1-shift a last))
              value)
             1
           0)
         (phpost1-signed-count
          memory-view a lower last value)))
    0))

(defun phpost1-count
    (memory-view a lower upper value)
  (if (phpost1-is-sint32-p value)
      (phpost1-signed-count
       memory-view a lower upper value)
    (phpost1-arbitrary-count
     memory-view a lower upper value)))

;; Exact unfoldings of p_multisetadd, p_multisetminus,
;; p_multisetretainrest_3', and p_multisetunchanged_1'.

(defun phpost1-multiset-add-t2-t4-p
    (a upper value)
  (equal
   (+ 1 (phpost1-count 4 a 0 upper value))
   (phpost1-count 2 a 0 upper value)))

(defun phpost1-multiset-minus-t2-t4-p
    (a upper value)
  (equal
   (+ 1 (phpost1-count 2 a 0 upper value))
   (phpost1-count 4 a 0 upper value)))

(defun-sk phpost1-multiset-retain-rest-t2-t4-p
    (a upper removed added)
  (forall (value)
    (implies
     (and
      (integerp value)
      (not (equal value removed))
      (not (equal value added))
      (phpost1-is-sint32-p value))
     (equal
      (phpost1-count 4 a 0 upper value)
      (phpost1-count 2 a 0 upper value)))))

(defun-sk phpost1-multiset-unchanged-t3-t4-p
    (a lower upper)
  (forall (value)
    (implies
     (and
      (integerp value)
      (phpost1-is-sint32-p value))
     (equal
      (phpost1-count 4 a lower upper value)
      (phpost1-count 3 a lower upper value)))))

(defun-sk ntp4vc-push-heap-post-reorder-goal1-statement ()
  (forall
   (a i1 i5 i3 i i2 i4 p1 p)
   (implies
    (and
     (phpost1-address-p a)
     (integerp i1)
     (integerp i5)
     (integerp i3)
     (integerp i)
     (integerp i2)
     (integerp i4)
     (booleanp p1)
     (booleanp p)
     (phpost1-function-types-p)
     (phpost1-arbitrary-count-extensional-p))
    (let*
        ((a1 (phpost1-shift a 0))
         (x (- i1 1))
         (a2 (phpost1-shift a i5))
         (a3
          (phpost1-shift
           a (phpost1-to-uint32 x)))
         (x1 (phpost1-memory 4 a2))
         (a4 (phpost1-shift a x))
         (x2 (phpost1-memory 4 a4))
         (a5 (phpost1-shift a i3))
         (x3 (phpost1-memory 2 a5))
         (a6 (phpost1-shift a i)))
      (implies
       (and
        (< 0 i1)
        (<=
         (phpost1-region
          (phpost1-address-base a))
         0)
        (phpost1-linked-p)
        (phpost1-is-uint32-p i)
        (phpost1-is-uint32-p i1)
        (phpost1-is-uint32-p i2)
        (phpost1-is-uint32-p i3)
        (phpost1-is-uint32-p i4)
        (phpost1-is-uint32-p i5)
        (phpost1-valid-rw-p a1 i1)
        (phpost1-isheap-p 4 a x)
        (if (<= 2 i1)
            (and
             (equal p1 nil)
             (equal (phpost1-heap-parent x) i5)
             (phpost1-valid-rd-p a2 1)
             (phpost1-valid-rd-p a3 1)
             (if (< x1 x2)
                 (and
                  (phpost1-updated-t2-equals-t3-p
                   a i3 x2)
                  (phpost1-valid-rw-p a5 1)
                  (phpost1-valid-rw-p a3 1)
                  (if (< 0 i5)
                      (and
                       (equal p nil)
                       (equal i3 i2)
                       (equal i4 i2)
                       (equal i4 i3)
                       (equal
                        (phpost1-heap-parent i3)
                        i)
                       (phpost1-havoc-equals-t2-p
                        a i1 i5)
                       (<= 0 i3)
                       (< x3 x2)
                       (<= (+ 2 i3) i1)
                       (phpost1-isheap-p 2 a i1)
                       (phpost1-multiset-add-t2-t4-p
                        a i1 x3)
                       (phpost1-multiset-minus-t2-t4-p
                        a i1 x2)
                       (phpost1-multiset-retain-rest-t2-t4-p
                        a i1 x2 x3)
                       (or
                        (<= i3 0)
                        (and
                         (<=
                          x2
                          (phpost1-memory 2 a6))
                         (phpost1-valid-rd-p
                          a6 1))))
                    (and
                     (equal i5 i3)
                     (phpost1-m-equals-t2-p
                      a i1 i5))))
               (phpost1-t4-equals-t3-p)))
          (phpost1-t4-equals-t3-p)))
       (phpost1-multiset-unchanged-t3-t4-p
        a 0 i1))))))

(value-triple :itpeval-statement-checked)

:q
