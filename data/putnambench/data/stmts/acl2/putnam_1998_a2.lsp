;; Statement-only formalization of PutnamBench corpus artifact putnam_1998_a2:
;; for first-quadrant unit-circle arcs, the sum of the two specified Lebesgue
;; areas depends only on the arc length. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive complete real field or Lebesgue measure.  The
;; conservative interfaces below present those objects, and every field,
;; completeness, set, sigma-algebra, additivity, invariance, normalization,
;; measurability, and finiteness property used by the statement is an explicit
;; hypothesis of the final predicate.  Arbitrary scalar subsets, plane
;; subsets, and countable families are represented extensionally by tame
;; APPLY$ function objects; none is replaced by a finite table.

(defstub p98a2-real-p (real-type value) t)
(defstub p98a2-zero (real-type) t)
(defstub p98a2-one (real-type) t)
(defstub p98a2-add (real-type left right) t)
(defstub p98a2-mul (real-type left right) t)
(defstub p98a2-neg (real-type value) t)
(defstub p98a2-inv (real-type value) t)
(defstub p98a2-less (real-type left right) t)

(defstub p98a2-empty-set (real-type) t)
(defstub p98a2-complement-set (real-type set) t)
(defstub p98a2-union-sequence-set (real-type sequence) t)
(defstub p98a2-unit-square-set (real-type) t)
(defstub p98a2-translate-set
  (real-type shift-x shift-y set)
  t)
(defstub p98a2-below-arc-set
  (real-type p-x p-y q-x q-y)
  t)
(defstub p98a2-left-of-arc-set
  (real-type p-x p-y q-x q-y)
  t)
(defstub p98a2-measurable-p (real-type set) t)
(defstub p98a2-measure (real-type set) t)

(defun p98a2-scalar-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun p98a2-plane-set-p (set)
  (tamep-functionp set))

(defun p98a2-plane-member-p (set x y)
  (if (apply$ set (list x y)) t nil))

(defun p98a2-sequence-set (sequence n)
  (apply$ sequence (list n)))

(defun p98a2-leq (real-type left right)
  (not (p98a2-less real-type right left)))

(defun p98a2-sub (real-type left right)
  (p98a2-add real-type left (p98a2-neg real-type right)))

(defun p98a2-square (real-type value)
  (p98a2-mul real-type value value))

(defun-sk p98a2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and (p98a2-real-p real-type x)
          (p98a2-real-p real-type y)
          (p98a2-real-p real-type z))
     (let* ((zero (p98a2-zero real-type))
            (one (p98a2-one real-type))
            (xy-add (p98a2-add real-type x y))
            (yz-add (p98a2-add real-type y z))
            (xy-mul (p98a2-mul real-type x y))
            (yz-mul (p98a2-mul real-type y z))
            (neg-x (p98a2-neg real-type x))
            (inv-x (p98a2-inv real-type x)))
       (and
        (p98a2-real-p real-type xy-add)
        (p98a2-real-p real-type xy-mul)
        (p98a2-real-p real-type neg-x)
        (p98a2-real-p real-type inv-x)
        (equal (p98a2-add real-type xy-add z)
               (p98a2-add real-type x yz-add))
        (equal xy-add (p98a2-add real-type y x))
        (equal (p98a2-add real-type x zero) x)
        (equal (p98a2-add real-type x neg-x) zero)
        (equal (p98a2-mul real-type xy-mul z)
               (p98a2-mul real-type x yz-mul))
        (equal xy-mul (p98a2-mul real-type y x))
        (equal (p98a2-mul real-type x one) x)
        (implies (equal x zero)
                 (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (p98a2-mul real-type x inv-x) one))
        (equal
         (p98a2-mul real-type x yz-add)
         (p98a2-add
          real-type
          (p98a2-mul real-type x y)
          (p98a2-mul real-type x z))))))))

(defun-sk p98a2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and (p98a2-real-p real-type x)
          (p98a2-real-p real-type y)
          (p98a2-real-p real-type z))
     (let ((zero (p98a2-zero real-type)))
       (and
        (not (p98a2-less real-type x x))
        (or (p98a2-less real-type x y)
            (equal x y)
            (p98a2-less real-type y x))
        (implies
         (and (p98a2-less real-type x y)
              (p98a2-less real-type y z))
         (p98a2-less real-type x z))
        (implies
         (p98a2-less real-type x y)
         (p98a2-less
          real-type
          (p98a2-add real-type x z)
          (p98a2-add real-type y z)))
        (implies
         (and (p98a2-less real-type zero x)
              (p98a2-less real-type zero y))
         (p98a2-less
          real-type
          zero
          (p98a2-mul real-type x y))))))))

(defun-sk p98a2-valid-scalar-set-p (real-type set)
  (forall (x)
    (implies
     (p98a2-scalar-set-member-p set x)
     (p98a2-real-p real-type x))))

(defun-sk p98a2-upper-bound-p (real-type set upper)
  (forall (x)
    (implies
     (and (p98a2-real-p real-type x)
          (p98a2-scalar-set-member-p set x))
     (p98a2-leq real-type x upper))))

(defun-sk p98a2-scalar-set-nonempty-p (real-type set)
  (exists (x)
    (and (p98a2-real-p real-type x)
         (p98a2-scalar-set-member-p set x))))

(defun-sk p98a2-scalar-set-bounded-p (real-type set)
  (exists (upper)
    (and (p98a2-real-p real-type upper)
         (p98a2-upper-bound-p real-type set upper))))

(defun-sk p98a2-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and (p98a2-real-p real-type upper)
          (p98a2-upper-bound-p real-type set upper))
     (p98a2-leq real-type supremum upper))))

(defun p98a2-supremum-p
    (real-type set supremum)
  (and
   (p98a2-real-p real-type supremum)
   (p98a2-upper-bound-p real-type set supremum)
   (p98a2-least-upper-bound-p
    real-type set supremum)))

(defun-sk p98a2-has-supremum-p
    (real-type set)
  (exists (supremum)
    (p98a2-supremum-p
     real-type set supremum)))

(defun-sk p98a2-completeness-p (real-type)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (p98a2-valid-scalar-set-p real-type set)
          (p98a2-scalar-set-nonempty-p real-type set)
          (p98a2-scalar-set-bounded-p real-type set))
     (p98a2-has-supremum-p
      real-type set))))

(defun p98a2-real-field-p (real-type)
  (let ((zero (p98a2-zero real-type))
        (one (p98a2-one real-type)))
    (and
     (p98a2-real-p real-type zero)
     (p98a2-real-p real-type one)
     (not (equal zero one))
     (p98a2-field-laws-p real-type)
     (p98a2-order-laws-p real-type)
     (p98a2-less real-type zero one)
     (p98a2-completeness-p real-type))))

;; Coordinates inline EuclideanSpace R (Fin 2).  On unit vectors the dot
;; product is cos of their inner-product angle.  Since all relevant angles
;; lie strictly between 0 and pi/2, dot product is an injective code for arc
;; length.  Thus existence of a real function of this code is bidirectionally
;; equivalent to existence of a real function of the source arc angle, after
;; extending either function arbitrarily away from attained values.

(defun p98a2-first-quadrant-unit-point-p
    (real-type x y)
  (let ((zero (p98a2-zero real-type))
        (one (p98a2-one real-type)))
    (and
     (p98a2-real-p real-type x)
     (p98a2-real-p real-type y)
     (p98a2-less real-type zero x)
     (p98a2-less real-type zero y)
     (equal
      (p98a2-add
       real-type
       (p98a2-square real-type x)
       (p98a2-square real-type y))
      one))))

(defun p98a2-is-arc-p
    (real-type p-x p-y q-x q-y)
  (and
   (p98a2-first-quadrant-unit-point-p
    real-type p-x p-y)
   (p98a2-first-quadrant-unit-point-p
    real-type q-x q-y)
   (p98a2-less real-type q-x p-x)))

(defun p98a2-arc-length-code
    (real-type p-x p-y q-x q-y)
  (p98a2-add
   real-type
   (p98a2-mul real-type p-x q-x)
   (p98a2-mul real-type p-y q-y)))

;; Exact extensional definitions of the two planar regions from the source.

(defun-sk p98a2-below-member-witness-p
    (real-type p-x p-y q-x q-y s-x s-y)
  (exists (r-x r-y)
    (and
     (p98a2-first-quadrant-unit-point-p
      real-type r-x r-y)
     (p98a2-less real-type r-x p-x)
     (p98a2-less real-type q-x r-x)
     (equal r-x s-x)
     (p98a2-less real-type s-y r-y)
     (p98a2-less real-type
                   (p98a2-zero real-type)
                   s-y))))

(defun-sk p98a2-left-member-witness-p
    (real-type p-x p-y q-x q-y s-x s-y)
  (exists (r-x r-y)
    (and
     (p98a2-first-quadrant-unit-point-p
      real-type r-x r-y)
     (p98a2-less real-type r-x p-x)
     (p98a2-less real-type q-x r-x)
     (equal r-y s-y)
     (p98a2-less real-type s-x r-x)
     (p98a2-less real-type
                   (p98a2-zero real-type)
                   s-x))))

(defun-sk p98a2-plane-sets-equiv-p
    (real-type left right)
  (forall (x y)
    (implies
     (and (p98a2-real-p real-type x)
          (p98a2-real-p real-type y))
     (iff
      (p98a2-plane-member-p left x y)
      (p98a2-plane-member-p right x y)))))

(defun-sk p98a2-plane-set-sequence-p
    (sequence)
  (forall (n)
    (implies
     (natp n)
     (p98a2-plane-set-p
      (p98a2-sequence-set sequence n)))))

(defun-sk p98a2-union-member-exists-p
    (sequence x y)
  (exists (n)
    (and
     (natp n)
     (p98a2-plane-member-p
      (p98a2-sequence-set sequence n)
      x y))))

(defun-sk p98a2-empty-set-law-p (real-type)
  (forall (x y)
    (implies
     (and (p98a2-real-p real-type x)
          (p98a2-real-p real-type y))
     (and
      (p98a2-plane-set-p
       (p98a2-empty-set real-type))
      (not
       (p98a2-plane-member-p
        (p98a2-empty-set real-type)
        x y))))))

(defun-sk p98a2-complement-set-law-p (real-type)
  (forall (set x y)
    (implies
     (and (p98a2-plane-set-p set)
          (p98a2-real-p real-type x)
          (p98a2-real-p real-type y))
     (and
      (p98a2-plane-set-p
       (p98a2-complement-set real-type set))
      (iff
       (p98a2-plane-member-p
        (p98a2-complement-set real-type set)
        x y)
       (not
        (p98a2-plane-member-p
         set x y)))))))

(defun-sk p98a2-union-set-law-p (real-type)
  (forall (sequence x y)
    (implies
     (and (tamep-functionp sequence)
          (p98a2-plane-set-sequence-p sequence)
          (p98a2-real-p real-type x)
          (p98a2-real-p real-type y))
     (and
      (p98a2-plane-set-p
       (p98a2-union-sequence-set real-type sequence))
      (iff
       (p98a2-plane-member-p
        (p98a2-union-sequence-set real-type sequence)
        x y)
       (p98a2-union-member-exists-p
        sequence x y))))))

(defun-sk p98a2-unit-square-law-p (real-type)
  (forall (x y)
    (let ((zero (p98a2-zero real-type))
          (one (p98a2-one real-type)))
      (implies
       (and (p98a2-real-p real-type x)
            (p98a2-real-p real-type y))
       (and
        (p98a2-plane-set-p
         (p98a2-unit-square-set real-type))
        (iff
         (p98a2-plane-member-p
          (p98a2-unit-square-set real-type)
          x y)
         (and
          (p98a2-leq real-type zero x)
          (p98a2-less real-type x one)
          (p98a2-leq real-type zero y)
          (p98a2-less real-type y one))))))))

(defun-sk p98a2-translate-set-law-p (real-type)
  (forall (set shift-x shift-y x y)
    (implies
     (and (p98a2-plane-set-p set)
          (p98a2-real-p real-type shift-x)
          (p98a2-real-p real-type shift-y)
          (p98a2-real-p real-type x)
          (p98a2-real-p real-type y))
     (and
      (p98a2-plane-set-p
       (p98a2-translate-set
        real-type shift-x shift-y set))
      (iff
       (p98a2-plane-member-p
        (p98a2-translate-set
         real-type shift-x shift-y set)
        x y)
       (p98a2-plane-member-p
        set
        (p98a2-sub real-type x shift-x)
        (p98a2-sub real-type y shift-y)))))))

(defun-sk p98a2-below-arc-set-law-p (real-type)
  (forall (p-x p-y q-x q-y s-x s-y)
    (implies
     (and
      (p98a2-real-p real-type p-x)
      (p98a2-real-p real-type p-y)
      (p98a2-real-p real-type q-x)
      (p98a2-real-p real-type q-y)
      (p98a2-real-p real-type s-x)
     (p98a2-real-p real-type s-y))
     (and
      (p98a2-plane-set-p
       (p98a2-below-arc-set
        real-type p-x p-y q-x q-y))
      (iff
       (p98a2-plane-member-p
        (p98a2-below-arc-set
         real-type p-x p-y q-x q-y)
        s-x s-y)
       (p98a2-below-member-witness-p
        real-type p-x p-y q-x q-y s-x s-y))))))

(defun-sk p98a2-left-of-arc-set-law-p (real-type)
  (forall (p-x p-y q-x q-y s-x s-y)
    (implies
     (and
      (p98a2-real-p real-type p-x)
      (p98a2-real-p real-type p-y)
      (p98a2-real-p real-type q-x)
      (p98a2-real-p real-type q-y)
      (p98a2-real-p real-type s-x)
     (p98a2-real-p real-type s-y))
     (and
      (p98a2-plane-set-p
       (p98a2-left-of-arc-set
        real-type p-x p-y q-x q-y))
      (iff
       (p98a2-plane-member-p
        (p98a2-left-of-arc-set
         real-type p-x p-y q-x q-y)
        s-x s-y)
       (p98a2-left-member-witness-p
        real-type p-x p-y q-x q-y s-x s-y))))))

(defun p98a2-set-constructor-laws-p (real-type)
  (and
   (p98a2-empty-set-law-p real-type)
   (p98a2-complement-set-law-p real-type)
   (p98a2-union-set-law-p real-type)
   (p98a2-unit-square-law-p real-type)
   (p98a2-translate-set-law-p real-type)
   (p98a2-below-arc-set-law-p real-type)
   (p98a2-left-of-arc-set-law-p real-type)))

(defun-sk p98a2-measurable-sequence-elements-p
    (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (and
      (p98a2-plane-set-p
       (p98a2-sequence-set sequence n))
      (p98a2-measurable-p
       real-type
       (p98a2-sequence-set sequence n))))))

(defun p98a2-measurable-sequence-p
    (real-type sequence)
  (and
   (tamep-functionp sequence)
   (p98a2-plane-set-sequence-p sequence)
   (p98a2-measurable-sequence-elements-p
    real-type sequence)))

(defun p98a2-distance-square
    (real-type x y u v)
  (p98a2-add
   real-type
   (p98a2-square
    real-type
    (p98a2-sub real-type u x))
   (p98a2-square
    real-type
    (p98a2-sub real-type v y))))

(defun-sk p98a2-ball-contained-p
    (real-type set x y radius)
  (forall (u v)
    (implies
     (and
      (p98a2-real-p real-type u)
      (p98a2-real-p real-type v)
      (p98a2-less
       real-type
       (p98a2-distance-square
        real-type x y u v)
       (p98a2-square real-type radius)))
     (p98a2-plane-member-p set u v))))

(defun-sk p98a2-interior-point-p
    (real-type set x y)
  (exists (radius)
    (and
     (p98a2-real-p real-type radius)
     (p98a2-less
      real-type
      (p98a2-zero real-type)
      radius)
     (p98a2-ball-contained-p
      real-type set x y radius))))

(defun-sk p98a2-open-set-p
    (real-type set)
  (forall (x y)
    (implies
     (and
      (p98a2-real-p real-type x)
      (p98a2-real-p real-type y)
      (p98a2-plane-member-p set x y))
     (p98a2-interior-point-p
      real-type set x y))))

(defun-sk p98a2-open-sets-measurable-p
    (real-type)
  (forall (set)
    (implies
     (and
      (p98a2-plane-set-p set)
      (p98a2-open-set-p real-type set))
     (p98a2-measurable-p real-type set))))

(defun-sk p98a2-sigma-algebra-laws-p (real-type)
  (forall (set sequence)
    (and
     (p98a2-measurable-p
     real-type
     (p98a2-empty-set real-type))
     (implies
      (p98a2-measurable-p real-type set)
      (and
       (p98a2-plane-set-p set)
       (p98a2-measurable-p
        real-type
        (p98a2-complement-set real-type set))))
     (implies
      (p98a2-measurable-sequence-p real-type sequence)
      (p98a2-measurable-p
       real-type
       (p98a2-union-sequence-set
        real-type sequence))))))

;; Extended nonnegative real values and countable sums.

(defun p98a2-ennreal-p (real-type value)
  (or
   (equal value :p98a2-top)
   (and
    (consp value)
    (equal (car value) :p98a2-finite)
    (p98a2-real-p real-type (cdr value))
    (p98a2-leq
     real-type
     (p98a2-zero real-type)
     (cdr value)))))

(defun p98a2-ennreal-finite (value)
  (cons :p98a2-finite value))

(defun p98a2-ennreal-zero (real-type)
  (p98a2-ennreal-finite (p98a2-zero real-type)))

(defun p98a2-ennreal-add (real-type left right)
  (if
   (or (equal left :p98a2-top)
       (equal right :p98a2-top))
   :p98a2-top
   (p98a2-ennreal-finite
    (p98a2-add real-type (cdr left) (cdr right)))))

(defun p98a2-ennreal-leq (real-type left right)
  (cond
   ((equal right :p98a2-top) t)
   ((equal left :p98a2-top) nil)
   (t
    (p98a2-leq
     real-type (cdr left) (cdr right)))))

(defun p98a2-partial-measure-sum
    (real-type sequence count)
  (declare (xargs :measure (nfix count)))
  (if
   (zp count)
   (p98a2-ennreal-zero real-type)
   (p98a2-ennreal-add
    real-type
    (p98a2-partial-measure-sum
     real-type sequence (1- count))
    (p98a2-measure
     real-type
     (p98a2-sequence-set
      sequence (1- count))))))

(defun-sk p98a2-sum-upper-bound-p
    (real-type sequence total)
  (forall (count)
    (implies
     (natp count)
     (p98a2-ennreal-leq
      real-type
      (p98a2-partial-measure-sum
       real-type sequence count)
      total))))

(defun-sk p98a2-countable-sum-least-p
    (real-type sequence total)
  (forall (bound)
    (implies
     (and
      (p98a2-ennreal-p real-type bound)
      (p98a2-sum-upper-bound-p
       real-type sequence bound))
     (p98a2-ennreal-leq
      real-type total bound))))

(defun p98a2-infinite-sum-p
    (real-type sequence total)
  (and
   (p98a2-ennreal-p real-type total)
   (p98a2-sum-upper-bound-p
    real-type sequence total)
   (p98a2-countable-sum-least-p
    real-type sequence total)))

(defun-sk p98a2-disjoint-sets-p
    (real-type left right)
  (forall (x y)
    (implies
     (and
      (p98a2-real-p real-type x)
      (p98a2-real-p real-type y))
     (not
      (and
       (p98a2-plane-member-p
        left x y)
       (p98a2-plane-member-p
        right x y))))))

(defun-sk p98a2-pairwise-disjoint-p
    (real-type sequence)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (not (equal m n)))
     (p98a2-disjoint-sets-p
      real-type
      (p98a2-sequence-set sequence m)
      (p98a2-sequence-set sequence n)))))

(defun-sk p98a2-measure-values-p (real-type)
  (forall (set)
    (implies
     (p98a2-plane-set-p set)
     (p98a2-ennreal-p
      real-type
      (p98a2-measure real-type set)))))

(defun-sk p98a2-measure-extensional-p (real-type)
  (forall (left right)
    (implies
     (and
      (p98a2-plane-set-p left)
      (p98a2-plane-set-p right)
      (p98a2-plane-sets-equiv-p
       real-type left right))
     (equal
      (p98a2-measure real-type left)
      (p98a2-measure real-type right)))))

(defun-sk p98a2-countable-additivity-p (real-type)
  (forall (sequence)
    (implies
     (and
      (p98a2-measurable-sequence-p
       real-type sequence)
      (p98a2-pairwise-disjoint-p
       real-type sequence))
     (p98a2-infinite-sum-p
      real-type
      sequence
      (p98a2-measure
       real-type
       (p98a2-union-sequence-set
        real-type sequence))))))

(defun-sk p98a2-translation-invariance-p (real-type)
  (forall (shift-x shift-y set)
    (implies
     (and
      (p98a2-real-p real-type shift-x)
      (p98a2-real-p real-type shift-y)
      (p98a2-measurable-p real-type set))
     (equal
      (p98a2-measure
       real-type
       (p98a2-translate-set
        real-type shift-x shift-y set))
      (p98a2-measure real-type set)))))

(defun p98a2-finite-measure-p (real-type set)
  (let ((value (p98a2-measure real-type set)))
    (and
     (consp value)
     (equal (car value) :p98a2-finite)
     (p98a2-real-p real-type (cdr value)))))

(defun p98a2-measure-to-real (real-type set)
  (let ((value (p98a2-measure real-type set)))
    (if
     (and
      (consp value)
      (equal (car value) :p98a2-finite)
      (p98a2-real-p real-type (cdr value)))
     (cdr value)
     (p98a2-zero real-type))))

(defun-sk p98a2-arc-regions-measurable-finite-p
    (real-type)
  (forall (p-x p-y q-x q-y)
    (implies
     (p98a2-is-arc-p
      real-type p-x p-y q-x q-y)
     (let
         ((below
           (p98a2-below-arc-set
            real-type p-x p-y q-x q-y))
          (left
           (p98a2-left-of-arc-set
            real-type p-x p-y q-x q-y)))
       (and
        (p98a2-measurable-p real-type below)
        (p98a2-measurable-p real-type left)
        (p98a2-finite-measure-p real-type below)
        (p98a2-finite-measure-p real-type left))))))

(defun p98a2-lebesgue-plane-p (real-type)
  (and
   (p98a2-set-constructor-laws-p real-type)
   (p98a2-sigma-algebra-laws-p real-type)
   (p98a2-open-sets-measurable-p real-type)
   (p98a2-measure-values-p real-type)
   (p98a2-measure-extensional-p real-type)
   (equal
    (p98a2-measure
     real-type
     (p98a2-empty-set real-type))
    (p98a2-ennreal-zero real-type))
   (p98a2-countable-additivity-p real-type)
   (p98a2-translation-invariance-p real-type)
   (p98a2-measurable-p
    real-type
    (p98a2-unit-square-set real-type))
   (equal
    (p98a2-measure
     real-type
     (p98a2-unit-square-set real-type))
    (p98a2-ennreal-finite
     (p98a2-one real-type)))
   (p98a2-arc-regions-measurable-finite-p real-type)))

(defun p98a2-area-sum
    (real-type p-x p-y q-x q-y)
  (p98a2-add
   real-type
   (p98a2-measure-to-real
    real-type
    (p98a2-below-arc-set
     real-type p-x p-y q-x q-y))
   (p98a2-measure-to-real
    real-type
    (p98a2-left-of-arc-set
     real-type p-x p-y q-x q-y))))

;; The source's existential f : R -> R is expressed without restricting the
;; function space: a value factors through the arc-length code exactly when it
;; is constant on every fiber of that code.  Fiber constancy implies the
;; source existential by assigning the common value on attained codes and an
;; arbitrary real value elsewhere; the converse follows by substitution.

(defun-sk p98a2-area-sum-fiber-constant-p
    (real-type)
  (forall
   (p-x p-y q-x q-y
        r-x r-y s-x s-y)
   (implies
    (and
     (p98a2-is-arc-p
      real-type p-x p-y q-x q-y)
     (p98a2-is-arc-p
      real-type r-x r-y s-x s-y)
     (equal
      (p98a2-arc-length-code
       real-type p-x p-y q-x q-y)
      (p98a2-arc-length-code
       real-type r-x r-y s-x s-y)))
    (equal
     (p98a2-area-sum
      real-type p-x p-y q-x q-y)
     (p98a2-area-sum
      real-type r-x r-y s-x s-y)))))

(defun putnambench-putnam-1998-a2-statement
    (real-type)
  (implies
   (and
    (p98a2-real-field-p real-type)
    (p98a2-lebesgue-plane-p real-type))
   (p98a2-area-sum-fiber-constant-p real-type)))

(value-triple :itpeval-statement-checked)
:q
