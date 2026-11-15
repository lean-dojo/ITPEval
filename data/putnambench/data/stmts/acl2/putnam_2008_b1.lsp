;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_b1:
;; the maximum number of rational-coordinate points on a real plane circle
;; with a non-rational center is two. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive carrier containing every real number. Following the
;; repository's statement-only convention, the conservative interfaces below
;; present an arbitrary Dedekind-complete Archimedean ordered field with its
;; canonical rational embedding, hence the real field up to ordered-field
;; isomorphism. All carrier, algebraic, order, completeness, and embedding
;; conditions are explicit, and no real coordinate is replaced by a rational
;; coordinate, finite table, or external witness.

(defstub p08b1-real-p (real-type value) t)
(defstub p08b1-zero (real-type) t)
(defstub p08b1-one (real-type) t)
(defstub p08b1-add (real-type left right) t)
(defstub p08b1-mul (real-type left right) t)
(defstub p08b1-neg (real-type value) t)
(defstub p08b1-inv (real-type value) t)
(defstub p08b1-less (real-type left right) t)
(defstub p08b1-rational-embed (real-type rational) t)
(defstub p08b1-real-set-p (real-type set) t)
(defstub p08b1-real-set-member-p (real-type set value) t)
(defstub p08b1-supremum (real-type set) t)

(defun p08b1-leq (real-type left right)
  (not (p08b1-less real-type right left)))

(defun p08b1-sub (real-type left right)
  (p08b1-add real-type left (p08b1-neg real-type right)))

(defun p08b1-square (real-type value)
  (p08b1-mul real-type value value))

(defun-sk p08b1-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p08b1-real-p real-type x)
      (p08b1-real-p real-type y)
      (p08b1-real-p real-type z))
     (let* ((zero (p08b1-zero real-type))
            (one (p08b1-one real-type))
            (xy-add (p08b1-add real-type x y))
            (yz-add (p08b1-add real-type y z))
            (xy-mul (p08b1-mul real-type x y))
            (yz-mul (p08b1-mul real-type y z))
            (neg-x (p08b1-neg real-type x))
            (inv-x (p08b1-inv real-type x)))
       (and
        (p08b1-real-p real-type xy-add)
        (p08b1-real-p real-type xy-mul)
        (p08b1-real-p real-type neg-x)
        (p08b1-real-p real-type inv-x)
        (equal
         (p08b1-add real-type xy-add z)
         (p08b1-add real-type x yz-add))
        (equal xy-add (p08b1-add real-type y x))
        (equal (p08b1-add real-type x zero) x)
        (equal (p08b1-add real-type x neg-x) zero)
        (equal
         (p08b1-mul real-type xy-mul z)
         (p08b1-mul real-type x yz-mul))
        (equal xy-mul (p08b1-mul real-type y x))
        (equal (p08b1-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (p08b1-mul real-type x inv-x) one))
        (equal
         (p08b1-mul real-type x yz-add)
         (p08b1-add
          real-type
          (p08b1-mul real-type x y)
          (p08b1-mul real-type x z))))))))

(defun-sk p08b1-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p08b1-real-p real-type x)
      (p08b1-real-p real-type y)
      (p08b1-real-p real-type z))
     (let ((zero (p08b1-zero real-type)))
       (and
        (not (p08b1-less real-type x x))
        (or
         (p08b1-less real-type x y)
         (equal x y)
         (p08b1-less real-type y x))
        (implies
         (and
          (p08b1-less real-type x y)
          (p08b1-less real-type y z))
         (p08b1-less real-type x z))
        (implies
         (p08b1-less real-type x y)
         (p08b1-less
          real-type
          (p08b1-add real-type x z)
          (p08b1-add real-type y z)))
        (implies
         (and
          (p08b1-less real-type zero x)
          (p08b1-less real-type zero y))
         (p08b1-less
          real-type
          zero
          (p08b1-mul real-type x y))))))))

(defun-sk p08b1-rational-embedding-laws-p (real-type)
  (forall (q r)
    (implies
     (and (rationalp q) (rationalp r))
     (and
      (p08b1-real-p
       real-type
       (p08b1-rational-embed real-type q))
      (equal
       (p08b1-rational-embed real-type (+ q r))
       (p08b1-add
        real-type
        (p08b1-rational-embed real-type q)
        (p08b1-rational-embed real-type r)))
      (equal
       (p08b1-rational-embed real-type (* q r))
       (p08b1-mul
        real-type
        (p08b1-rational-embed real-type q)
        (p08b1-rational-embed real-type r)))
      (iff
       (< q r)
       (p08b1-less
        real-type
        (p08b1-rational-embed real-type q)
        (p08b1-rational-embed real-type r)))))))

(defun-sk p08b1-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (p08b1-real-set-member-p real-type set value)
     (p08b1-real-p real-type value))))

(defun-sk p08b1-real-set-nonempty-p (real-type set)
  (exists (value)
    (and
     (p08b1-real-p real-type value)
     (p08b1-real-set-member-p real-type set value))))

(defun-sk p08b1-upper-bound-p (real-type set upper)
  (forall (value)
    (implies
     (and
      (p08b1-real-p real-type value)
      (p08b1-real-set-member-p real-type set value))
     (p08b1-leq real-type value upper))))

(defun-sk p08b1-real-set-bounded-above-p (real-type set)
  (exists (upper)
    (and
     (p08b1-real-p real-type upper)
     (p08b1-upper-bound-p real-type set upper))))

(defun-sk p08b1-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (p08b1-real-p real-type upper)
      (p08b1-upper-bound-p real-type set upper))
     (p08b1-leq real-type supremum upper))))

(defun-sk p08b1-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (p08b1-real-set-p real-type set)
      (p08b1-valid-real-set-p real-type set)
      (p08b1-real-set-nonempty-p real-type set)
      (p08b1-real-set-bounded-above-p real-type set))
     (let ((supremum (p08b1-supremum real-type set)))
       (and
        (p08b1-real-p real-type supremum)
        (p08b1-upper-bound-p real-type set supremum)
        (p08b1-least-upper-bound-p
         real-type set supremum))))))

(defun-sk p08b1-rational-above-exists-p
    (real-type value)
  (exists (q)
    (and
     (rationalp q)
     (p08b1-less
      real-type
      value
      (p08b1-rational-embed real-type q)))))

(defun-sk p08b1-archimedean-p (real-type)
  (forall (value)
    (implies
     (p08b1-real-p real-type value)
     (p08b1-rational-above-exists-p real-type value))))

(defun p08b1-real-field-p (real-type)
  (let ((zero (p08b1-zero real-type))
        (one (p08b1-one real-type)))
    (and
     (p08b1-real-p real-type zero)
     (p08b1-real-p real-type one)
     (not (equal zero one))
     (equal
      (p08b1-rational-embed real-type 0)
      zero)
     (equal
      (p08b1-rational-embed real-type 1)
      one)
     (p08b1-less real-type zero one)
     (p08b1-field-laws-p real-type)
     (p08b1-order-laws-p real-type)
     (p08b1-rational-embedding-laws-p real-type)
     (p08b1-completeness-p real-type)
     (p08b1-archimedean-p real-type))))

;; A coordinate is rational exactly when it is the image of an ACL2 rational
;; under the canonical embedding. All quantifiers over circle centers, radii,
;; and point coordinates remain quantifiers over the full real carrier.

(defun-sk p08b1-rational-real-p (real-type value)
  (exists (q)
    (and
     (rationalp q)
     (equal
      value
      (p08b1-rational-embed real-type q)))))

(defun p08b1-rational-point-p (real-type x y)
  (and
   (p08b1-real-p real-type x)
   (p08b1-real-p real-type y)
   (p08b1-rational-real-p real-type x)
   (p08b1-rational-real-p real-type y)))

(defun p08b1-non-rational-center-p
    (real-type center-x center-y)
  (and
   (p08b1-real-p real-type center-x)
   (p08b1-real-p real-type center-y)
   (not
    (p08b1-rational-point-p
     real-type center-x center-y))))

(defun p08b1-point-equal-p (x1 y1 x2 y2)
  (and (equal x1 x2)
       (equal y1 y2)))

(defun p08b1-squared-distance
    (real-type center-x center-y point-x point-y)
  (p08b1-add
   real-type
   (p08b1-square
    real-type
    (p08b1-sub real-type point-x center-x))
   (p08b1-square
    real-type
    (p08b1-sub real-type point-y center-y))))

(defun p08b1-on-circle-p
    (real-type center-x center-y radius point-x point-y)
  (and
   (p08b1-real-p real-type center-x)
   (p08b1-real-p real-type center-y)
   (p08b1-real-p real-type radius)
   (p08b1-real-p real-type point-x)
   (p08b1-real-p real-type point-y)
   (not
    (p08b1-less
     real-type radius (p08b1-zero real-type)))
   (equal
    (p08b1-squared-distance
     real-type center-x center-y point-x point-y)
    (p08b1-square real-type radius))))

;; This universal clause says that the two displayed rational points exhaust
;; all rational points of the same circle.

(defun-sk p08b1-only-two-rational-points-p
    (real-type center-x center-y radius x1 y1 x2 y2)
  (forall (x y)
    (implies
     (and
      (p08b1-rational-point-p real-type x y)
      (p08b1-on-circle-p
       real-type center-x center-y radius x y))
     (or
      (p08b1-point-equal-p x y x1 y1)
      (p08b1-point-equal-p x y x2 y2)))))

;; Exact attainment of the value two: the center, radius, and the two points
;; are internal existential witnesses, and the exhaustion clause makes the
;; rational-point set have cardinality exactly two.

(defun-sk p08b1-two-attained-p (real-type)
  (exists (center-x center-y radius x1 y1 x2 y2)
    (and
     (p08b1-non-rational-center-p
      real-type center-x center-y)
     (p08b1-rational-point-p real-type x1 y1)
     (p08b1-rational-point-p real-type x2 y2)
     (not (p08b1-point-equal-p x1 y1 x2 y2))
     (p08b1-on-circle-p
      real-type center-x center-y radius x1 y1)
     (p08b1-on-circle-p
      real-type center-x center-y radius x2 y2)
     (p08b1-only-two-rational-points-p
      real-type
      center-x center-y radius
      x1 y1 x2 y2))))

;; Universal upper bound: on every real circle with a non-rational center,
;; any three rational points include a repeated pair. This is exactly the
;; assertion that such a circle has at most two rational points.

(defun-sk p08b1-at-most-two-on-every-circle-p (real-type)
  (forall
   (center-x center-y radius x1 y1 x2 y2 x3 y3)
   (implies
    (and
     (p08b1-non-rational-center-p
      real-type center-x center-y)
     (p08b1-rational-point-p real-type x1 y1)
     (p08b1-rational-point-p real-type x2 y2)
     (p08b1-rational-point-p real-type x3 y3)
     (p08b1-on-circle-p
      real-type center-x center-y radius x1 y1)
     (p08b1-on-circle-p
      real-type center-x center-y radius x2 y2)
     (p08b1-on-circle-p
      real-type center-x center-y radius x3 y3))
    (or
     (p08b1-point-equal-p x1 y1 x2 y2)
     (p08b1-point-equal-p x1 y1 x3 y3)
     (p08b1-point-equal-p x2 y2 x3 y3)))))

(defun p08b1-maximum-is-two-p (real-type)
  (and
   (p08b1-two-attained-p real-type)
   (p08b1-at-most-two-on-every-circle-p real-type)))

(defun putnambench-putnam-2008-b1-statement (real-type)
  (implies
   (p08b1-real-field-p real-type)
   (p08b1-maximum-is-two-p real-type)))

(value-triple :itpeval-statement-checked)

:q
