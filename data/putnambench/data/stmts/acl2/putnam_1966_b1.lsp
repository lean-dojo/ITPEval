;; Statement-only formalization of PutnamBench artifact putnam_1966_b1:
;; a convex polygon contained in the unit square has sum of squared side
;; lengths at most four. This file contains no proof.

(in-package "ACL2")

;; A length-n list is exactly a function on the cyclic finite type ZMod n,
;; with the final-to-first edge implementing addition modulo n.
;;
;; Under the stated noncollinearity assumption, a segment joining consecutive
;; vertices is disjoint from the interior of their convex hull exactly when
;; every vertex lies in one of the two closed half-planes bounded by that
;; edge. The supporting-edge predicates below express this equivalence using
;; orientation signs, without external convex-hull or interior witnesses.
;;
;; ACL2's exact ordered arithmetic is rational. This predicate is
;; bidirectionally equivalent to the source universal statement over real
;; coordinates. A real counterexample has a strict conclusion violation,
;; every three vertices have nonzero orientation, and every non-edge vertex
;; has a strict supporting-edge orientation sign. These finitely many strict
;; conditions persist under a sufficiently small perturbation. Rational
;; points are dense in the unit square, including relative to its boundary,
;; so such a perturbation yields a rational counterexample with the same
;; cyclic order. Conversely, every rational counterexample is a real one.

(defun putnam-1966-b1-point-p (point)
  (and (consp point)
       (rationalp (car point))
       (rationalp (cdr point))))

(defun putnam-1966-b1-point-list-p (points)
  (if (consp points)
      (and (putnam-1966-b1-point-p (car points))
           (putnam-1966-b1-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1966-b1-points-in-unit-square-p (points)
  (if (consp points)
      (let ((point (car points)))
        (and (<= 0 (car point))
             (<= (car point) 1)
             (<= 0 (cdr point))
             (<= (cdr point) 1)
             (putnam-1966-b1-points-in-unit-square-p (cdr points))))
    t))

(defun putnam-1966-b1-square (x)
  (* x x))

(defun putnam-1966-b1-orientation (a b c)
  (- (* (- (car b) (car a))
        (- (cdr c) (cdr a)))
     (* (- (cdr b) (cdr a))
        (- (car c) (car a)))))

(defun putnam-1966-b1-distance-squared (a b)
  (+ (putnam-1966-b1-square (- (car b) (car a)))
     (putnam-1966-b1-square (- (cdr b) (cdr a)))))

(defun putnam-1966-b1-noncollinear-with-pair-p (a b remaining)
  (if (consp remaining)
      (and
       (not (equal (putnam-1966-b1-orientation a b (car remaining))
                   0))
       (putnam-1966-b1-noncollinear-with-pair-p
        a b (cdr remaining)))
    t))

(defun putnam-1966-b1-noncollinear-with-first-p (a remaining)
  (if (consp remaining)
      (and
       (putnam-1966-b1-noncollinear-with-pair-p
        a (car remaining) (cdr remaining))
       (putnam-1966-b1-noncollinear-with-first-p a (cdr remaining)))
    t))

(defun putnam-1966-b1-all-triples-noncollinear-p (points)
  (if (consp points)
      (and
       (putnam-1966-b1-noncollinear-with-first-p
        (car points) (cdr points))
       (putnam-1966-b1-all-triples-noncollinear-p (cdr points)))
    t))

(defun putnam-1966-b1-all-on-nonnegative-side-p (a b points)
  (if (consp points)
      (and
       (<= 0 (putnam-1966-b1-orientation a b (car points)))
       (putnam-1966-b1-all-on-nonnegative-side-p a b (cdr points)))
    t))

(defun putnam-1966-b1-all-on-nonpositive-side-p (a b points)
  (if (consp points)
      (and
       (<= (putnam-1966-b1-orientation a b (car points)) 0)
       (putnam-1966-b1-all-on-nonpositive-side-p a b (cdr points)))
    t))

(defun putnam-1966-b1-supporting-edge-p (a b points)
  (or (putnam-1966-b1-all-on-nonnegative-side-p a b points)
      (putnam-1966-b1-all-on-nonpositive-side-p a b points)))

(defun putnam-1966-b1-all-cyclic-edges-supporting-aux
    (remaining first all-points)
  (if (consp remaining)
      (if (consp (cdr remaining))
          (and
           (putnam-1966-b1-supporting-edge-p
            (car remaining) (cadr remaining) all-points)
           (putnam-1966-b1-all-cyclic-edges-supporting-aux
            (cdr remaining) first all-points))
        (putnam-1966-b1-supporting-edge-p
         (car remaining) first all-points))
    t))

(defun putnam-1966-b1-all-cyclic-edges-supporting-p (points)
  (if (consp points)
      (putnam-1966-b1-all-cyclic-edges-supporting-aux
       points (car points) points)
    t))

(defun putnam-1966-b1-cyclic-squared-length-sum-aux
    (remaining first)
  (if (consp remaining)
      (if (consp (cdr remaining))
          (+ (putnam-1966-b1-distance-squared
              (car remaining) (cadr remaining))
             (putnam-1966-b1-cyclic-squared-length-sum-aux
              (cdr remaining) first))
        (putnam-1966-b1-distance-squared (car remaining) first))
    0))

(defun putnam-1966-b1-cyclic-squared-length-sum (points)
  (if (consp points)
      (putnam-1966-b1-cyclic-squared-length-sum-aux
       points (car points))
    0))

(defun putnambench-putnam-1966-b1-statement (n points)
  (implies
   (and
    (natp n)
    (<= 3 n)
    (true-listp points)
    (equal (len points) n)
    (putnam-1966-b1-point-list-p points)
    (putnam-1966-b1-points-in-unit-square-p points)
    (putnam-1966-b1-all-triples-noncollinear-p points)
    (putnam-1966-b1-all-cyclic-edges-supporting-p points))
   (<= (putnam-1966-b1-cyclic-squared-length-sum points) 4)))

(value-triple :itpeval-statement-checked)
:q
