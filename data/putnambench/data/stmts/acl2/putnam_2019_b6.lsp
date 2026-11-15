;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_b6:
;; the existence of a perfect independent dominating set in the integer
;; lattice Z^n is classified by the positive dimensions. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A point of Z^n is an exact length-N list of integers. For a radius R, a
;; finite alist labels every point of the box [-R-1,R+1]^n by T or NIL, and
;; the source's two conditions are imposed on every point of [-R,R]^n.
;;
;; This finite-box formulation is bidirectionally equivalent to the source
;; existential quantifier over arbitrary subsets of Z^n. Restricting a global
;; set gives every finite labeling. Conversely, the constraints have Boolean
;; variables and finite neighborhoods, so satisfiability on every finite box
;; gives a global labeling by propositional compactness (equivalently,
;; Konig's lemma applied to the finitely branching tree of finite labelings).
;; The one-step-larger box contains every neighbor used by an inner constraint.

(defun putnam-2019-b6-point-p (point n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (equal point nil)
    (and
     (consp point)
     (integerp (car point))
     (putnam-2019-b6-point-p
      (cdr point) (- n 1)))))

(defun putnam-2019-b6-coordinates-bounded-p
    (point radius)
  (if (consp point)
      (and
       (<= (abs (car point)) radius)
       (putnam-2019-b6-coordinates-bounded-p
        (cdr point) radius))
    (equal point nil)))

(defun putnam-2019-b6-in-box-p (point n radius)
  (and
   (natp n)
   (natp radius)
   (putnam-2019-b6-point-p point n)
   (putnam-2019-b6-coordinates-bounded-p
    point radius)))

(defun putnam-2019-b6-assignment-entry
    (point assignment)
  (assoc-equal point assignment))

(defun putnam-2019-b6-assignment-member-p
    (point assignment)
  (let ((entry
         (putnam-2019-b6-assignment-entry
          point assignment)))
    (and (consp entry)
         (cdr entry))))

(defun-sk putnam-2019-b6-assignment-covers-box-p
    (n radius assignment)
  (forall
   (point)
   (implies
    (putnam-2019-b6-in-box-p point n radius)
    (let ((entry
           (putnam-2019-b6-assignment-entry
            point assignment)))
      (and
       (consp entry)
       (booleanp (cdr entry)))))))

;; For a valid point these are exactly the 2N points obtained by changing one
;; coordinate by plus or minus one, with no duplicates.

(defun putnam-2019-b6-neighbor-count-aux
    (assignment point index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((coordinate (nth index point))
           (plus-neighbor
            (update-nth index (+ coordinate 1) point))
           (minus-neighbor
            (update-nth index (- coordinate 1) point)))
      (+
       (if
           (putnam-2019-b6-assignment-member-p
            plus-neighbor assignment)
           1
         0)
       (if
           (putnam-2019-b6-assignment-member-p
            minus-neighbor assignment)
           1
         0)
       (putnam-2019-b6-neighbor-count-aux
        assignment point (+ index 1)
        (- remaining 1))))))

(defun putnam-2019-b6-neighbor-count
    (assignment point n)
  (putnam-2019-b6-neighbor-count-aux
   assignment point 0 n))

(defun putnam-2019-b6-point-condition-p
    (assignment point n)
  (let ((neighbor-count
         (putnam-2019-b6-neighbor-count
          assignment point n)))
    (if
        (putnam-2019-b6-assignment-member-p
         point assignment)
        (equal neighbor-count 0)
      (equal neighbor-count 1))))

(defun-sk putnam-2019-b6-inner-conditions-p
    (n radius assignment)
  (forall
   (point)
   (implies
    (putnam-2019-b6-in-box-p point n radius)
    (putnam-2019-b6-point-condition-p
     assignment point n))))

(defun putnam-2019-b6-valid-local-assignment-p
    (n radius assignment)
  (and
   (natp n)
   (natp radius)
   (true-listp assignment)
   (alistp assignment)
   (putnam-2019-b6-assignment-covers-box-p
    n (+ radius 1) assignment)
   (putnam-2019-b6-inner-conditions-p
    n radius assignment)))

(defun-sk putnam-2019-b6-local-assignment-exists-p
    (n radius)
  (exists
   (assignment)
   (putnam-2019-b6-valid-local-assignment-p
    n radius assignment)))

(defun-sk putnam-2019-b6-perfect-set-exists-p (n)
  (forall
   (radius)
   (implies
    (natp radius)
    (putnam-2019-b6-local-assignment-exists-p
     n radius))))

;; The published solution set is Set.Ici 1. ACL2 universally closes N, so
;; this pointwise equivalence is equality with the set of positive dimensions.

(defun putnambench-putnam-2019-b6-statement (n)
  (implies
   (natp n)
   (iff
    (and
     (<= 1 n)
     (putnam-2019-b6-perfect-set-exists-p n))
    (<= 1 n))))

(value-triple :itpeval-statement-checked)
:q
