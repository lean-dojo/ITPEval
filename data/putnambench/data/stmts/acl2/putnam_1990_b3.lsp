;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_b3:
;; a sufficiently large set of 2 by 2 natural-number matrices whose entries
;; are integer squares at most 200 contains two distinct commuting matrices.
;; This file contains no proof.

(in-package "ACL2")

;; Each admissible entry belongs to a finite set, so every source set S is
;; finite. A duplicate-free list is therefore an extensional enumeration of S,
;; and every such list determines a source set with the same cardinality.
;; The downward search is equivalent to the source existential square witness:
;; for natural X, any integer M satisfying M^2 = X yields the natural witness
;; |M| <= X, while every natural witness is also an integer witness.

(defun putnam-1990-b3-square-witness-down-p (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (equal x 0)
    (or
     (equal x (* candidate candidate))
     (putnam-1990-b3-square-witness-down-p
      x (- candidate 1)))))

(defun putnam-1990-b3-entry-p (x)
  (and
   (natp x)
   (<= x 200)
   (putnam-1990-b3-square-witness-down-p x x)))

;; A matrix is stored in row-major order as (a_00 a_01 a_10 a_11).

(defun putnam-1990-b3-matrix-p (matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) 4)
   (putnam-1990-b3-entry-p (nth 0 matrix))
   (putnam-1990-b3-entry-p (nth 1 matrix))
   (putnam-1990-b3-entry-p (nth 2 matrix))
   (putnam-1990-b3-entry-p (nth 3 matrix))))

(defun putnam-1990-b3-matrix-set-p (matrices)
  (if (consp matrices)
      (and
       (putnam-1990-b3-matrix-p (car matrices))
       (not (member-equal (car matrices) (cdr matrices)))
       (putnam-1990-b3-matrix-set-p (cdr matrices)))
    (equal matrices nil)))

(defun putnam-1990-b3-matrix-multiply (left right)
  (let ((a (nth 0 left))
        (b (nth 1 left))
        (c (nth 2 left))
        (d (nth 3 left))
        (e (nth 0 right))
        (f (nth 1 right))
        (g (nth 2 right))
        (h (nth 3 right)))
    (list
     (+ (* a e) (* b g))
     (+ (* a f) (* b h))
     (+ (* c e) (* d g))
     (+ (* c f) (* d h)))))

(defun putnam-1990-b3-commute-p (left right)
  (equal
   (putnam-1990-b3-matrix-multiply left right)
   (putnam-1990-b3-matrix-multiply right left)))

;; These two searches are exactly the nested existential quantifiers over
;; distinct members A and B of S; no witnesses are external parameters.

(defun putnam-1990-b3-commutes-with-some-p (matrix matrices)
  (if (consp matrices)
      (or
       (and
        (not (equal matrix (car matrices)))
        (putnam-1990-b3-commute-p matrix (car matrices)))
       (putnam-1990-b3-commutes-with-some-p
        matrix (cdr matrices)))
    nil))

(defun putnam-1990-b3-commuting-pair-exists-p (matrices)
  (if (consp matrices)
      (or
       (putnam-1990-b3-commutes-with-some-p
        (car matrices) (cdr matrices))
       (putnam-1990-b3-commuting-pair-exists-p
        (cdr matrices)))
    nil))

(defun putnambench-putnam-1990-b3-statement (matrices)
  (implies
   (and
    (putnam-1990-b3-matrix-set-p matrices)
    (< 50387 (len matrices)))
   (putnam-1990-b3-commuting-pair-exists-p matrices)))

(value-triple :itpeval-statement-checked)
:q
