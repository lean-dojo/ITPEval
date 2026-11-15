;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_b5:
;; the number of two weakly increasing positive integer sequences with a
;; common upper bound agrees on positive integers with a rational polynomial
;; having nonnegative coefficients. This file contains no proof.

(in-package "ACL2")

;; For positive Q, PUTNAM-2024-B5-QUALIFYING-SEQUENCE-COUNT(Q,Z) counts the
;; functions Fin Q -> Nat that are monotone, start at least at 1, and end at
;; most at Z. Such functions are in bijection with weakly increasing lists of
;; length Q over {1,...,Z}. Partitioning these lists according to whether the
;; last entry is Z gives the recurrence below, so no finite-table restriction
;; is placed on either the source function space or its natural-number range.
;;
;; The source hypotheses uniquely determine ISQUALIFYINGSEQ and F. Eliminating
;; them definitionally yields PUTNAM-2024-B5-COUNT(K,M,N): partition the finite
;; set of triples by Z and multiply the independent X- and Y-sequence counts.
;; Conversely, the predicates and function defined by these same conditions
;; instantiate the source hypotheses, making this direct counting statement
;; bidirectionally equivalent to the Lean statement.
;;
;; A rational polynomial is represented by its finite coefficient list in
;; ascending degree order; omitted coefficients are zero. DEFUN-SK keeps both
;; the universal quantifier over every positive natural N and the existential
;; polynomial witness internal to the statement.

(defun putnam-2024-b5-qualifying-sequence-count (q z)
  (declare (xargs :measure (+ (nfix q) (nfix z))))
  (if (zp q)
      1
    (if (zp z)
        0
      (+
       (putnam-2024-b5-qualifying-sequence-count
        q (- z 1))
       (putnam-2024-b5-qualifying-sequence-count
        (- q 1) z)))))

(defun putnam-2024-b5-count (k m n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+
     (putnam-2024-b5-count k m (- n 1))
     (*
      (putnam-2024-b5-qualifying-sequence-count k n)
      (putnam-2024-b5-qualifying-sequence-count m n)))))

(defun putnam-2024-b5-nonnegative-rational-coefficients-p
    (coefficients)
  (if (consp coefficients)
      (and
       (rationalp (car coefficients))
       (<= 0 (car coefficients))
       (putnam-2024-b5-nonnegative-rational-coefficients-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2024-b5-polynomial-eval (coefficients x)
  (if (consp coefficients)
      (+
       (car coefficients)
       (* x
          (putnam-2024-b5-polynomial-eval
           (cdr coefficients) x)))
    0))

(defun-sk putnam-2024-b5-polynomial-agrees-p
    (k m coefficients)
  (forall (n)
    (implies
     (and
      (natp n)
      (< 0 n))
     (equal
      (putnam-2024-b5-count k m n)
      (putnam-2024-b5-polynomial-eval
       coefficients n)))))

(defun putnam-2024-b5-polynomial-witness-p
    (k m coefficients)
  (and
   (true-listp coefficients)
   (putnam-2024-b5-nonnegative-rational-coefficients-p
    coefficients)
   (putnam-2024-b5-polynomial-agrees-p
    k m coefficients)))

(defun-sk putnam-2024-b5-polynomial-exists-p (k m)
  (exists (coefficients)
    (putnam-2024-b5-polynomial-witness-p
     k m coefficients)))

(defun putnambench-putnam-2024-b5-statement (k m)
  (implies
   (and
    (natp k)
    (< 0 k)
    (natp m)
    (< 0 m))
   (putnam-2024-b5-polynomial-exists-p k m)))

(value-triple :itpeval-statement-checked)
:q
