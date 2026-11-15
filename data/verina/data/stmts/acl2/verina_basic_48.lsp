;; Statement-only formalization of VERINA corpus artifact verina_basic_48,
;; catalog title "isPerfectSquare": a deterministic natural-number search
;; returns true exactly when its input is the square of a natural number.
;; This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat input domain remains explicit in
;; the final correctness statement.

(defun verina-basic-48-is-perfect-square-precond (n)
  (declare (ignore n))
  t)

;; This is the source-local CHECK recursion. For positive FUEL it tests X^2
;; against N in the source order, then increments X and uses the predecessor
;; fuel. On natural arguments this is exactly the Lean computation.

(defun verina-basic-48-check (n x fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (if (> (* x x) n)
        nil
      (if (equal (* x x) n)
          t
        (verina-basic-48-check
         n
         (+ x 1)
         (- fuel 1))))))

;; The zero branch and the search starting at one with N units of fuel exactly
;; reproduce the executable source implementation.

(defun verina-basic-48-is-perfect-square (n)
  (if (equal n 0)
      t
    (verina-basic-48-check n 1 n)))

(defun verina-basic-48-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This preserves the source existential quantifier over the full Nat domain.

(defun-sk verina-basic-48-has-natural-square-root-p (n)
  (exists (i)
    (and
     (natp i)
     (equal (* i i) n))))

(defun verina-basic-48-is-perfect-square-postcond
    (n result)
  (and
   (natp n)
   (verina-basic-48-bool-p result)
   (iff
    result
    (verina-basic-48-has-natural-square-root-p n))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every natural input, applies the source True precondition, and connects
;; the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-48-is-perfect-square-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-48-is-perfect-square-precond n))
     (verina-basic-48-is-perfect-square-postcond
      n
      (verina-basic-48-is-perfect-square n)))))

(value-triple :itpeval-statement-checked)
:q
