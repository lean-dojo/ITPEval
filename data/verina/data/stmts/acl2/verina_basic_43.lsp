;; Statement-only formalization of VERINA corpus artifact verina_basic_43,
;; catalog title "sumOfFourthPowerOfOddNumbers": a deterministic natural-number
;; recursion sums the fourth powers of the first n odd numbers, with correctness
;; stated by the source closed formula. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat input domain remains explicit in
;; the final correctness statement.

(defun verina-basic-43-sum-fourth-odd-precond (n)
  (declare (ignore n))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. For positive N, PREDECESSOR is the source pattern variable in the
;; N = predecessor + 1 branch, so NEXT-ODD is exactly 2 * predecessor + 1.

(defun verina-basic-43-sum-fourth-odd (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let* ((predecessor (- n 1))
           (previous
            (verina-basic-43-sum-fourth-odd predecessor))
           (next-odd (+ (* 2 predecessor) 1)))
      (+ previous (expt next-odd 4)))))

;; Lean Nat subtraction truncates at zero. The source polynomial contains two
;; left-associated Nat subtractions, which are represented by nested calls.

(defun verina-basic-43-nat-sub (left right)
  (nfix (- left right)))

(defun verina-basic-43-sum-fourth-odd-postcond (n result)
  (let* ((after-square-term
          (verina-basic-43-nat-sub
           (+ 7 (* 24 (expt n 3)))
           (* 12 (expt n 2))))
         (closed-form-factor
          (verina-basic-43-nat-sub
           after-square-term
           (* 14 n))))
    (and
     (natp n)
     (natp result)
     (equal
      (* 15 result)
      (* (* n (+ (* 2 n) 1))
         closed-form-factor)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Nat input domain, applies the True precondition, and
;; connects the complete postcondition to the exact executable recursion.

(defun-sk
    verina-basic-43-sum-fourth-odd-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-43-sum-fourth-odd-precond n))
     (verina-basic-43-sum-fourth-odd-postcond
      n
      (verina-basic-43-sum-fourth-odd n)))))

(value-triple :itpeval-statement-checked)
:q
