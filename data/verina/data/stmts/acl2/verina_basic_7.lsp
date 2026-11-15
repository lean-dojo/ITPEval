;; Statement-only formalization of VERINA corpus artifact verina_basic_7,
;; catalog title "sumOfSquaresOfFirstNOddNumbers": a deterministic
;; natural-number recursion sums the squares of the first n odd numbers and
;; satisfies the source closed formula. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat input domain remains explicit in
;; the final correctness proposition.

(defun verina-basic-7-sum-of-squares-precond (n)
  (declare (ignore n))
  t)

;; This is the source-local LOOP recursion. For positive K, ODD is the source
;; value 2 * K - 1, the accumulator gains ODD squared, and K decreases by one.

(defun verina-basic-7-sum-of-squares-loop (k sum)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      sum
    (let ((odd (- (* 2 k) 1)))
      (verina-basic-7-sum-of-squares-loop
       (- k 1)
       (+ sum (* odd odd))))))

;; The proof-valued True precondition argument has no computational effect and
;; is erased. The initial call preserves the source loop n 0 exactly.

(defun verina-basic-7-sum-of-squares (n)
  (verina-basic-7-sum-of-squares-loop n 0))

;; Lean Nat subtraction truncates at zero.

(defun verina-basic-7-nat-sub (left right)
  (nfix (- left right)))

;; On natural inputs, ACL2 FLOOR by positive divisor three is Lean Nat
;; division. The multiplication and truncated subtraction preserve the source
;; expression n * (2 * n - 1) * (2 * n + 1) / 3.

(defun verina-basic-7-closed-form (n)
  (floor
   (* n
      (verina-basic-7-nat-sub (* 2 n) 1)
      (+ (* 2 n) 1))
   3))

;; This is the complete two-sided source postcondition.

(defun verina-basic-7-sum-of-squares-postcond (n result)
  (and
   (natp n)
   (natp result)
   (let ((expected (verina-basic-7-closed-form n)))
     (and
      (equal
       (verina-basic-7-nat-sub result expected)
       0)
      (equal
       (verina-basic-7-nat-sub expected result)
       0)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Nat input domain, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-7-sum-of-squares-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (natp n)
      (verina-basic-7-sum-of-squares-precond n))
     (verina-basic-7-sum-of-squares-postcond
      n
      (verina-basic-7-sum-of-squares n)))))

(value-triple :itpeval-statement-checked)
:q
