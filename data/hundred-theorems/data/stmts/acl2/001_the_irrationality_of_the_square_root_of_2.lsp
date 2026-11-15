;; Statement-only formalization of hundred-theorems artifact 001, "The
;; Irrationality of the Square Root of 2": no natural numbers p and nonzero q
;; satisfy p^2 = 2 * q^2, equivalently the square root of 2 is not rational.
;; This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-001-irrational-sqrt-two-statement (p q)
  (implies (and (natp p)
                (natp q)
                (not (equal q 0)))
           (not (equal (* p p)
                       (* 2 (* q q))))))

(value-triple :itpeval-statement-checked)
:q
