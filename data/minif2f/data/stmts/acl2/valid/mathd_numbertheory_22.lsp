;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_22: a natural digit b for which 10*b+6 is a perfect
;; square must be 3 or 1. This file contains no proof.

(in-package "ACL2")

;; A natural square root of n cannot exceed n. Therefore this search from n
;; down to 0 is equivalent to the source existential over all natural roots.
(defun mathd-numbertheory-22-square-witness-through-p (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (natp candidate)
      (or (equal (* candidate candidate) n)
          (and (not (zp candidate))
               (mathd-numbertheory-22-square-witness-through-p
                n (- candidate 1))))
    nil))

(defun mathd-numbertheory-22-statement (b)
  (let ((n (+ (* 10 b) 6)))
    (implies
     (and (natp b)
          (< b 10)
          (mathd-numbertheory-22-square-witness-through-p n n))
     (or (equal b 3)
         (equal b 1)))))

(value-triple :itpeval-statement-checked)
:q
