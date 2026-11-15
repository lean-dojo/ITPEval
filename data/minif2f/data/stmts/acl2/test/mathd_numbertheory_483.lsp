;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_483: every natural-number sequence with a(1) = a(2) = 1
;; and a(n + 2) = a(n + 1) + a(n) has remainder 3 modulo 4 at index 100.
;; This file contains no proof.
;;
;; The initial values and recurrence uniquely determine the sequence on the
;; naturals and force a(0) = 0. Thus the recursive function below is
;; bidirectionally equivalent to quantifying over natural-number functions
;; satisfying the source hypotheses.

(in-package "ACL2")

(defun mathd-numbertheory-483-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (natp n)
      (if (zp n)
          0
        (if (equal n 1)
            1
          (+ (mathd-numbertheory-483-sequence (- n 1))
             (mathd-numbertheory-483-sequence (- n 2)))))
    0))

(defun mathd-numbertheory-483-statement ()
  (equal (mod (mathd-numbertheory-483-sequence 100) 4)
         3))

(value-triple :itpeval-statement-checked)
:q
