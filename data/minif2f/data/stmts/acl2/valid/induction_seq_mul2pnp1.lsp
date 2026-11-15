;; Statement-only formalization of miniF2F corpus artifact
;; induction_seq_mul2pnp1: every natural-number sequence with u(0) = 0 and
;; u(n+1) = 2*u(n) + (n+1) has u(n) = 2^(n+1) - (n+2), where subtraction
;; is natural subtraction. This file contains no proof.
;;
;; The initial value and recurrence uniquely determine the sequence on the
;; naturals. Every satisfying source sequence therefore agrees with the
;; recursive function below, and conversely this function is natural-valued
;; and satisfies those hypotheses. Thus eliminating the function parameter
;; is bidirectionally equivalent to the universally quantified source
;; implication and does not replace the sequence by a finite table.

(in-package "ACL2")

(defun induction-seq-mul2pnp1-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      0
    (if (zp n)
        0
      (+ (* 2
            (induction-seq-mul2pnp1-sequence (- n 1)))
         n))))

(defun induction-seq-mul2pnp1-statement (n)
  (implies
   (natp n)
   (equal
    (induction-seq-mul2pnp1-sequence n)
    (nfix (- (expt 2 (+ n 1))
             (+ n 2))))))

(value-triple :itpeval-statement-checked)
:q
