;; Statement-only formalization of miniF2F corpus artifact
;; induction_ineq_nsqlefactn: for every natural number n at least 4, n
;; squared is at most n factorial. This file contains no proof.

(in-package "ACL2")

(defun induction-ineq-nsqlefactn-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (induction-ineq-nsqlefactn-factorial (- n 1)))))

(defun induction-ineq-nsqlefactn-statement (n)
  (implies (and (natp n)
                (<= 4 n))
           (<= (expt n 2)
               (induction-ineq-nsqlefactn-factorial n))))

(value-triple :itpeval-statement-checked)
:q
