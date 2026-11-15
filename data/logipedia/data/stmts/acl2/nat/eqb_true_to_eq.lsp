;; Statement-only formalization of Logipedia corpus artifact
;; nat.eqb_true_to_eq, catalog title "nat.eqb_true_to_eq": if the recursive
;; Boolean equality test on two natural numbers returns true, then the natural
;; numbers are equal. This file contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the true and false constructors.
(defun logipedia-nat-eqb-true-to-eq-eqb (n m)
  (if (zp n)
      (if (zp m) t nil)
    (if (zp m)
        nil
      (logipedia-nat-eqb-true-to-eq-eqb (1- n) (1- m)))))

(defun-sk logipedia-nat-eqb-true-to-eq-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (equal
       (logipedia-nat-eqb-true-to-eq-eqb n m)
       t))
     (equal n m))))

(value-triple :itpeval-statement-checked)
:q
