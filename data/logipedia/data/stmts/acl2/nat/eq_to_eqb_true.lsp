;; Statement-only formalization of Logipedia corpus artifact
;; nat.eq_to_eqb_true, catalog title "nat.eq_to_eqb_true": equality of two
;; natural numbers implies that their recursive Boolean equality test returns
;; true. This file contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the two Boolean values.
(defun logipedia-nat-eq-to-eqb-true-eqb (n m)
  (if (zp n)
      (if (zp m) t nil)
    (if (zp m)
        nil
      (logipedia-nat-eq-to-eqb-true-eqb (1- n) (1- m)))))

(defun-sk logipedia-nat-eq-to-eqb-true-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (equal n m))
     (equal
      (logipedia-nat-eq-to-eqb-true-eqb n m)
      t))))

(value-triple :itpeval-statement-checked)
:q
