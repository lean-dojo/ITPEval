;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_eq_to_eqb_false, catalog title "nat.not_eq_to_eqb_false": for all
;; natural numbers n and m, if n and m are unequal, then their recursive
;; Boolean equality test returns false. This file contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the true and false constructors.
(defun logipedia-nat-not-eq-to-eqb-false-eqb (n m)
  (if (zp n)
      (if (zp m) t nil)
    (if (zp m)
        nil
      (logipedia-nat-not-eq-to-eqb-false-eqb (1- n) (1- m)))))

(defun-sk logipedia-nat-not-eq-to-eqb-false-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (implies
      (not (equal n m))
      (equal
       (logipedia-nat-not-eq-to-eqb-false-eqb n m)
       nil)))))

(value-triple :itpeval-statement-checked)
:q
