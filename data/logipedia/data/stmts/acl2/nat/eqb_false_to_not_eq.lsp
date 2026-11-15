;; Statement-only formalization of Logipedia corpus artifact
;; nat.eqb_false_to_not_eq, catalog title "nat.eqb_false_to_not_eq": if the
;; recursive Boolean equality test on two natural numbers returns false, then
;; the natural numbers are unequal. This file contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the true and false constructors.
(defun logipedia-nat-eqb-false-to-not-eq-eqb (n m)
  (if (zp n)
      (if (zp m) t nil)
    (if (zp m)
        nil
      (logipedia-nat-eqb-false-to-not-eq-eqb (1- n) (1- m)))))

(defun-sk logipedia-nat-eqb-false-to-not-eq-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (equal
       (logipedia-nat-eqb-false-to-not-eq-eqb n m)
       nil))
     (not (equal n m)))))

(value-triple :itpeval-statement-checked)
:q
