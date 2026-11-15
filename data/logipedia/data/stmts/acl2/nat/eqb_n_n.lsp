;; Statement-only formalization of Logipedia corpus artifact nat.eqb_n_n,
;; catalog title "nat.eqb_n_n": the recursive Boolean equality test of any
;; natural number with itself returns true. This file contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean equality, represented
;; on ACL2's natural numbers with T and NIL as the two Boolean values.
(defun logipedia-nat-eqb-n-n-eqb (n m)
  (if (zp n)
      (if (zp m) t nil)
    (if (zp m)
        nil
      (logipedia-nat-eqb-n-n-eqb (1- n) (1- m)))))

(defun-sk logipedia-nat-eqb-n-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-nat-eqb-n-n-eqb n n)
      t))))

(value-triple :itpeval-statement-checked)
:q
