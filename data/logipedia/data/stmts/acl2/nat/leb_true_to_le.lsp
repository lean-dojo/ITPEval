;; Statement-only formalization of Logipedia corpus artifact
;; nat.leb_true_to_le, catalog title "nat.leb_true_to_le": if the recursive
;; Boolean less-than-or-equal test on two natural numbers returns true, then
;; the first natural number is less than or equal to the second. This file
;; contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean less-than-or-equal,
;; represented on ACL2's natural numbers with T and NIL as the Boolean values.
(defun logipedia-nat-leb-true-to-le-leb (n m)
  (if (zp n)
      t
    (if (zp m)
        nil
      (logipedia-nat-leb-true-to-le-leb (1- n) (1- m)))))

(defun-sk logipedia-nat-leb-true-to-le-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (equal
       (logipedia-nat-leb-true-to-le-leb n m)
       t))
     (<= n m))))

(value-triple :itpeval-statement-checked)
:q
