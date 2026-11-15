;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_to_leb_true, catalog title "nat.le_to_leb_true": if one natural
;; number is less than or equal to another, their recursive Boolean
;; less-than-or-equal test returns true. This file contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean less-than-or-equal,
;; represented on ACL2's natural numbers with T and NIL as the Boolean values.
(defun logipedia-nat-le-to-leb-true-leb (n m)
  (if (zp n)
      t
    (if (zp m)
        nil
      (logipedia-nat-le-to-leb-true-leb (1- n) (1- m)))))

(defun-sk logipedia-nat-le-to-leb-true-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (<= n m))
     (equal
      (logipedia-nat-le-to-leb-true-leb n m)
      t))))

(value-triple :itpeval-statement-checked)
:q
