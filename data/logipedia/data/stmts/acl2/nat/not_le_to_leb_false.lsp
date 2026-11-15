;; Statement-only formalization of Logipedia corpus artifact
;; nat.not_le_to_leb_false, catalog title "nat.not_le_to_leb_false": for all
;; natural numbers n and m, if n is not less than or equal to m, then their
;; recursive Boolean less-than-or-equal test returns false. This file contains
;; no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean less-than-or-equal,
;; represented on ACL2's natural numbers with T and NIL as the Boolean values.
(defun logipedia-nat-not-le-to-leb-false-leb (n m)
  (if (zp n)
      t
    (if (zp m)
        nil
      (logipedia-nat-not-le-to-leb-false-leb (1- n) (1- m)))))

(defun-sk logipedia-nat-not-le-to-leb-false-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (implies
      (not (<= n m))
      (equal
       (logipedia-nat-not-le-to-leb-false-leb n m)
       nil)))))

(value-triple :itpeval-statement-checked)
:q
