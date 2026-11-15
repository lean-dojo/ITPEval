;; Statement-only formalization of Logipedia corpus artifact
;; nat.transitive_le, catalog title "nat.transitive_le": less-than-or-equal
;; is transitive on the natural numbers. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-transitive-le-statement ()
  (forall (a b c)
    (implies
     (and (natp a)
          (natp b)
          (natp c))
     (implies
      (<= a b)
      (implies
       (<= b c)
       (<= a c))))))

(value-triple :itpeval-statement-checked)
:q
