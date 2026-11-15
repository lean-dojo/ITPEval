;; Statement-only formalization of Logipedia corpus artifact
;; nat.transitive_lt, catalog title "nat.transitive_lt": strict less-than is
;; transitive on the natural numbers. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-transitive-lt-statement ()
  (forall (a b c)
    (implies
     (and (natp a)
          (natp b)
          (natp c))
     (implies
      (< a b)
      (implies
       (< b c)
       (< a c))))))

(value-triple :itpeval-statement-checked)
:q
