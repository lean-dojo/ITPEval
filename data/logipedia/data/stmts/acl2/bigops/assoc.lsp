;; Statement-only formalization of Logipedia corpus artifact bigops.assoc,
;; catalog title "bigops.assoc": multiplication of natural numbers is
;; associative. This file contains no proof.

(in-package "ACL2")

(defun logipedia-bigops-assoc-statement (a b c)
  (implies
   (and (natp a)
        (natp b)
        (natp c))
   (equal (* a (* b c))
          (* (* a b) c))))

(value-triple :itpeval-statement-checked)
:q
