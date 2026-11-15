;; Statement-only formalization of Logipedia corpus artifact bool.andb_true_r,
;; catalog title "bool.andb_true_r": for Boolean values b1 and b2, if their
;; Boolean conjunction is true, then b2 is true. This file contains no proof.

(in-package "ACL2")

(defun logipedia-bool-andb (b1 b2)
  (if (equal b1 t)
      b2
    nil))

(defun logipedia-bool-andb-true-r-statement (b1 b2)
  (implies
   (and (booleanp b1)
        (booleanp b2))
   (implies
    (equal (logipedia-bool-andb b1 b2) t)
    (equal b2 t))))

(value-triple :itpeval-statement-checked)
:q
