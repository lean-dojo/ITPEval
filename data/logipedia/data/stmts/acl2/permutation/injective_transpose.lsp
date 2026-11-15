;; Statement-only formalization of Logipedia corpus artifact
;; permutation.injective_transpose, catalog title
;; "permutation.injective_transpose": swapping any two natural numbers defines
;; an injective function on the natural numbers. This file contains no proof.

(in-package "ACL2")

(defun logipedia-permutation-transpose (i j n)
  (cond
   ((equal n i) j)
   ((equal n j) i)
   (t n)))

(defun-sk logipedia-permutation-injective-transpose-statement ()
  (forall (i j x y)
    (implies
     (and
      (natp i)
      (natp j)
      (natp x)
      (natp y)
      (equal (logipedia-permutation-transpose i j x)
             (logipedia-permutation-transpose i j y)))
     (equal x y))))

(value-triple :itpeval-statement-checked)
:q
