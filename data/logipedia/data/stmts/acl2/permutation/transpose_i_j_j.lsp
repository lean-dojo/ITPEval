;; Statement-only formalization of Logipedia corpus artifact
;; permutation.transpose_i_j_j, catalog title
;; "permutation.transpose_i_j_j": swapping two natural numbers sends the
;; second selected number j to i. This file contains no proof.

(in-package "ACL2")

(defun logipedia-permutation-transpose-i-j-j-transpose (i j natural)
  (cond
   ((equal natural i) j)
   ((equal natural j) i)
   (t natural)))

(defun-sk logipedia-permutation-transpose-i-j-j-statement ()
  (forall (i j)
    (implies
     (and
      (natp i)
      (natp j))
     (equal
      (logipedia-permutation-transpose-i-j-j-transpose i j j)
      i))))

(value-triple :itpeval-statement-checked)
:q
