;; Statement-only formalization of Logipedia corpus artifact
;; permutation.transpose_i_j_i, catalog title
;; "permutation.transpose_i_j_i": swapping two natural numbers sends the
;; first selected number i to j. This file contains no proof.

(in-package "ACL2")

(defun logipedia-permutation-transpose-i-j-i-transpose (i j natural)
  (cond
   ((equal natural i) j)
   ((equal natural j) i)
   (t natural)))

(defun-sk logipedia-permutation-transpose-i-j-i-statement ()
  (forall (i j)
    (implies
     (and
      (natp i)
      (natp j))
     (equal
      (logipedia-permutation-transpose-i-j-i-transpose i j i)
      j))))

(value-triple :itpeval-statement-checked)
:q
