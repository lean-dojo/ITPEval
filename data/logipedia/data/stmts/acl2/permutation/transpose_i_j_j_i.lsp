;; Statement-only formalization of Logipedia corpus artifact
;; permutation.transpose_i_j_j_i, catalog title
;; "permutation.transpose_i_j_j_i": swapping two natural numbers is symmetric
;; in the selected numbers for every natural input. This file contains no proof.

(in-package "ACL2")

(defun logipedia-permutation-transpose-i-j-j-i-transpose (i j natural)
  (if (equal natural i)
      j
    (if (equal natural j)
        i
      natural)))

(defun-sk logipedia-permutation-transpose-i-j-j-i-statement ()
  (forall (i j natural)
    (implies
     (and
      (natp i)
      (natp j)
      (natp natural))
     (equal
      (logipedia-permutation-transpose-i-j-j-i-transpose
       i j natural)
      (logipedia-permutation-transpose-i-j-j-i-transpose
       j i natural)))))

(value-triple :itpeval-statement-checked)
:q
