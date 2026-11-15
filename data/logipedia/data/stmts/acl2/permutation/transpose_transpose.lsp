;; Statement-only formalization of Logipedia corpus artifact
;; permutation.transpose_transpose, catalog title
;; "permutation.transpose_transpose": swapping the same two natural numbers
;; twice returns every natural input unchanged. This file contains no proof.

(in-package "ACL2")

(defun logipedia-permutation-transpose-transpose-transpose
    (i j natural)
  (cond
   ((equal natural i) j)
   ((equal natural j) i)
   (t natural)))

(defun-sk logipedia-permutation-transpose-transpose-statement ()
  (forall (i j natural)
    (implies
     (and
      (natp i)
      (natp j)
      (natp natural))
     (equal
      (logipedia-permutation-transpose-transpose-transpose
       i j
       (logipedia-permutation-transpose-transpose-transpose
        i j natural))
      natural))))

(value-triple :itpeval-statement-checked)
:q
