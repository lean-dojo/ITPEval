;; Statement-only formalization of Logipedia corpus artifact nat.le_plus_b,
;; catalog title "nat.le_plus_b": if n plus a natural number b is at most m,
;; then n is at most m. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-plus-b-statement (b n m)
  (implies
   (and (natp b)
        (natp n)
        (natp m)
        (<= (+ n b) m))
   (<= n m)))

(value-triple :itpeval-statement-checked)
:q
