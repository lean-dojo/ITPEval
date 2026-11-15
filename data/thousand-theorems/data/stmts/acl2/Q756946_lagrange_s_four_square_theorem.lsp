;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q756946, "Lagrange's four-square theorem": every
;; natural number is a sum of the squares of four natural numbers. This file
;; contains no proof.

(in-package "ACL2")

;; ACL2's untyped universe is restricted explicitly to the natural-number
;; parameter and four internal natural-number witnesses used by the source.

(defun-sk q756946-four-natural-squares-exist-p (n)
  (exists (a b c d)
    (and
     (natp a)
     (natp b)
     (natp c)
     (natp d)
     (equal
      (+ (* a a)
         (* b b)
         (* c c)
         (* d d))
      n))))

(defun thousand-theorems-q756946-lagrange-four-square-theorem-statement
    (n)
  (implies
   (natp n)
   (q756946-four-natural-squares-exist-p n)))

(value-triple :itpeval-statement-checked)
:q
