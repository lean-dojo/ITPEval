;; Statement-only formalization of Logipedia corpus artifact nat.assoc_plus1,
;; catalog title "nat.assoc_plus1": for all natural numbers a, b, and c,
;; c + (b + a) equals (b + c) + a. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-assoc-plus1-statement (a b c)
  (implies
   (and (natp a)
        (natp b)
        (natp c))
   (equal (+ c (+ b a))
          (+ (+ b c) a))))

(value-triple :itpeval-statement-checked)
:q
