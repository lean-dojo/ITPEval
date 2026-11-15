;; Statement-only formalization of Logipedia corpus artifact
;; nat.associative_plus: associativity of addition on the natural numbers.
;; This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-associative-plus-statement (x y z)
  (implies
   (and (natp x)
        (natp y)
        (natp z))
   (equal (+ (+ x y) z)
          (+ x (+ y z)))))

(value-triple :itpeval-statement-checked)
:q
