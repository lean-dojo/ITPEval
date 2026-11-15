;; Statement-only formalization of Logipedia corpus artifact
;; nat.minus_plus_plus_l, catalog title "nat.minus_plus_plus_l": for all
;; natural numbers x, y, and h, adding h to both operands leaves their
;; truncated natural difference unchanged. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-plus-plus-l-statement ()
  (forall (x y h)
    (implies
     (and (natp x)
          (natp y)
          (natp h))
     (equal
      (nfix (- (+ x h) (+ y h)))
      (nfix (- x y))))))

(value-triple :itpeval-statement-checked)
:q
