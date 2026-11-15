;; Statement-only formalization of Logipedia corpus artifact nat.minus_O_n,
;; catalog title "nat.minus_O_n": subtracting any natural number from zero
;; using truncated natural subtraction yields zero. This file contains no
;; proof.

(in-package "ACL2")

;; On natural inputs, nfix of the integer difference is truncated natural
;; subtraction.
(defun logipedia-nat-minus-o-n-minus (minuend subtrahend)
  (nfix (- (nfix minuend) (nfix subtrahend))))

(defun-sk logipedia-nat-minus-o-n-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      0
      (logipedia-nat-minus-o-n-minus 0 n)))))

(value-triple :itpeval-statement-checked)
:q
