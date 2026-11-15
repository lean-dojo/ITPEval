;; Statement-only formalization of miniF2F corpus artifact aime_1991_p1:
;; positive natural numbers satisfying the given two Diophantine equations
;; have sum of squares equal to 146. This file contains no proof.

(in-package "ACL2")

(defun aime-1991-p1-statement (x y)
  (implies
   (and (natp x)
        (natp y)
        (< 0 x)
        (< 0 y)
        (equal (+ (* x y)
                  (+ x y))
               71)
        (equal (+ (* (expt x 2) y)
                  (* x (expt y 2)))
               880))
   (equal (+ (expt x 2)
             (expt y 2))
          146)))

(value-triple :itpeval-statement-checked)
:q
