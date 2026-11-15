;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_459:
;; four linear equations over rational numbers imply that the numerator and
;; denominator of d in reduced form sum to 28. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-459-statement (a b c d)
  (implies
   (and (rationalp a)
        (rationalp b)
        (rationalp c)
        (rationalp d)
        (equal (* 3 a)
               (+ b c d))
        (equal (* 4 b)
               (+ a c d))
        (equal (* 2 c)
               (+ a b d))
        (equal (+ (* 8 a)
                  (* 10 b)
                  (* 6 c))
               24))
   (equal (+ (denominator d)
             (numerator d))
          28)))

(value-triple :itpeval-statement-checked)
:q
