;; Statement-only formalization of miniF2F corpus artifact imo_2006_p3:
;; for all real numbers a, b, and c, the stated cyclic quartic expression
;; is at most 9*sqrt(2)/32 times (a^2+b^2+c^2)^2. This file contains no proof.
;;
;; Write L for the cyclic expression and Q for (a^2+b^2+c^2)^2. Since Q is
;; nonnegative, L <= 9*sqrt(2)*Q/32 is exactly equivalent to
;; L <= 0 or 512*L^2 <= 81*Q^2, which uses rational polynomial arithmetic.
;; The rationally quantified statement below is bidirectionally equivalent
;; to the real statement: restriction gives one direction, while any real
;; counterexample would persist on an open neighborhood containing a rational
;; triple, where the displayed radical-free equivalence applies.

(in-package "ACL2")

(defun imo-2006-p3-statement (a b c)
  (implies
   (and (rationalp a)
        (rationalp b)
        (rationalp c))
   (let* ((a2 (expt a 2))
          (b2 (expt b 2))
          (c2 (expt c 2))
          (left-hand-side
           (+ (* a b (- a2 b2))
              (* b c (- b2 c2))
              (* c a (- c2 a2))))
          (quadratic-square
           (expt (+ a2 b2 c2) 2)))
     (or (<= left-hand-side 0)
         (<= (* 512 (expt left-hand-side 2))
             (* 81 (expt quadratic-square 2)))))))

(value-triple :itpeval-statement-checked)
:q
