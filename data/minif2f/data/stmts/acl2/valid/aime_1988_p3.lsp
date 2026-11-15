;; Statement-only formalization of miniF2F corpus artifact aime_1988_p3:
;; for a positive real x satisfying the given nested base-2 and base-8
;; logarithm equation, the square of log base 2 of x is 27. This file
;; contains no proof.

(in-package "ACL2")

;; On the intended domain of the nested logarithms, put
;;
;;   u = log_2(log_2(x)),  L = log_2(3),  and  q = u/L.
;;
;; Since log_8(x) = log_2(x)/3 and L is nonzero, the source hypothesis is
;; equivalent to q - 1 = q/3. Also log_2(x) = 2^u = 3^q, so its square is
;; 27 exactly when 2q = 3. The encoded equation itself forces q = 3/2;
;; consequently every satisfying real source instance has a rational q.
;; Conversely, any rational q satisfying the equation reconstructs the
;; positive source instance x = 2^(3^q). Thus the rational coordinate below
;; represents the full satisfying locus rather than restricting x.
(defun aime-1988-p3-statement (q)
  (implies
   (and (rationalp q)
        (equal (- q 1)
               (/ q 3)))
   (equal (* 2 q)
          3)))

(value-triple :itpeval-statement-checked)
:q
