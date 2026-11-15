;; Statement-only formalization of miniF2F corpus artifact amc12a_2008_p2:
;; for a real number x, if x * (1/2 + 2/3) = 1, then x = 6/7. This file
;; contains no proof.
;;
;; ACL2 exact rationals give a bidirectionally equivalent closed statement.
;; The real theorem implies its rational restriction. Conversely, the
;; hypothesis is x * (7/6) = 1 and therefore forces x = 6/7, so every real
;; input satisfying the hypothesis is rational and occurs in this encoding.

(in-package "ACL2")

(defun amc12a-2008-p2-statement (x)
  (implies
   (and (rationalp x)
        (equal (* x
                  (+ (/ 1 2)
                     (/ 2 3)))
               1))
   (equal x (/ 6 7))))

(value-triple :itpeval-statement-checked)
:q
