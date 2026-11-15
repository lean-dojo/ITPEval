;; Statement-only formalization of miniF2F corpus artifact amc12b_2021_p4:
;; for positive natural numbers m and a with m/a = 3/4, the weighted average
;; (84*m + 70*a)/(m + a) equals 76. This file contains no proof.

(in-package "ACL2")

(defun amc12b-2021-p4-statement (m a)
  (implies
   (and (natp m)
        (natp a)
        (< 0 m)
        (< 0 a)
        (equal (/ m a) (/ 3 4)))
   (equal (/ (+ (* 84 m)
                (* 70 a))
             (+ m a))
          76)))

(value-triple :itpeval-statement-checked)
:q
