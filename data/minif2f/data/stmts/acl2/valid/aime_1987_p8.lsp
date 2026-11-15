;; Statement-only formalization of miniF2F corpus artifact aime_1987_p8:
;; 112 is the greatest positive natural number n for which there is a unique
;; natural k satisfying 8/15 < n/(n+k) < 7/13. This file contains no proof.
;;
;; For positive natural n and natural k, the denominator n+k is positive, so
;; the two strict rational inequalities are equivalent to
;;
;;   6*n < 7*k  and  8*k < 7*n.
;;
;; Thus the possible natural k range from floor(6*n/7)+1 through
;; floor((7*n-1)/8). There is exactly one such k precisely when the difference
;; of those two floors is 1. This finite arithmetic characterization is
;; bidirectionally equivalent to the source's internal unique existential and
;; does not externalize its witness.

(in-package "ACL2")

(defun aime-1987-p8-unique-k-p (n)
  (and (natp n)
       (< 0 n)
       (equal (- (floor (- (* 7 n) 1) 8)
                 (floor (* 6 n) 7))
              1)))

(defun aime-1987-p8-statement (n)
  (and (aime-1987-p8-unique-k-p 112)
       (implies (aime-1987-p8-unique-k-p n)
                (<= n 112))))

(value-triple :itpeval-statement-checked)
:q
