;; Statement-only formalization of miniF2F corpus artifact aime_1991_p6:
;; a sum of floors over k = 19,...,91 equal to 546 forces
;; floor(100*r) = 743. This file contains no proof.
;;
;; Standard ACL2 has no primitive arbitrary-real domain. This exact encoding
;; eliminates r by putting n = floor(100*r). For every integer k,
;; floor(r + k/100) = floor((n+k)/100), because 0 <= 100*r-n < 1.
;; Conversely, every integer n is attained by r = n/100. Thus the universal
;; integer implication below is bidirectionally equivalent to the source
;; universal real implication, without restricting r to rational values.

(in-package "ACL2")

(defun aime-1991-p6-floor-sum (n count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (floor (+ n (- 92 count)) 100)
       (aime-1991-p6-floor-sum n (- count 1)))))

(defun aime-1991-p6-statement (n)
  (implies
   (and (integerp n)
        (equal (aime-1991-p6-floor-sum n 73) 546))
   (equal n 743)))

(value-triple :itpeval-statement-checked)
:q
