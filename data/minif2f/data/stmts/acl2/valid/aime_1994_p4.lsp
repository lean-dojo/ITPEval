;; Statement-only formalization of miniF2F corpus artifact aime_1994_p4:
;; for a positive natural n, if the sum from k = 1 through n of
;; floor(log base 2 of k) is 1994, then n = 312. This file contains no proof.
;;
;; For every positive integer k, (integer-length k) - 1 is exactly
;; floor(log base 2 of k), so replacing each summand yields exactly the
;; source sum without restricting its domain.

(in-package "ACL2")

(defun aime-1994-p4-floor-log2 (k)
  (if (and (integerp k)
           (< 0 k))
      (- (integer-length k) 1)
    0))

(defun aime-1994-p4-sum-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (aime-1994-p4-floor-log2 n)
       (aime-1994-p4-sum-through (- n 1)))))

(defun aime-1994-p4-statement (n)
  (implies
   (and (natp n)
        (< 0 n)
        (equal (aime-1994-p4-sum-through n) 1994))
   (equal n 312)))

(value-triple :itpeval-statement-checked)
:q
