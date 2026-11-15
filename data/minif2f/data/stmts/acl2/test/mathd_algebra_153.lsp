;; Statement-only formalization of miniF2F artifact mathd_algebra_153: for a
;; real number n equal to 1/3, the sum of the floors of 10n, 100n, 1000n, and
;; 10000n is 3702. The hypothesis fixes n to an exact rational, so ACL2's
;; rational arithmetic and floor operation are equivalent here. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-algebra-153-statement (n)
  (implies
   (and (rationalp n)
        (equal n (/ 1 3)))
   (equal
    (+ (+ (floor (* 10 n) 1)
          (floor (* 100 n) 1))
       (+ (floor (* 1000 n) 1)
          (floor (* 10000 n) 1)))
    3702)))

(value-triple :itpeval-statement-checked)
:q
