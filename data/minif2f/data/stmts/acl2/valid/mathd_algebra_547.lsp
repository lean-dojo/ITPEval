;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_547:
;; for real x = 5 and y = 2, the principal square root of x^3 - 2^y is 11.
;; This file contains no proof.
;;
;; The hypotheses fix both real variables to rational values, so every
;; satisfying source assignment is represented exactly in ACL2 and conversely
;; embeds unchanged into the reals. For a nonnegative root, equality of its
;; square with the radicand is bidirectionally equivalent to the corresponding
;; principal-real-square-root equality.

(in-package "ACL2")

(defun mathd-algebra-547-principal-square-root-value-p (root radicand)
  (and (rationalp root)
       (rationalp radicand)
       (<= 0 root)
       (equal (expt root 2) radicand)))

(defun mathd-algebra-547-statement (x y)
  (implies
   (and (rationalp x)
        (rationalp y)
        (equal x 5)
        (equal y 2))
   (mathd-algebra-547-principal-square-root-value-p
    11
    (- (expt x 3)
       (expt 2 y)))))

(value-triple :itpeval-statement-checked)
:q
