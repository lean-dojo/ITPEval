;; Statement-only formalization of miniF2F artifact mathd_algebra_208:
;; the exact nonnegative real square root and cube root of 1,000,000 differ
;; by 900. Both roots are rational, so their defining polynomial equations
;; and order conditions are preserved by ACL2 rational arithmetic. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-algebra-208-nonnegative-square-root-p (root radicand)
  (and (rationalp root)
       (rationalp radicand)
       (<= 0 root)
       (equal (expt root 2) radicand)))

(defun mathd-algebra-208-nonnegative-cube-root-p (root radicand)
  (and (rationalp root)
       (rationalp radicand)
       (<= 0 root)
       (equal (expt root 3) radicand)))

(defun mathd-algebra-208-statement ()
  (and
   (mathd-algebra-208-nonnegative-square-root-p 1000 1000000)
   (mathd-algebra-208-nonnegative-cube-root-p 100 1000000)
   (equal (- 1000 100) 900)))

(value-triple :itpeval-statement-checked)
:q
