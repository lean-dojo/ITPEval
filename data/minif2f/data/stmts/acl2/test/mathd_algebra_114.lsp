;; Statement-only formalization of miniF2F artifact mathd_algebra_114:
;; when a = 8, the nested real cube-root expression
;; cube-root(16 * cube-root(a^2)) equals 4. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-114-cube-root-value-p (root radicand)
  (and (rationalp root)
       (rationalp radicand)
       (equal (expt root 3) radicand)))

(defun mathd-algebra-114-statement (a)
  (implies
   (and (rationalp a)
        (equal a 8))
   (and
    (mathd-algebra-114-cube-root-value-p 4 (expt a 2))
    (mathd-algebra-114-cube-root-value-p 4 (* 16 4)))))

(value-triple :itpeval-statement-checked)
:q
