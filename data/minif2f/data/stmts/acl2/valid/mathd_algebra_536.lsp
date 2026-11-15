;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_536:
;; over the real numbers, 3! times (2^3 + sqrt(9)), divided by 2, equals 33.
;; The square root is characterized as the nonnegative root rather than
;; replaced by its precomputed value. This file contains no proof.

(in-package "ACL2")

(defun mathd-algebra-536-factorial (n)
  (if (zp n)
      1
    (* n (mathd-algebra-536-factorial (- n 1)))))

(defun mathd-algebra-536-principal-sqrt-nine-p (root)
  (and (rationalp root)
       (<= 0 root)
       (equal (* root root) 9)))

(defun-sk mathd-algebra-536-statement ()
  (exists (root)
    (and
     (mathd-algebra-536-principal-sqrt-nine-p root)
     (equal
      (/ (* (mathd-algebra-536-factorial 3)
            (+ (expt 2 3) root))
         2)
      33))))

(value-triple :itpeval-statement-checked)
:q
