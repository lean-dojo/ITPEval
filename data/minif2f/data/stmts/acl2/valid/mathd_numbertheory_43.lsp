;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_43:
;; 233 is the greatest natural exponent n for which 15^n divides 942
;; factorial. This file contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-43-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (mathd-numbertheory-43-factorial (- n 1)))))

(defun mathd-numbertheory-43-divides-p (d n)
  (and (natp d)
       (natp n)
       (if (equal d 0)
           (equal n 0)
         (equal (mod n d) 0))))

(defun mathd-numbertheory-43-statement ()
  (let ((factorial-942 (mathd-numbertheory-43-factorial 942)))
    (and
     (mathd-numbertheory-43-divides-p
      (expt 15 233)
      factorial-942)
     (not
      (mathd-numbertheory-43-divides-p
       (expt 15 234)
       factorial-942)))))

(value-triple :itpeval-statement-checked)
:q
