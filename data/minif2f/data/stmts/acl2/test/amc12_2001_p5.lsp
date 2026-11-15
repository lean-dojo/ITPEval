;; Statement-only formalization of miniF2F artifact amc12_2001_p5: the
;; product of the positive odd natural numbers below 10,000 equals 10,000!
;; divided in the natural numbers by 2^5000 times 5000!. This file contains
;; no proof.

(in-package "ACL2")

(defun amc12-2001-p5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (amc12-2001-p5-factorial (- n 1)))))

(defun amc12-2001-p5-odd-product-below (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (let ((previous (- n 1)))
      (* (if (equal (mod previous 2) 1)
             previous
           1)
         (amc12-2001-p5-odd-product-below previous)))))

(defun amc12-2001-p5-statement ()
  (equal
   (amc12-2001-p5-odd-product-below 10000)
   (floor
    (amc12-2001-p5-factorial 10000)
    (* (expt 2 5000)
       (amc12-2001-p5-factorial 5000)))))

(value-triple :itpeval-statement-checked)
:q
