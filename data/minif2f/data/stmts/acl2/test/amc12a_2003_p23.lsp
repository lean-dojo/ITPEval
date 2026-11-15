;; Statement-only formalization of miniF2F corpus artifact amc12a_2003_p23:
;; the set of positive natural numbers k whose square divides the product
;; 1! * ... * 9! has cardinality 672. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2003-p23-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (amc12a-2003-p23-factorial (- n 1)))))

(defun amc12a-2003-p23-factorial-product-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (amc12a-2003-p23-factorial n)
       (amc12a-2003-p23-factorial-product-through (- n 1)))))

(defun amc12a-2003-p23-square-divides-p (k n)
  (and (natp k)
       (< 0 k)
       (natp n)
       (equal (mod n (* k k)) 0)))

(defun amc12a-2003-p23-count-square-divisors-through (limit n)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (+ (if (amc12a-2003-p23-square-divides-p limit n) 1 0)
       (amc12a-2003-p23-count-square-divisors-through (- limit 1) n))))

(defun amc12a-2003-p23-statement ()
  (let ((factorial-product
         (amc12a-2003-p23-factorial-product-through 9)))
    (equal
     (amc12a-2003-p23-count-square-divisors-through
      factorial-product
      factorial-product)
     672)))

(value-triple :itpeval-statement-checked)
:q
