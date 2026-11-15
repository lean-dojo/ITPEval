;; Statement-only formalization of miniF2F corpus artifact amc12a_2021_p9:
;; the natural-number product over k = 0, ..., 6 of
;; 2^(2^k) + 3^(2^k) equals 3^128 - 2^128. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2021-p9-product-below (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (let ((k (- n 1)))
      (* (+ (expt 2 (expt 2 k))
            (expt 3 (expt 2 k)))
         (amc12a-2021-p9-product-below k)))))

(defun amc12a-2021-p9-statement ()
  (equal
   (amc12a-2021-p9-product-below 7)
   (- (expt 3 128)
      (expt 2 128))))

(value-triple :itpeval-statement-checked)
:q
