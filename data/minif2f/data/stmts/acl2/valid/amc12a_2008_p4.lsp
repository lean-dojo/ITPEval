;; Statement-only formalization of miniF2F corpus artifact amc12a_2008_p4:
;; the real product from k = 1 through 501 of (4*k + 4)/(4*k) equals 502.
;; ACL2 computes these rational factors exactly, with the same values after
;; embedding them in the reals. This file contains no proof.

(in-package "ACL2")

(defun amc12a-2008-p4-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (amc12a-2008-p4-product (- n 1))
       (/ (+ (* 4 n) 4)
          (* 4 n)))))

(defun amc12a-2008-p4-statement ()
  (equal (amc12a-2008-p4-product 501)
         502))

(value-triple :itpeval-statement-checked)
:q
