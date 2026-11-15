;; Statement-only formalization of miniF2F corpus artifact
;; induction_pord1p1on2powklt5on2: for every positive natural number n, the
;; product from k = 1 through n of 1 + 1/2^k is strictly less than 5/2.
;; ACL2 computes this rational product exactly, with the same value and order
;; after embedding it in the reals. This file contains no proof.

(in-package "ACL2")

(defun induction-pord1p1on2powklt5on2-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (induction-pord1p1on2powklt5on2-product (- n 1))
       (+ 1 (/ 1 (expt 2 n))))))

(defun induction-pord1p1on2powklt5on2-statement (n)
  (implies (and (natp n)
                (< 0 n))
           (< (induction-pord1p1on2powklt5on2-product n)
              (/ 5 2))))

(value-triple :itpeval-statement-checked)
:q
