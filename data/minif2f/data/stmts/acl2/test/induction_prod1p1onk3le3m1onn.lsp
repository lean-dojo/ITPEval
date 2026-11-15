;; Statement-only formalization of miniF2F corpus artifact
;; induction_prod1p1onk3le3m1onn: for every positive natural number n, the
;; product from k = 1 through n of 1 + 1/k^3 is at most 3 - 1/n. ACL2
;; computes these rational quantities exactly, with the same values and order
;; after embedding them in the reals. This file contains no proof.

(in-package "ACL2")

(defun induction-prod1p1onk3le3m1onn-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (induction-prod1p1onk3le3m1onn-product (- n 1))
       (+ 1 (/ 1 (expt n 3))))))

(defun induction-prod1p1onk3le3m1onn-statement (n)
  (implies (and (natp n)
                (< 0 n))
           (<= (induction-prod1p1onk3le3m1onn-product n)
               (- 3 (/ 1 n)))))

(value-triple :itpeval-statement-checked)
:q
