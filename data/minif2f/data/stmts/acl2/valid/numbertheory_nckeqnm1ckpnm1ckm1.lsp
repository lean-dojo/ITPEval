;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_nckeqnm1ckpnm1ckm1: Pascal's identity for binomial
;; coefficients at positive natural numbers n and k with k <= n.
;; This file contains no proof.

(in-package "ACL2")

(defun numbertheory-nckeqnm1ckpnm1ckm1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (numbertheory-nckeqnm1ckpnm1ckm1-factorial (- n 1)))))

;; On natural inputs this is the standard binomial coefficient, with value
;; zero when k exceeds n.
(defun numbertheory-nckeqnm1ckpnm1ckm1-binomial-coefficient (n k)
  (if (and (natp n)
           (natp k)
           (<= k n))
      (/ (numbertheory-nckeqnm1ckpnm1ckm1-factorial n)
         (* (numbertheory-nckeqnm1ckpnm1ckm1-factorial k)
            (numbertheory-nckeqnm1ckpnm1ckm1-factorial (- n k))))
    0))

(defun numbertheory-nckeqnm1ckpnm1ckm1-statement (n k)
  (implies
   (and (natp n)
        (natp k)
        (< 0 n)
        (< 0 k)
        (<= k n))
   (equal
    (numbertheory-nckeqnm1ckpnm1ckm1-binomial-coefficient n k)
    (+ (numbertheory-nckeqnm1ckpnm1ckm1-binomial-coefficient
        (- n 1) k)
       (numbertheory-nckeqnm1ckpnm1ckm1-binomial-coefficient
        (- n 1) (- k 1))))))

(value-triple :itpeval-statement-checked)
:q
