;; Statement-only formalization of miniF2F corpus artifact imo_1974_p3:
;; for every natural n, 5 does not divide the sum from k = 0 through n of
;; choose(2*n+1, 2*k+1) * 2^(3*k). This file contains no proof.

(in-package "ACL2")

(defun imo-1974-p3-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (imo-1974-p3-binomial-coefficient (- n 1) k)
       (imo-1974-p3-binomial-coefficient (- n 1) (- k 1)))))

(defun imo-1974-p3-term (n k)
  (* (imo-1974-p3-binomial-coefficient
      (+ (* 2 n) 1)
      (+ (* 2 k) 1))
     (expt 2 (* 3 k))))

(defun imo-1974-p3-sum-through (n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (imo-1974-p3-term n 0)
    (+ (imo-1974-p3-sum-through n (- k 1))
       (imo-1974-p3-term n k))))

(defun imo-1974-p3-statement (n)
  (implies
   (natp n)
   (not
    (equal
     (mod (imo-1974-p3-sum-through n n) 5)
     0))))

(value-triple :itpeval-statement-checked)
:q
