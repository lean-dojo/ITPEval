;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_a1:
;; no four consecutive binomial coefficients choose(n,r) through
;; choose(n,r+3), for positive natural n and r with r+3 <= n, form an
;; arithmetic progression. This file contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1972-a1-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1972-a1-binomial-coefficient (- n 1) k)
       (putnam-1972-a1-binomial-coefficient
        (- n 1) (- k 1)))))

(defun putnam-1972-a1-four-ap-p (n r)
  (let ((c0 (putnam-1972-a1-binomial-coefficient n r))
        (c1 (putnam-1972-a1-binomial-coefficient n (+ r 1)))
        (c2 (putnam-1972-a1-binomial-coefficient n (+ r 2)))
        (c3 (putnam-1972-a1-binomial-coefficient n (+ r 3))))
    (and (equal (- c3 c2) (- c2 c1))
         (equal (- c2 c1) (- c1 c0)))))

;; For natural n, this searches exactly the positive r satisfying r+3 <= n.
(defun putnam-1972-a1-has-four-ap-through (n r)
  (declare (xargs :measure (nfix r)))
  (if (zp r)
      nil
    (or (putnam-1972-a1-four-ap-p n r)
        (putnam-1972-a1-has-four-ap-through n (- r 1)))))

(defun putnambench-putnam-1972-a1-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (not
    (putnam-1972-a1-has-four-ap-through n (- n 3)))))

(value-triple :itpeval-statement-checked)
:q
