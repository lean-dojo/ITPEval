;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_b2:
;; the coefficient of x^k in (1+x+x^2+x^3)^n equals a finite sum of products
;; of natural-number binomial coefficients. This file contains no proof.

(in-package "ACL2")

;; Pascal recursion with zero outside 0 <= k <= n is the standard natural
;; binomial coefficient used by the source statements.
(defun putnam-1992-b2-choose (n k)
  (declare (xargs :measure (nfix n)))
  (if (and (natp n)
           (natp k))
      (cond
       ((zp k) 1)
       ((zp n) 0)
       (t
        (+ (putnam-1992-b2-choose (- n 1) (- k 1))
           (putnam-1992-b2-choose (- n 1) k))))
    0))

;; Multiplication by 1+x+x^2+x^3 gives this exact recurrence for the
;; coefficient of x^k in (1+x+x^2+x^3)^n.
(defun putnam-1992-b2-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (and (natp n)
           (natp k))
      (if (zp n)
          (if (zp k) 1 0)
        (+ (putnam-1992-b2-coefficient (- n 1) k)
           (if (<= 1 k)
               (putnam-1992-b2-coefficient (- n 1) (- k 1))
             0)
           (if (<= 2 k)
               (putnam-1992-b2-coefficient (- n 1) (- k 2))
             0)
           (if (<= 3 k)
               (putnam-1992-b2-coefficient (- n 1) (- k 3))
             0)))
    0))

;; Inclusive sum over j from 0 through J. The source summand is zero when
;; 2*j > k, matching the explicit conditional in both ground-truth files.
(defun putnam-1992-b2-sum-through (n k j)
  (declare (xargs :measure (nfix j)))
  (if (and (natp n)
           (natp k)
           (natp j))
      (if (zp j)
          (* (putnam-1992-b2-choose n 0)
             (putnam-1992-b2-choose n k))
        (+ (* (putnam-1992-b2-choose n j)
              (if (<= (* 2 j) k)
                  (putnam-1992-b2-choose n (- k (* 2 j)))
                0))
           (putnam-1992-b2-sum-through n k (- j 1))))
    0))

;; The source function Q is eliminated by substituting its defining
;; polynomial coefficient. Universal closure over N and K is represented by
;; the free arguments of this predicate-valued statement definition.
(defun putnambench-putnam-1992-b2-statement (n k)
  (implies
   (and (natp n)
        (natp k))
   (equal
    (putnam-1992-b2-coefficient n k)
    (putnam-1992-b2-sum-through n k k))))

(value-triple :itpeval-statement-checked)
:q
