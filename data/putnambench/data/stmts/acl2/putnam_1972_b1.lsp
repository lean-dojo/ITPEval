;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_b1:
;; no three consecutive coefficients of the real power series
;; sum_n x^n (x - 1)^(2n) / n! are all zero. This file contains no proof.

(in-package "ACL2")

(defun putnam-1972-b1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1972-b1-factorial (- n 1)))))

;; The source series is
;;
;;   exp(x (x - 1)^2) = exp(x) exp(-2 x^2) exp(x^3).
;;
;; Its coefficient of x^n is therefore the finite rational sum
;;
;;   sum_{i + 2j + 3k = n} (-2)^j / (i! j! k!).
;;
;; The inner sum fixes k and ranges over every possible j; i is then the
;; nonnegative remainder n - 2j - 3k.
(defun putnam-1972-b1-coefficient-inner-sum
    (n k term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let* ((j (- term-count 1))
           (i (- n (+ (* 2 j) (* 3 k)))))
      (+
       (/ (expt -2 j)
          (* (putnam-1972-b1-factorial i)
             (putnam-1972-b1-factorial j)
             (putnam-1972-b1-factorial k)))
       (putnam-1972-b1-coefficient-inner-sum
        n k j)))))

(defun putnam-1972-b1-coefficient-outer-sum
    (n term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let* ((k (- term-count 1))
           (remaining (- n (* 3 k)))
           (j-count (+ 1 (floor remaining 2))))
      (+
       (putnam-1972-b1-coefficient-inner-sum
        n k j-count)
       (putnam-1972-b1-coefficient-outer-sum
        n k)))))

(defun putnam-1972-b1-coefficient (n)
  (if (natp n)
      (putnam-1972-b1-coefficient-outer-sum
       n
       (+ 1 (floor n 3)))
    0))

;; Equality of real power series on a neighborhood of zero uniquely
;; determines every coefficient p(n). Thus the source hypotheses force p(n)
;; to equal the exact coefficient above. Conversely, these coefficients give
;; the source series, so eliminating S, p, and the local equality hypothesis
;; is bidirectionally equivalent to the original implication. The free
;; natural argument n is the universal form of the source's negated
;; existential conclusion.
(defun putnambench-putnam-1972-b1-statement (n)
  (implies
   (natp n)
   (not
    (and
     (equal (putnam-1972-b1-coefficient n) 0)
     (equal (putnam-1972-b1-coefficient (+ n 1)) 0)
     (equal (putnam-1972-b1-coefficient (+ n 2)) 0)))))

(value-triple :itpeval-statement-checked)
:q
