;; Statement-only formalization of PutnamBench artifact putnam_1967_a2:
;; the count of symmetric nonnegative-integer matrices with every column sum
;; equal to one, its recurrence, and its exponential generating function.
;; This file contains no proof.

(in-package "ACL2")

;; A matrix in the source set has exactly one entry equal to one in each
;; column and all other entries zero. It is therefore determined by a
;; function f on {0,...,n-1}; symmetry is equivalent to f(f(j)) = j.
;; Thus counting the function codes accepted below is exactly the source
;; matrix cardinality, including the unique empty matrix when n = 0.
(defun putnam-1967-a2-function-value (code index radix)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (mod code radix)
    (putnam-1967-a2-function-value
     (floor code radix)
     (- index 1)
     radix)))

(defun putnam-1967-a2-involution-code-aux-p
    (code remaining radix)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let* ((index (- remaining 1))
           (image
            (putnam-1967-a2-function-value
             code index radix)))
      (and
       (equal
        (putnam-1967-a2-function-value
         code image radix)
        index)
       (putnam-1967-a2-involution-code-aux-p
        code index radix)))))

(defun putnam-1967-a2-involution-code-p (code n)
  (and (natp n)
       (< code (expt n n))
       (putnam-1967-a2-involution-code-aux-p
        code n n)))

(defun putnam-1967-a2-count-involution-codes
    (code-count n)
  (declare (xargs :measure (nfix code-count)))
  (if (zp code-count)
      0
    (let ((code (- code-count 1)))
      (+
       (if (putnam-1967-a2-involution-code-p code n)
           1
         0)
       (putnam-1967-a2-count-involution-codes
        code n)))))

(defun putnam-1967-a2-matrix-count (n)
  (if (natp n)
      (putnam-1967-a2-count-involution-codes
       (expt n n)
       n)
    0))

(defun putnam-1967-a2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1967-a2-factorial (- n 1)))))

;; Since exp(x + x^2/2) = exp(x) * exp(x^2/2), its coefficient of x^n is
;;
;;   sum_{0 <= k <= n/2} 1 / ((n-2k)! 2^k k!).
;;
;; Both sides of the source generating-function identity are entire real
;; power series. Consequently, equality for every real x is bidirectionally
;; equivalent to equality of every rational Taylor coefficient. This formal
;; coefficient encoding preserves the universal real identity without
;; restricting x to the ACL2 rationals.
(defun putnam-1967-a2-exp-quadratic-coefficient-sum
    (n term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let* ((k (- term-count 1))
           (linear-degree (- n (* 2 k))))
      (+
       (/ 1
          (* (putnam-1967-a2-factorial linear-degree)
             (expt 2 k)
             (putnam-1967-a2-factorial k)))
       (putnam-1967-a2-exp-quadratic-coefficient-sum
        n k)))))

(defun putnam-1967-a2-exp-quadratic-coefficient (n)
  (if (natp n)
      (putnam-1967-a2-exp-quadratic-coefficient-sum
       n
       (+ 1 (floor n 2)))
    0))

;; The source hypotheses uniquely determine S at every natural index:
;; S(0) is one and, for n >= 1, S(n) is the matrix count defined above.
;; Eliminating that uniquely specified function is definitionally
;; equivalent to the original implication. The free ACL2 argument n
;; universally ranges over both requested conclusions.
(defun putnambench-putnam-1967-a2-statement (n)
  (implies
   (natp n)
   (and
    (implies
     (<= 1 n)
     (equal
      (putnam-1967-a2-matrix-count (+ n 1))
      (+
       (putnam-1967-a2-matrix-count n)
       (* n
          (putnam-1967-a2-matrix-count
           (- n 1))))))
    (equal
     (/ (putnam-1967-a2-matrix-count n)
        (putnam-1967-a2-factorial n))
     (putnam-1967-a2-exp-quadratic-coefficient n)))))

(value-triple :itpeval-statement-checked)
:q
