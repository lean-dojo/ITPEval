;; Statement-only formalization of PutnamBench artifact putnam_1962_b1:
;; the binomial addition formula for real falling-factorial polynomials.
;; This file contains no proof.

(in-package "ACL2")

;; The hypotheses uniquely identify p n as the nth falling-factorial
;; polynomial (with p 0 = 1). The predicate below compares the complete
;; integer coefficient grids of the two resulting bivariate polynomials.
;; Equality of these grids implies the source equality at every pair of real
;; values. Conversely, a real polynomial identity has equal coefficients, so
;; this formal-polynomial encoding is bidirectionally equivalent to the
;; universally quantified source statement and does not restrict real inputs
;; to ACL2's rational number domain.

(defun putnam-1962-b1-polynomial-add (left right)
  (if (endp left)
      right
    (if (endp right)
        left
      (cons (+ (car left) (car right))
            (putnam-1962-b1-polynomial-add
             (cdr left) (cdr right))))))

(defun putnam-1962-b1-polynomial-scale (coefficient polynomial)
  (if (endp polynomial)
      nil
    (cons (* coefficient (car polynomial))
          (putnam-1962-b1-polynomial-scale
           coefficient (cdr polynomial)))))

;; Coefficients are in ascending degree order. This recurrence multiplies
;; the preceding polynomial by X - (n - 1).
(defun putnam-1962-b1-falling-factorial-coefficients (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 1)
    (let* ((previous
            (putnam-1962-b1-falling-factorial-coefficients
             (- n 1)))
           (constant (- n 1)))
      (putnam-1962-b1-polynomial-add
       (putnam-1962-b1-polynomial-scale
        (- constant) previous)
       (cons 0 previous)))))

(defun putnam-1962-b1-coefficient-at (degree coefficients)
  (declare (xargs :measure (nfix degree)))
  (if (endp coefficients)
      0
    (if (zp degree)
        (car coefficients)
      (putnam-1962-b1-coefficient-at
       (- degree 1) (cdr coefficients)))))

(defun putnam-1962-b1-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k) (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1962-b1-binomial (- n 1) k)
       (putnam-1962-b1-binomial
        (- n 1) (- k 1)))))

;; In p_n(X + Y), the coefficient of X^a Y^b is the coefficient
;; of T^(a+b) in p_n(T), multiplied by choose(a+b,a).
(defun putnam-1962-b1-left-coefficient (n a b)
  (let ((total-degree (+ a b)))
    (* (putnam-1962-b1-coefficient-at
        total-degree
        (putnam-1962-b1-falling-factorial-coefficients n))
       (putnam-1962-b1-binomial total-degree a))))

(defun putnam-1962-b1-right-coefficient-sum (n k a b)
  (declare (xargs :measure (nfix k)))
  (let ((term
         (* (putnam-1962-b1-binomial n k)
            (putnam-1962-b1-coefficient-at
             a
             (putnam-1962-b1-falling-factorial-coefficients k))
            (putnam-1962-b1-coefficient-at
             b
             (putnam-1962-b1-falling-factorial-coefficients
              (- n k))))))
    (if (zp k)
        term
      (+ term
         (putnam-1962-b1-right-coefficient-sum
          n (- k 1) a b)))))

(defun putnam-1962-b1-left-row (n a b)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      (list (putnam-1962-b1-left-coefficient n a 0))
    (cons (putnam-1962-b1-left-coefficient n a b)
          (putnam-1962-b1-left-row n a (- b 1)))))

(defun putnam-1962-b1-right-row (n a b)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      (list
       (putnam-1962-b1-right-coefficient-sum n n a 0))
    (cons
     (putnam-1962-b1-right-coefficient-sum n n a b)
     (putnam-1962-b1-right-row n a (- b 1)))))

(defun putnam-1962-b1-left-coefficient-grid (n a)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      (list (putnam-1962-b1-left-row n 0 n))
    (cons (putnam-1962-b1-left-row n a n)
          (putnam-1962-b1-left-coefficient-grid
           n (- a 1)))))

(defun putnam-1962-b1-right-coefficient-grid (n a)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      (list (putnam-1962-b1-right-row n 0 n))
    (cons (putnam-1962-b1-right-row n a n)
          (putnam-1962-b1-right-coefficient-grid
           n (- a 1)))))

(defun putnambench-putnam-1962-b1-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-1962-b1-left-coefficient-grid n n)
    (putnam-1962-b1-right-coefficient-grid n n))))

(value-triple :itpeval-statement-checked)
:q
