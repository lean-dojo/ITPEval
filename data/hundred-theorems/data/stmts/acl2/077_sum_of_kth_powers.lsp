;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__077, "Sum of kth Powers": for all natural numbers
;; n and m, the inclusive sum from k = 0 through n of k^m equals the
;; Bernoulli-polynomial finite-difference formula. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-077-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (hundred-theorems-077-binomial-coefficient
        (- n 1) k)
       (hundred-theorems-077-binomial-coefficient
        (- n 1) (- k 1)))))

(defun hundred-theorems-077-bernoulli-weighted-sum
    (row k values)
  (if (consp values)
      (+ (* (hundred-theorems-077-binomial-coefficient row k)
            (car values))
         (hundred-theorems-077-bernoulli-weighted-sum
          row (+ k 1) (cdr values)))
    0))

(defun hundred-theorems-077-bernoulli-prefix (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 1)
    (let* ((previous
            (hundred-theorems-077-bernoulli-prefix (- n 1)))
           (weighted-sum
            (hundred-theorems-077-bernoulli-weighted-sum
             (+ n 1) 0 previous))
           (next (/ (- weighted-sum) (+ n 1))))
      (append previous (list next)))))

(defun hundred-theorems-077-bernoulli-number (n)
  (nth n (hundred-theorems-077-bernoulli-prefix n)))

(defun hundred-theorems-077-bernoulli-polynomial-term
    (degree k x)
  (* (hundred-theorems-077-binomial-coefficient degree k)
     (* (hundred-theorems-077-bernoulli-number k)
        (expt x (- degree k)))))

(defun hundred-theorems-077-bernoulli-polynomial-sum-through
    (degree k x)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (hundred-theorems-077-bernoulli-polynomial-term degree 0 x)
    (+ (hundred-theorems-077-bernoulli-polynomial-sum-through
        degree (- k 1) x)
       (hundred-theorems-077-bernoulli-polynomial-term degree k x))))

(defun hundred-theorems-077-bernoulli-polynomial (degree x)
  (hundred-theorems-077-bernoulli-polynomial-sum-through
   degree degree x))

(defun hundred-theorems-077-power-sum-through (n exponent)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (expt 0 exponent)
    (+ (hundred-theorems-077-power-sum-through
        (- n 1) exponent)
       (expt n exponent))))

(defun hundred-theorems-077-sum-of-kth-powers-statement (n m)
  (implies
   (and (natp n)
        (natp m))
   (equal
    (hundred-theorems-077-power-sum-through n m)
    (/ (- (hundred-theorems-077-bernoulli-polynomial
           (+ m 1) (+ n 1))
          (hundred-theorems-077-bernoulli-polynomial
           (+ m 1) 0))
       (+ m 1)))))

(value-triple :itpeval-statement-checked)
:q
