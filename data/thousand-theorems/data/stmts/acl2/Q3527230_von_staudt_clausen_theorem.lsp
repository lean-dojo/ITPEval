;; Statement-only formalization of thousand-theorems corpus artifact Q3527230,
;; "Von Staudt-Clausen theorem": for every natural k, the even Bernoulli
;; number B_(2k) plus the sum of 1/p over primes p < 2k + 2 with p - 1
;; dividing 2k is an integer. This file contains no proof.

(in-package "ACL2")

(defun q3527230-binomial-coefficient (n j)
  (declare (xargs :measure (nfix n)))
  (if (or (zp j)
          (zp n))
      (if (zp j) 1 0)
    (+ (q3527230-binomial-coefficient (- n 1) j)
       (q3527230-binomial-coefficient (- n 1) (- j 1)))))

;; This is the negative-first Bernoulli convention B_1 = -1/2 used by the
;; canonical Lean source. The recurrence computes exact rational values.

(defun q3527230-bernoulli-weighted-sum (row j values)
  (if (consp values)
      (+ (* (q3527230-binomial-coefficient row j)
            (car values))
         (q3527230-bernoulli-weighted-sum
          row (+ j 1) (cdr values)))
    0))

(defun q3527230-bernoulli-prefix (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 1)
    (let* ((previous
            (q3527230-bernoulli-prefix (- n 1)))
           (weighted-sum
            (q3527230-bernoulli-weighted-sum
             (+ n 1) 0 previous))
           (next (/ (- weighted-sum) (+ n 1))))
      (append previous (list next)))))

(defun q3527230-bernoulli-number (n)
  (nth n (q3527230-bernoulli-prefix n)))

(defun q3527230-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q3527230-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q3527230-primep (number)
  (and (natp number)
       (< 1 number)
       (q3527230-no-divisor-from-p number 2)))

;; Summing below LIMIT matches the Finset.range bound in the canonical source.

(defun q3527230-von-staudt-sum-below (limit twice-k)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0
    (let ((p (- limit 1)))
      (+ (q3527230-von-staudt-sum-below (- limit 1) twice-k)
         (if (and (q3527230-primep p)
                  (equal (mod twice-k (- p 1)) 0))
             (/ 1 p)
           0)))))

(defun thousand-theorems-q3527230-von-staudt-clausen-statement (k)
  (implies
   (natp k)
   (let ((twice-k (* 2 k)))
     (integerp
      (+ (q3527230-bernoulli-number twice-k)
         (q3527230-von-staudt-sum-below (+ twice-k 2) twice-k))))))

(value-triple :itpeval-statement-checked)
:q
