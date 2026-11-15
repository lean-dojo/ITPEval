;; Statement-only formalization of the hundred-theorems corpus artifact
;; hundred-theorems__acl2__067, "e is Transcendental": Euler's number
;; exp(1) is not a root of any nonzero integer polynomial. Exact rational
;; partial sums of its defining exponential series represent exp(1).
;; This file contains no proof.

(in-package "ACL2")

(defun ht067-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (ht067-factorial (- n 1)))))

(defun ht067-exp-one-series-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (ht067-exp-one-series-prefix index)
         (/ 1 (ht067-factorial index))))))

;; The nth approximation is sum_{k=0}^n 1/k!, whose real limit is exp(1).
(defun ht067-exp-one-approximation (index)
  (ht067-exp-one-series-prefix (+ 1 (nfix index))))

(defun ht067-integer-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and (integerp (car coefficients))
           (ht067-integer-coefficient-list-p
            (cdr coefficients)))
    (equal coefficients nil)))

(defun ht067-nonzero-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (or (not (equal (car coefficients) 0))
          (ht067-nonzero-coefficient-list-p
           (cdr coefficients)))
    nil))

;; Coefficients are listed in ascending order of exponent.
(defun ht067-polynomial-value (coefficients x)
  (if (consp coefficients)
      (+ (car coefficients)
         (* x
            (ht067-polynomial-value
             (cdr coefficients) x)))
    0))

(defun-sk ht067-polynomial-zero-tail-p
  (coefficients epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (<
      (abs
       (ht067-polynomial-value
        coefficients
        (ht067-exp-one-approximation index)))
      epsilon))))

(defun-sk ht067-polynomial-zero-cutoff-exists-p
  (coefficients epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht067-polynomial-zero-tail-p
      coefficients epsilon cutoff))))

(defun-sk ht067-polynomial-tends-to-zero-p (coefficients)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (ht067-polynomial-zero-cutoff-exists-p
      coefficients epsilon))))

(defun-sk ht067-exp-one-is-algebraic-p ()
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (ht067-integer-coefficient-list-p coefficients)
     (ht067-nonzero-coefficient-list-p coefficients)
     (ht067-polynomial-tends-to-zero-p coefficients))))

(defun hundred-theorems-067-e-is-transcendental-statement ()
  (not (ht067-exp-one-is-algebraic-p)))

(value-triple :itpeval-statement-checked)
:q
