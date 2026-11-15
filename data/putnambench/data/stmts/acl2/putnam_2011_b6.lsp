;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_b6:
;; for every odd prime p, at least (p+1)/2 residues n from 0 through p-1
;; make the factorial polynomial sum from k=0 through p-1 nonzero modulo p.
;; This file contains no proof.

(in-package "ACL2")

;; Testing every possible divisor from 2 through NUMBER-1 is exactly the
;; usual primality condition for a natural number greater than one.
(defun putnam-2011-b6-no-divisor-through-p (number divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (or (not (natp divisor))
          (<= divisor 1))
      t
    (and
     (not (equal (mod number divisor) 0))
     (putnam-2011-b6-no-divisor-through-p
      number (- divisor 1)))))

(defun putnam-2011-b6-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2011-b6-no-divisor-through-p
    number (- number 1))))

(defun putnam-2011-b6-factorial (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (* k
       (putnam-2011-b6-factorial (- k 1)))))

;; COUNT represents the source index range 0,...,COUNT-1.
(defun putnam-2011-b6-factorial-polynomial-sum (n count)
  (declare (xargs :measure (nfix count)))
  (if (or (not (natp n))
          (not (natp count))
          (zp count))
      0
    (let ((k (- count 1)))
      (+ (* (putnam-2011-b6-factorial k)
            (expt n k))
         (putnam-2011-b6-factorial-polynomial-sum
          n k)))))

(defun putnam-2011-b6-nondivisible-p (p n)
  (and
   (natp p)
   (< 0 p)
   (natp n)
   (not
    (equal
     (mod
      (putnam-2011-b6-factorial-polynomial-sum n p)
      p)
     0))))

;; COUNT represents the source residue range 0,...,COUNT-1, so calling this
;; with COUNT=P computes exactly the cardinality appearing in the statement.
(defun putnam-2011-b6-nondivisible-count (p count)
  (declare (xargs :measure (nfix count)))
  (if (or (not (natp p))
          (not (natp count))
          (zp count))
      0
    (let ((n (- count 1)))
      (+ (if (putnam-2011-b6-nondivisible-p p n)
             1
           0)
         (putnam-2011-b6-nondivisible-count
          p n)))))

(defun putnambench-putnam-2011-b6-statement (p)
  (implies
   (and
    (putnam-2011-b6-prime-p p)
    (equal (mod p 2) 1))
   (<= (floor (+ p 1) 2)
       (putnam-2011-b6-nondivisible-count p p))))

(value-triple :itpeval-statement-checked)
:q
