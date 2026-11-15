;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_b1:
;; integer-valued leading-coefficient partial sums at a rational root of an
;; integer polynomial. This file contains no proof.

(in-package "ACL2")

;; Coefficients are stored in ascending degree order. A proper integer list
;; of length n+1 with nonzero nth entry represents exactly a degree-n
;; polynomial over the integers. Since ACL2 rationals are exact, INTEGERP of
;; each displayed rational sum is equivalent to the source's existential
;; equality with an integer.

(defun putnam-2004-b1-integer-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and (integerp (car coefficients))
           (putnam-2004-b1-integer-coefficient-list-p
            (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2004-b1-polynomial-evaluate (coefficients r)
  (if (consp coefficients)
      (+ (car coefficients)
         (* r
            (putnam-2004-b1-polynomial-evaluate
             (cdr coefficients) r)))
    0))

;; For i >= 0, this is
;; c_n*r^(i+1) + c_(n-1)*r^i + ... + c_(n-i)*r.
(defun putnam-2004-b1-leading-partial-sum
    (coefficients n r i)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      (* (nth n coefficients) r)
    (* r
       (+ (putnam-2004-b1-leading-partial-sum
           coefficients n r (- i 1))
          (nth (- n i) coefficients)))))

(defun putnambench-putnam-2004-b1-statement
    (coefficients n r i)
  (implies
   (and (natp n)
        (rationalp r)
        (natp i)
        (true-listp coefficients)
        (putnam-2004-b1-integer-coefficient-list-p coefficients)
        (equal (len coefficients) (+ n 1))
        (not (equal (nth n coefficients) 0))
        (equal
         (putnam-2004-b1-polynomial-evaluate coefficients r)
         0)
        (< i n))
   (integerp
    (putnam-2004-b1-leading-partial-sum
     coefficients n r i))))

(value-triple :itpeval-statement-checked)
:q
