;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_b1:
;; a nonconstant integer polynomial with nonnegative coefficients satisfies
;; f(n) divides f(f(n)+1) exactly when the positive integer n is 1.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Coefficients are listed in ascending degree order. Every integer polynomial
;; has such a finite list, and allowing trailing zeroes does not change either
;; its evaluation or the proposition, so this represents the full source
;; polynomial domain rather than a bounded family.

(defun putnam-2007-b1-nonnegative-integer-coefficients-p
    (coefficients)
  (if (consp coefficients)
      (and
       (integerp (car coefficients))
       (<= 0 (car coefficients))
       (putnam-2007-b1-nonnegative-integer-coefficients-p
        (cdr coefficients)))
    (equal coefficients nil)))

;; Applied to the positive-degree tail, this is the source's internal
;; existential assertion that some coefficient of degree greater than zero
;; is positive.
(defun putnam-2007-b1-positive-coefficient-exists-p
    (coefficients)
  (if (consp coefficients)
      (or
       (< 0 (car coefficients))
       (putnam-2007-b1-positive-coefficient-exists-p
        (cdr coefficients)))
    nil))

(defun putnam-2007-b1-evaluate (coefficients x)
  (if (consp coefficients)
      (+ (car coefficients)
         (* x
            (putnam-2007-b1-evaluate
             (cdr coefficients) x)))
    0))

(defun putnam-2007-b1-integer-divides-p (divisor multiple)
  (and
   (integerp divisor)
   (integerp multiple)
   (if (equal divisor 0)
       (equal multiple 0)
     (equal (mod multiple divisor) 0))))

(defun putnambench-putnam-2007-b1-statement (coefficients n)
  (implies
   (and
    (true-listp coefficients)
    (putnam-2007-b1-nonnegative-integer-coefficients-p
     coefficients)
    (putnam-2007-b1-positive-coefficient-exists-p
     (cdr coefficients))
    (integerp n)
    (< 0 n))
   (let* ((f-of-n
           (putnam-2007-b1-evaluate coefficients n))
          (f-of-f-of-n-plus-one
           (putnam-2007-b1-evaluate
            coefficients (+ f-of-n 1))))
     (equal
      (putnam-2007-b1-integer-divides-p
       f-of-n f-of-f-of-n-plus-one)
      (equal n 1)))))

(value-triple :itpeval-statement-checked)
:q
