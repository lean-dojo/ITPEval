;; Statement-only formalization of the PutnamBench corpus artifact
;; putnam_2014_a1: every nonzero Taylor coefficient of
;; (1 - x + x^2) * exp(x) has reduced numerator 1 or a prime number. This
;; file contains no proof.

(in-package "ACL2")

(defun putnam-2014-a1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2014-a1-factorial (- n 1)))))

;; The coefficient of x^n is the convolution of 1 - x + x^2 with the
;; coefficient sequence 1/n! of exp(x). This exact rational formula
;; eliminates the source's uniquely determined real function and coefficient
;; function without changing the quantified proposition.
(defun putnam-2014-a1-coefficient (n)
  (if (natp n)
      (+ (/ 1 (putnam-2014-a1-factorial n))
         (if (posp n)
             (- (/ 1
                   (putnam-2014-a1-factorial (- n 1))))
           0)
         (if (<= 2 n)
             (/ 1
                (putnam-2014-a1-factorial (- n 2)))
           0))
    0))

(defun putnam-2014-a1-no-proper-divisor-through-p
    (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod number candidate) 0))
     (putnam-2014-a1-no-proper-divisor-through-p
      number (- candidate 1)))))

(defun putnam-2014-a1-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2014-a1-no-proper-divisor-through-p
    number (- number 1))))

(defun putnambench-putnam-2014-a1-statement (n)
  (implies
   (natp n)
   (let ((coefficient
          (putnam-2014-a1-coefficient n)))
     (implies
      (not (equal coefficient 0))
      (and
       (rationalp coefficient)
       (or
        (equal (numerator coefficient) 1)
        (putnam-2014-a1-prime-p
         (abs (numerator coefficient)))))))))

(value-triple :itpeval-statement-checked)
:q
