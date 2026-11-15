;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_b2:
;; a unit complex number with rational real and imaginary parts has rational
;; distance from 1 after every even integer power. This file contains no proof.

(in-package "ACL2")

;; A pair (real-part . imaginary-part) represents a complex number whose
;; coordinates are rational.
(defun putnam-1973-b2-complexp (z)
  (and (consp z)
       (rationalp (car z))
       (rationalp (cdr z))))

(defun putnam-1973-b2-complex (real-part imaginary-part)
  (cons real-part imaginary-part))

(defun putnam-1973-b2-complex-add (z w)
  (putnam-1973-b2-complex
   (+ (car z) (car w))
   (+ (cdr z) (cdr w))))

(defun putnam-1973-b2-complex-neg (z)
  (putnam-1973-b2-complex
   (- (car z))
   (- (cdr z))))

(defun putnam-1973-b2-complex-sub (z w)
  (putnam-1973-b2-complex-add
   z
   (putnam-1973-b2-complex-neg w)))

(defun putnam-1973-b2-complex-mul (z w)
  (putnam-1973-b2-complex
   (- (* (car z) (car w))
      (* (cdr z) (cdr w)))
   (+ (* (car z) (cdr w))
      (* (cdr z) (car w)))))

(defun putnam-1973-b2-norm-squared (z)
  (+ (* (car z) (car z))
     (* (cdr z) (cdr z))))

(defun putnam-1973-b2-complex-inverse (z)
  (let ((norm-squared (putnam-1973-b2-norm-squared z)))
    (putnam-1973-b2-complex
     (/ (car z) norm-squared)
     (/ (- (cdr z)) norm-squared))))

(defun putnam-1973-b2-natural-power (z n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1973-b2-complex 1 0)
    (putnam-1973-b2-complex-mul
     z
     (putnam-1973-b2-natural-power z (- n 1)))))

(defun putnam-1973-b2-integer-power (z n)
  (if (< n 0)
      (putnam-1973-b2-natural-power
       (putnam-1973-b2-complex-inverse z)
       (- n))
    (putnam-1973-b2-natural-power z n)))

;; For a nonnegative rational x, this finite search is true exactly when x is
;; the square of an integer no larger than candidate.
(defun putnam-1973-b2-square-witness-down-p (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (equal x 0)
    (or (equal (* candidate candidate) x)
        (putnam-1973-b2-square-witness-down-p
         x
         (- candidate 1)))))

;; A nonnegative rational is the square of a rational exactly when its reduced
;; numerator and denominator are both integer squares. Thus this predicate is
;; equivalent to the source conclusion's existential rational norm witness.
(defun putnam-1973-b2-rational-square-p (x)
  (and (rationalp x)
       (<= 0 x)
       (putnam-1973-b2-square-witness-down-p
        (numerator x)
        (numerator x))
       (putnam-1973-b2-square-witness-down-p
        (denominator x)
        (denominator x))))

(defun putnambench-putnam-1973-b2-statement (z n)
  (implies
   (and (putnam-1973-b2-complexp z)
        (equal (putnam-1973-b2-norm-squared z) 1)
        (integerp n))
   (putnam-1973-b2-rational-square-p
    (putnam-1973-b2-norm-squared
     (putnam-1973-b2-complex-sub
      (putnam-1973-b2-integer-power z (* 2 n))
      (putnam-1973-b2-complex 1 0))))))

(value-triple :itpeval-statement-checked)
:q
