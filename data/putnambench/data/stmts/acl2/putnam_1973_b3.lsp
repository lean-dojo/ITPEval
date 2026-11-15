;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_b3:
;; a natural p whose values x^2-x+p are prime for every natural x<p has
;; exactly one reduced integer triple of discriminant 1-4p. This file contains
;; no proof.

(in-package "ACL2")

(defun putnam-1973-b3-no-divisor-down-p (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod n candidate) 0))
     (putnam-1973-b3-no-divisor-down-p
      n (- candidate 1)))))

(defun putnam-1973-b3-prime-p (n)
  (and
   (natp n)
   (< 1 n)
   (putnam-1973-b3-no-divisor-down-p
    n (- n 1))))

;; Descending count p examines exactly x=0,...,p-1. For natural x,
;; x^2-x is nonnegative, so ACL2 integer subtraction agrees with the source
;; natural-number subtraction.
(defun putnam-1973-b3-polynomial-prime-range-p (p count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((x (- count 1)))
      (and
       (putnam-1973-b3-prime-p
        (+ (- (* x x) x) p))
       (putnam-1973-b3-polynomial-prime-range-p
        p x)))))

(defun putnam-1973-b3-reduced-triple-p (p a b c)
  (and
   (natp p)
   (integerp a)
   (integerp b)
   (integerp c)
   (equal
    (- (* b b) (* 4 a c))
    (- 1 (* 4 p)))
   (< 0 a)
   (<= a c)
   (<= (- a) b)
   (< b a)))

;; For any source triple, b^2 <= a^2 and
;; 4*a*c=b^2+4*p-1. Since c>=a, this gives a<=p; then
;; (a-1)*(4*p-a-1)>=0 gives c<=p. Thus the finite ranges below contain every
;; and only possible source triple, and count=1 is equivalent to exists-unique.

(defun putnam-1973-b3-count-c (p a b count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((c (+ a (- count 1))))
      (+
       (if (putnam-1973-b3-reduced-triple-p p a b c)
           1
         0)
       (putnam-1973-b3-count-c
        p a b (- count 1))))))

(defun putnam-1973-b3-count-b (p a count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((b (- (- count 1) a)))
      (+
       (putnam-1973-b3-count-c
        p a b (+ (- p a) 1))
       (putnam-1973-b3-count-b
        p a (- count 1))))))

(defun putnam-1973-b3-count-a (p count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((a count))
      (+
       (putnam-1973-b3-count-b
        p a (* 2 a))
       (putnam-1973-b3-count-a
        p (- count 1))))))

(defun putnambench-putnam-1973-b3-statement (p)
  (implies
   (and
    (natp p)
    (< 1 p)
    (putnam-1973-b3-polynomial-prime-range-p
     p p))
   (equal
    (putnam-1973-b3-count-a p p)
    1)))

(value-triple :itpeval-statement-checked)
:q
