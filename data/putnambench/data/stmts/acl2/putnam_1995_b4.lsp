;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_b4:
;; evaluation of a positive continued-fraction fixed point's real eighth root
;; as (3 + sqrt(5))/2. This file contains no proof.

(in-package "ACL2")

;; A dotted pair (a . b) of rationals denotes a + b*sqrt(5). Since sqrt(5)
;; is irrational, equality of denoted reals is exactly componentwise equality.
(defun putnam-1995-b4-quad5-p (x)
  (and (consp x)
       (rationalp (car x))
       (rationalp (cdr x))))

(defun putnam-1995-b4-quad5-add (x y)
  (cons (+ (car x) (car y))
        (+ (cdr x) (cdr y))))

(defun putnam-1995-b4-quad5-neg (x)
  (cons (- (car x))
        (- (cdr x))))

(defun putnam-1995-b4-quad5-sub (x y)
  (putnam-1995-b4-quad5-add
   x (putnam-1995-b4-quad5-neg y)))

(defun putnam-1995-b4-quad5-scale (c x)
  (cons (* c (car x))
        (* c (cdr x))))

(defun putnam-1995-b4-quad5-mul (x y)
  (cons (+ (* (car x) (car y))
           (* 5 (cdr x) (cdr y)))
        (+ (* (car x) (cdr y))
           (* (cdr x) (car y)))))

(defun putnam-1995-b4-quad5-pow (x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons 1 0)
    (putnam-1995-b4-quad5-mul
     x
     (putnam-1995-b4-quad5-pow x (- n 1)))))

;; This is the exact order test a + b*sqrt(5) > 0. When a and b have
;; opposite signs, squaring is sound after the displayed sign checks.
(defun putnam-1995-b4-quad5-positive-p (x)
  (let ((a (car x))
        (b (cdr x)))
    (cond
     ((equal b 0)
      (< 0 a))
     ((< 0 b)
      (or (<= 0 a)
          (< (* a a) (* 5 b b))))
     (t
      (and (< 0 a)
           (< (* 5 b b) (* a a)))))))

(defun putnam-1995-b4-fixed-point-polynomial (x)
  (putnam-1995-b4-quad5-add
   (putnam-1995-b4-quad5-sub
    (putnam-1995-b4-quad5-mul x x)
    (putnam-1995-b4-quad5-scale 2207 x))
   (cons 1 0)))

(defun putnam-1995-b4-solution ()
  (cons (/ 3 2) (/ 1 2)))

;; Under contfrac > 1, the source equation
;;
;;   contfrac = 2207 - 1/contfrac
;;
;; is equivalent to contfrac^2 - 2207*contfrac + 1 = 0. Its discriminant is
;; 2207^2 - 4 = 5*987^2, so every satisfying real contfrac lies in Q(sqrt(5))
;; and has an exact pair above; conversely every pair denotes a real number.
;; The solution y=(3+sqrt(5))/2 is positive. Therefore the source conclusion
;; contfrac^(1/8)=y is equivalent to contfrac=y^8, which is expressed exactly
;; by the integer field power below.
(defun putnambench-putnam-1995-b4-statement (contfrac)
  (implies
   (and
    (putnam-1995-b4-quad5-p contfrac)
    (equal
     (putnam-1995-b4-fixed-point-polynomial contfrac)
     (cons 0 0))
    (putnam-1995-b4-quad5-positive-p
     (putnam-1995-b4-quad5-sub contfrac (cons 1 0))))
   (equal
    contfrac
    (putnam-1995-b4-quad5-pow
     (putnam-1995-b4-solution)
     8))))

(value-triple :itpeval-statement-checked)
:q
