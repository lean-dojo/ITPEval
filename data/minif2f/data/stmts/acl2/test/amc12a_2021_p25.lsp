;; Statement-only formalization of miniF2F artifact amc12a_2021_p25:
;; if a positive natural N is the unique strict maximizer of the divisor
;; count divided by the positive real cube root, then its decimal digits sum
;; to 9. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no native complete real field. The arbitrary real-closed ordered
;; field, natural embedding, cube-root operation, and function f below remain
;; explicit theorem premises. In particular, the global maximization hypothesis
;; is quantified over every positive natural; it is not replaced by a
;; theorem-specific finite search or by N = 2520.

(defstub amc21p25-real-p (real-type value) t)
(defstub amc21p25-zero (real-type) t)
(defstub amc21p25-one (real-type) t)
(defstub amc21p25-add (real-type left right) t)
(defstub amc21p25-mul (real-type left right) t)
(defstub amc21p25-neg (real-type value) t)
(defstub amc21p25-inv (real-type value) t)
(defstub amc21p25-le (real-type left right) t)
(defstub amc21p25-of-rational (real-type rational) t)
(defstub amc21p25-cube-root (real-type value) t)
(defstub amc21p25-f (real-type n) t)

(defun amc21p25-div (real-type x y)
  (amc21p25-mul real-type x (amc21p25-inv real-type y)))

(defun amc21p25-lt (real-type x y)
  (and
   (amc21p25-le real-type x y)
   (not (equal x y))))

(defun amc21p25-positive-p (real-type x)
  (and
   (amc21p25-real-p real-type x)
   (amc21p25-lt real-type (amc21p25-zero real-type) x)))

(defun amc21p25-cube (real-type x)
  (amc21p25-mul
   real-type
   x
   (amc21p25-mul real-type x x)))

(defun amc21p25-divisor-count-through (n d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod n d) 0) 1 0)
       (amc21p25-divisor-count-through n (- d 1)))))

(defun amc21p25-divisor-count (n)
  (if (and (natp n) (< 0 n))
      (amc21p25-divisor-count-through n n)
    0))

(defun amc21p25-digit-sum-aux (fuel n)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (zp n))
      0
    (+ (mod n 10)
       (amc21p25-digit-sum-aux
        (- fuel 1)
        (floor n 10)))))

(defun amc21p25-digit-sum (n)
  (if (natp n)
      (amc21p25-digit-sum-aux (+ n 1) n)
    0))

(defun-sk amc21p25-closure-laws-p (real-type)
  (forall (x y)
    (and
     (amc21p25-real-p real-type (amc21p25-zero real-type))
     (amc21p25-real-p real-type (amc21p25-one real-type))
     (implies
      (amc21p25-real-p real-type x)
      (and
       (amc21p25-real-p real-type (amc21p25-neg real-type x))
       (amc21p25-real-p real-type (amc21p25-inv real-type x))
       (amc21p25-real-p real-type (amc21p25-cube-root real-type x))))
     (implies
      (and
       (amc21p25-real-p real-type x)
       (amc21p25-real-p real-type y))
      (and
       (amc21p25-real-p
        real-type
        (amc21p25-add real-type x y))
       (amc21p25-real-p
        real-type
        (amc21p25-mul real-type x y)))))))

(defun-sk amc21p25-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc21p25-real-p real-type x)
      (amc21p25-real-p real-type y)
      (amc21p25-real-p real-type z))
     (let ((zero (amc21p25-zero real-type))
           (one (amc21p25-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (amc21p25-add
          real-type (amc21p25-add real-type x y) z)
         (amc21p25-add
          real-type x (amc21p25-add real-type y z)))
        (equal
         (amc21p25-add real-type x y)
         (amc21p25-add real-type y x))
        (equal (amc21p25-add real-type x zero) x)
        (equal
         (amc21p25-add real-type x (amc21p25-neg real-type x))
         zero)
        (equal
         (amc21p25-mul real-type x y)
         (amc21p25-mul real-type y x))
        (equal
         (amc21p25-mul real-type (amc21p25-mul real-type x y) z)
         (amc21p25-mul real-type x (amc21p25-mul real-type y z)))
        (equal (amc21p25-mul real-type x one) x)
        (equal (amc21p25-mul real-type x zero) zero)
        (equal (amc21p25-inv real-type zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (amc21p25-mul real-type x (amc21p25-inv real-type x))
          one))
        (equal
         (amc21p25-mul
          real-type x (amc21p25-add real-type y z))
         (amc21p25-add
          real-type
          (amc21p25-mul real-type x y)
          (amc21p25-mul real-type x z))))))))

(defun-sk amc21p25-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc21p25-real-p real-type x)
      (amc21p25-real-p real-type y)
      (amc21p25-real-p real-type z))
     (let ((zero (amc21p25-zero real-type)))
       (and
        (amc21p25-le real-type x x)
        (implies
         (and
          (amc21p25-le real-type x y)
          (amc21p25-le real-type y x))
         (equal x y))
        (implies
         (and
          (amc21p25-le real-type x y)
          (amc21p25-le real-type y z))
         (amc21p25-le real-type x z))
        (or
         (amc21p25-le real-type x y)
         (amc21p25-le real-type y x))
        (implies
         (amc21p25-le real-type x y)
         (amc21p25-le
          real-type
          (amc21p25-add real-type x z)
          (amc21p25-add real-type y z)))
        (implies
         (and
          (amc21p25-le real-type zero x)
          (amc21p25-le real-type zero y))
         (amc21p25-le
          real-type
          zero
          (amc21p25-mul real-type x y))))))))

(defun-sk amc21p25-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (amc21p25-real-p
       real-type (amc21p25-of-rational real-type p))
      (equal
       (amc21p25-of-rational real-type 0)
       (amc21p25-zero real-type))
      (equal
       (amc21p25-of-rational real-type 1)
       (amc21p25-one real-type))
      (equal
       (amc21p25-of-rational real-type (+ p q))
       (amc21p25-add
        real-type
        (amc21p25-of-rational real-type p)
        (amc21p25-of-rational real-type q)))
      (equal
       (amc21p25-of-rational real-type (* p q))
       (amc21p25-mul
        real-type
        (amc21p25-of-rational real-type p)
        (amc21p25-of-rational real-type q)))
      (iff
       (equal p q)
       (equal
        (amc21p25-of-rational real-type p)
        (amc21p25-of-rational real-type q)))
      (iff
       (<= p q)
       (amc21p25-le
       real-type
       (amc21p25-of-rational real-type p)
       (amc21p25-of-rational real-type q)))))))

(defun amc21p25-polynomial-p (real-type coefficients)
  (if (endp coefficients)
      t
    (and
     (amc21p25-real-p real-type (car coefficients))
     (amc21p25-polynomial-p real-type (cdr coefficients)))))

(defun amc21p25-polynomial-value
    (real-type coefficients x)
  (if (endp coefficients)
      (amc21p25-zero real-type)
    (amc21p25-add
     real-type
     (car coefficients)
     (amc21p25-mul
      real-type
      x
      (amc21p25-polynomial-value
       real-type (cdr coefficients) x)))))

(defun amc21p25-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc21p25-leading-coefficient (cdr coefficients))))

(defun amc21p25-odd-degree-p (real-type coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc21p25-leading-coefficient coefficients)
     (amc21p25-zero real-type)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc21p25-square-root-exists-p (real-type x)
  (exists (root)
    (and
     (amc21p25-real-p real-type root)
     (amc21p25-le real-type (amc21p25-zero real-type) root)
     (equal (amc21p25-mul real-type root root) x))))

(defun-sk amc21p25-positive-square-roots-p (real-type)
  (forall (x)
    (implies
     (and
      (amc21p25-real-p real-type x)
      (amc21p25-le real-type (amc21p25-zero real-type) x))
     (amc21p25-square-root-exists-p real-type x))))

(defun-sk amc21p25-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (amc21p25-real-p real-type root)
     (equal
      (amc21p25-polynomial-value real-type coefficients root)
      (amc21p25-zero real-type)))))

(defun-sk amc21p25-odd-polynomial-roots-p (real-type)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc21p25-polynomial-p real-type coefficients)
      (amc21p25-odd-degree-p real-type coefficients))
     (amc21p25-polynomial-root-exists-p
      real-type coefficients))))

(defun-sk amc21p25-cube-root-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (amc21p25-positive-p real-type x)
      (amc21p25-positive-p real-type y))
     (and
      (amc21p25-positive-p
       real-type (amc21p25-cube-root real-type x))
      (equal
       (amc21p25-cube
        real-type (amc21p25-cube-root real-type x))
       x)
      (implies
       (equal (amc21p25-cube real-type y) x)
       (equal
        (amc21p25-cube-root real-type x)
        y))))))

(defun amc21p25-real-cube-root-structure-p (real-type)
  (and
   (amc21p25-closure-laws-p real-type)
   (amc21p25-field-laws-p real-type)
   (amc21p25-order-laws-p real-type)
   (amc21p25-rational-laws-p real-type)
   (amc21p25-le
    real-type
    (amc21p25-zero real-type)
    (amc21p25-one real-type))
   (amc21p25-positive-square-roots-p real-type)
   (amc21p25-odd-polynomial-roots-p real-type)
   (amc21p25-cube-root-laws-p real-type)))

(defun amc21p25-divisor-ratio (real-type n)
  (amc21p25-div
   real-type
   (amc21p25-of-rational
    real-type (amc21p25-divisor-count n))
   (amc21p25-cube-root
    real-type (amc21p25-of-rational real-type n))))

(defun-sk amc21p25-function-law-p (real-type)
  (forall (n)
    (implies
     (and (natp n) (< 0 n))
     (equal
      (amc21p25-f real-type n)
      (amc21p25-divisor-ratio real-type n)))))

(defun-sk amc21p25-strict-maximizer-p (real-type n)
  (forall (other)
    (implies
     (and
      (natp other)
      (< 0 other)
      (not (equal other n)))
     (amc21p25-lt
      real-type
      (amc21p25-f real-type other)
      (amc21p25-f real-type n)))))

(defun amc12a-2021-p25-statement (real-type n)
  (implies
   (and
    (amc21p25-real-cube-root-structure-p real-type)
    (natp n)
    (< 0 n)
    (amc21p25-function-law-p real-type)
    (amc21p25-strict-maximizer-p real-type n))
   (equal (amc21p25-digit-sum n) 9)))

(value-triple :itpeval-statement-checked)
:q
