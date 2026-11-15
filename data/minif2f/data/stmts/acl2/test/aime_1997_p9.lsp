;; Statement-only formalization of miniF2F artifact aime_1997_p9:
;; for every positive real a, equality of the fractional parts of 1/a and
;; a^2, together with 2 < a^2 < 3, implies
;; a^12 - 144*(1/a) = 233. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no built-in first-class real field. The arbitrary carrier below
;; is constrained through explicit ordered-field, rational-embedding, and
;; floor laws in the theorem antecedent.

(defstub aime-1997-p9-real-p (real-type value) t)
(defstub aime-1997-p9-zero (real-type) t)
(defstub aime-1997-p9-one (real-type) t)
(defstub aime-1997-p9-add (real-type left right) t)
(defstub aime-1997-p9-mul (real-type left right) t)
(defstub aime-1997-p9-neg (real-type value) t)
(defstub aime-1997-p9-inv (real-type value) t)
(defstub aime-1997-p9-le (real-type left right) t)
(defstub aime-1997-p9-of-rational (real-type rational) t)
(defstub aime-1997-p9-floor (real-type value) t)

(defun aime-1997-p9-sub (real-type x y)
  (aime-1997-p9-add
   real-type x (aime-1997-p9-neg real-type y)))

(defun aime-1997-p9-lt (real-type x y)
  (and
   (aime-1997-p9-le real-type x y)
   (not (equal x y))))

(defun aime-1997-p9-pow (real-type value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (aime-1997-p9-one real-type)
    (aime-1997-p9-mul
     real-type
     value
     (aime-1997-p9-pow real-type value (1- exponent)))))

(defun-sk aime-1997-p9-closure-laws-p (real-type)
  (forall (x y)
    (and
     (aime-1997-p9-real-p
      real-type (aime-1997-p9-zero real-type))
     (aime-1997-p9-real-p
      real-type (aime-1997-p9-one real-type))
     (implies
      (aime-1997-p9-real-p real-type x)
      (and
       (aime-1997-p9-real-p
        real-type (aime-1997-p9-neg real-type x))
       (aime-1997-p9-real-p
        real-type (aime-1997-p9-inv real-type x))))
     (implies
      (and
       (aime-1997-p9-real-p real-type x)
       (aime-1997-p9-real-p real-type y))
      (and
       (aime-1997-p9-real-p
        real-type (aime-1997-p9-add real-type x y))
       (aime-1997-p9-real-p
        real-type (aime-1997-p9-mul real-type x y)))))))

(defun-sk aime-1997-p9-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (aime-1997-p9-real-p real-type x)
      (aime-1997-p9-real-p real-type y)
      (aime-1997-p9-real-p real-type z))
     (let ((zero (aime-1997-p9-zero real-type))
           (one (aime-1997-p9-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (aime-1997-p9-add real-type x y)
         (aime-1997-p9-add real-type y x))
        (equal
         (aime-1997-p9-add
          real-type
          (aime-1997-p9-add real-type x y)
          z)
         (aime-1997-p9-add
          real-type
          x
          (aime-1997-p9-add real-type y z)))
        (equal (aime-1997-p9-add real-type x zero) x)
        (equal
         (aime-1997-p9-add
          real-type x (aime-1997-p9-neg real-type x))
         zero)
        (equal
         (aime-1997-p9-mul real-type x y)
         (aime-1997-p9-mul real-type y x))
        (equal
         (aime-1997-p9-mul
          real-type
          (aime-1997-p9-mul real-type x y)
          z)
         (aime-1997-p9-mul
          real-type
          x
          (aime-1997-p9-mul real-type y z)))
        (equal (aime-1997-p9-mul real-type x one) x)
        (equal
         (aime-1997-p9-mul
          real-type
          x
          (aime-1997-p9-add real-type y z))
         (aime-1997-p9-add
          real-type
          (aime-1997-p9-mul real-type x y)
          (aime-1997-p9-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (aime-1997-p9-mul
           real-type x (aime-1997-p9-inv real-type x))
          one)))))))

(defun-sk aime-1997-p9-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (aime-1997-p9-real-p real-type x)
      (aime-1997-p9-real-p real-type y)
      (aime-1997-p9-real-p real-type z))
     (let ((zero (aime-1997-p9-zero real-type)))
       (and
        (aime-1997-p9-le real-type x x)
        (implies
         (and
          (aime-1997-p9-le real-type x y)
          (aime-1997-p9-le real-type y x))
         (equal x y))
        (implies
         (and
          (aime-1997-p9-le real-type x y)
          (aime-1997-p9-le real-type y z))
         (aime-1997-p9-le real-type x z))
        (or
         (aime-1997-p9-le real-type x y)
         (aime-1997-p9-le real-type y x))
        (implies
         (aime-1997-p9-le real-type x y)
         (aime-1997-p9-le
          real-type
          (aime-1997-p9-add real-type x z)
          (aime-1997-p9-add real-type y z)))
        (implies
         (and
          (aime-1997-p9-le real-type zero x)
          (aime-1997-p9-le real-type zero y))
         (aime-1997-p9-le
          real-type
          zero
          (aime-1997-p9-mul real-type x y))))))))

(defun-sk aime-1997-p9-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (aime-1997-p9-real-p
       real-type (aime-1997-p9-of-rational real-type p))
      (equal
       (aime-1997-p9-of-rational real-type 0)
       (aime-1997-p9-zero real-type))
      (equal
       (aime-1997-p9-of-rational real-type 1)
       (aime-1997-p9-one real-type))
      (equal
       (aime-1997-p9-of-rational real-type (+ p q))
       (aime-1997-p9-add
        real-type
        (aime-1997-p9-of-rational real-type p)
        (aime-1997-p9-of-rational real-type q)))
      (equal
       (aime-1997-p9-of-rational real-type (* p q))
       (aime-1997-p9-mul
        real-type
        (aime-1997-p9-of-rational real-type p)
        (aime-1997-p9-of-rational real-type q)))
      (equal
       (aime-1997-p9-of-rational real-type (- p))
       (aime-1997-p9-neg
        real-type
        (aime-1997-p9-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (aime-1997-p9-of-rational real-type p)
        (aime-1997-p9-of-rational real-type q)))
      (iff
       (<= p q)
       (aime-1997-p9-le
        real-type
        (aime-1997-p9-of-rational real-type p)
        (aime-1997-p9-of-rational real-type q)))))))

(defun-sk aime-1997-p9-floor-laws-p (real-type)
  (forall (x)
    (implies
     (aime-1997-p9-real-p real-type x)
     (let ((floor-x (aime-1997-p9-floor real-type x)))
       (and
        (integerp floor-x)
        (aime-1997-p9-le
         real-type
         (aime-1997-p9-of-rational real-type floor-x)
         x)
        (aime-1997-p9-lt
         real-type
         x
         (aime-1997-p9-of-rational
          real-type (+ floor-x 1))))))))

(defun aime-1997-p9-real-structure-p (real-type)
  (and
   (aime-1997-p9-closure-laws-p real-type)
   (aime-1997-p9-field-laws-p real-type)
   (aime-1997-p9-order-laws-p real-type)
   (aime-1997-p9-rational-laws-p real-type)
   (aime-1997-p9-floor-laws-p real-type)))

(defun aime-1997-p9-fractional-part (real-type x)
  (aime-1997-p9-sub
   real-type
   x
   (aime-1997-p9-of-rational
    real-type
    (aime-1997-p9-floor real-type x))))

(defun-sk aime-1997-p9-statement ()
  (forall (real-type a)
    (let* ((zero (aime-1997-p9-zero real-type))
           (a-inverse (aime-1997-p9-inv real-type a))
           (a-squared (aime-1997-p9-pow real-type a 2)))
      (implies
       (and
        (aime-1997-p9-real-structure-p real-type)
        (aime-1997-p9-real-p real-type a)
        (aime-1997-p9-lt real-type zero a)
        (equal
         (aime-1997-p9-fractional-part real-type a-inverse)
         (aime-1997-p9-fractional-part real-type a-squared))
        (aime-1997-p9-lt
         real-type
         (aime-1997-p9-of-rational real-type 2)
         a-squared)
        (aime-1997-p9-lt
         real-type
         a-squared
         (aime-1997-p9-of-rational real-type 3)))
       (equal
        (aime-1997-p9-sub
         real-type
         (aime-1997-p9-pow real-type a 12)
         (aime-1997-p9-mul
          real-type
          (aime-1997-p9-of-rational real-type 144)
          a-inverse))
        (aime-1997-p9-of-rational real-type 233))))))

(value-triple :itpeval-statement-checked)
:q
