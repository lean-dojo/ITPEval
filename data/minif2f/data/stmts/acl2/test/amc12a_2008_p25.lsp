;; Statement-only formalization of miniF2F artifact amc12a_2008_p25:
;; arbitrary real-valued sequences satisfying the two recurrences at every
;; natural index, with a(100) = 2 and b(100) = 4, have
;; a(1) + b(1) = 1/2^98. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no first-class real-valued function type. Sequence objects are
;; therefore reified through SEQ-AT, while the arbitrary carrier and all
;; real-closed-field and rational-embedding laws remain explicit theorem
;; premises. This pins the first-order scalar theory to that of the reals
;; instead of admitting arbitrary ordered-ring countermodels.

(defstub amc08-real-p (real-type value) t)
(defstub amc08-zero (real-type) t)
(defstub amc08-one (real-type) t)
(defstub amc08-add (real-type left right) t)
(defstub amc08-mul (real-type left right) t)
(defstub amc08-neg (real-type value) t)
(defstub amc08-inv (real-type value) t)
(defstub amc08-le (real-type left right) t)
(defstub amc08-of-rational (real-type rational) t)
(defstub amc08-seq-at (real-type sequence index) t)

(defun amc08-sub (real-type x y)
  (amc08-add real-type x (amc08-neg real-type y)))

(defun amc08-square (real-type x)
  (amc08-mul real-type x x))

(defun-sk amc08-closure-laws-p (real-type)
  (forall (x y)
    (and
     (amc08-real-p real-type (amc08-zero real-type))
     (amc08-real-p real-type (amc08-one real-type))
     (implies
      (amc08-real-p real-type x)
      (and
       (amc08-real-p real-type (amc08-neg real-type x))
       (amc08-real-p real-type (amc08-inv real-type x))))
     (implies
      (and
       (amc08-real-p real-type x)
       (amc08-real-p real-type y))
      (and
       (amc08-real-p real-type (amc08-add real-type x y))
       (amc08-real-p real-type (amc08-mul real-type x y)))))))

(defun-sk amc08-ring-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc08-real-p real-type x)
      (amc08-real-p real-type y)
      (amc08-real-p real-type z))
     (let ((zero (amc08-zero real-type))
           (one (amc08-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (amc08-add real-type x y)
         (amc08-add real-type y x))
        (equal
         (amc08-add real-type (amc08-add real-type x y) z)
         (amc08-add real-type x (amc08-add real-type y z)))
        (equal (amc08-add real-type x zero) x)
        (equal
         (amc08-add real-type x (amc08-neg real-type x))
         zero)
        (equal
         (amc08-mul real-type x y)
         (amc08-mul real-type y x))
        (equal
         (amc08-mul real-type (amc08-mul real-type x y) z)
         (amc08-mul real-type x (amc08-mul real-type y z)))
        (equal (amc08-mul real-type x one) x)
        (equal
         (amc08-mul
          real-type
          x
          (amc08-add real-type y z))
        (amc08-add
          real-type
          (amc08-mul real-type x y)
          (amc08-mul real-type x z))))))))

(defun-sk amc08-inverse-laws-p (real-type)
  (forall (x)
    (implies
     (amc08-real-p real-type x)
     (let ((zero (amc08-zero real-type))
           (one (amc08-one real-type)))
       (and
        (equal (amc08-inv real-type zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (amc08-mul real-type x (amc08-inv real-type x))
          one)))))))

(defun-sk amc08-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (amc08-real-p real-type x)
      (amc08-real-p real-type y)
      (amc08-real-p real-type z))
     (let ((zero (amc08-zero real-type)))
       (and
        (amc08-le real-type x x)
        (implies
         (and
          (amc08-le real-type x y)
          (amc08-le real-type y x))
         (equal x y))
        (implies
         (and
          (amc08-le real-type x y)
          (amc08-le real-type y z))
         (amc08-le real-type x z))
        (or
         (amc08-le real-type x y)
         (amc08-le real-type y x))
        (implies
         (amc08-le real-type x y)
         (amc08-le
          real-type
          (amc08-add real-type x z)
          (amc08-add real-type y z)))
        (implies
         (and
          (amc08-le real-type zero x)
          (amc08-le real-type zero y))
         (amc08-le
          real-type
          zero
          (amc08-mul real-type x y))))))))

(defun-sk amc08-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (amc08-real-p
       real-type (amc08-of-rational real-type p))
      (equal
       (amc08-of-rational real-type 0)
       (amc08-zero real-type))
      (equal
       (amc08-of-rational real-type 1)
       (amc08-one real-type))
      (equal
       (amc08-of-rational real-type (+ p q))
       (amc08-add
        real-type
        (amc08-of-rational real-type p)
        (amc08-of-rational real-type q)))
      (equal
       (amc08-of-rational real-type (* p q))
       (amc08-mul
        real-type
        (amc08-of-rational real-type p)
        (amc08-of-rational real-type q)))
      (equal
       (amc08-of-rational real-type (- p))
       (amc08-neg
        real-type
        (amc08-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (amc08-of-rational real-type p)
        (amc08-of-rational real-type q)))
      (iff
       (<= p q)
       (amc08-le
        real-type
        (amc08-of-rational real-type p)
        (amc08-of-rational real-type q)))))))

(defun amc08-nonnegative-p (real-type x)
  (and
   (amc08-real-p real-type x)
   (amc08-le real-type (amc08-zero real-type) x)))

(defun amc08-polynomial-p (real-type coefficients)
  (if (endp coefficients)
      t
    (and
     (amc08-real-p real-type (car coefficients))
     (amc08-polynomial-p real-type (cdr coefficients)))))

(defun amc08-polynomial-value (real-type coefficients x)
  (if (endp coefficients)
      (amc08-zero real-type)
    (amc08-add
     real-type
     (car coefficients)
     (amc08-mul
      real-type
      x
      (amc08-polynomial-value
       real-type (cdr coefficients) x)))))

(defun amc08-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (amc08-leading-coefficient (cdr coefficients))))

(defun amc08-odd-degree-p (real-type coefficients)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (amc08-leading-coefficient coefficients)
     (amc08-zero real-type)))
   (equal (mod (1- (len coefficients)) 2) 1)))

(defun-sk amc08-square-root-exists-p (real-type x)
  (exists (root)
    (and
     (amc08-nonnegative-p real-type root)
     (equal
      (amc08-mul real-type root root)
      x))))

(defun-sk amc08-positive-square-roots-p (real-type)
  (forall (x)
    (implies
     (and
      (amc08-real-p real-type x)
      (amc08-le real-type (amc08-zero real-type) x))
     (amc08-square-root-exists-p real-type x))))

(defun-sk amc08-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (amc08-real-p real-type root)
     (equal
      (amc08-polynomial-value real-type coefficients root)
      (amc08-zero real-type)))))

(defun-sk amc08-odd-polynomial-roots-p (real-type)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (amc08-polynomial-p real-type coefficients)
      (amc08-odd-degree-p real-type coefficients))
     (amc08-polynomial-root-exists-p
      real-type coefficients))))

(defun amc08-real-structure-p (real-type)
  (and
   (amc08-closure-laws-p real-type)
   (amc08-ring-laws-p real-type)
   (amc08-inverse-laws-p real-type)
   (amc08-order-laws-p real-type)
   (amc08-rational-laws-p real-type)
   (amc08-positive-square-roots-p real-type)
   (amc08-odd-polynomial-roots-p real-type)))

(defun-sk amc08-real-sequence-p (real-type sequence)
  (forall (n)
    (implies
     (natp n)
     (amc08-real-p
      real-type
      (amc08-seq-at real-type sequence n)))))

(defun-sk amc08-recurrences-p
    (real-type sqrt-three a-sequence b-sequence)
  (forall (n)
    (implies
     (natp n)
     (and
      (equal
       (amc08-seq-at real-type a-sequence (+ n 1))
       (amc08-sub
        real-type
        (amc08-mul
         real-type
         sqrt-three
         (amc08-seq-at real-type a-sequence n))
        (amc08-seq-at real-type b-sequence n)))
      (equal
       (amc08-seq-at real-type b-sequence (+ n 1))
       (amc08-add
        real-type
        (amc08-mul
         real-type
         sqrt-three
         (amc08-seq-at real-type b-sequence n))
        (amc08-seq-at real-type a-sequence n)))))))

(defun-sk amc12a-2008-p25-statement ()
  (forall (real-type sqrt-three a-sequence b-sequence)
    (implies
     (and
      (amc08-real-structure-p real-type)
      (amc08-real-p real-type sqrt-three)
      (amc08-le
       real-type (amc08-zero real-type) sqrt-three)
      (equal
       (amc08-square real-type sqrt-three)
       (amc08-of-rational real-type 3))
      (amc08-real-sequence-p real-type a-sequence)
      (amc08-real-sequence-p real-type b-sequence)
      (amc08-recurrences-p
       real-type sqrt-three a-sequence b-sequence)
      (equal
       (amc08-seq-at real-type a-sequence 100)
       (amc08-of-rational real-type 2))
      (equal
       (amc08-seq-at real-type b-sequence 100)
       (amc08-of-rational real-type 4)))
     (equal
      (amc08-add
       real-type
       (amc08-seq-at real-type a-sequence 1)
       (amc08-seq-at real-type b-sequence 1))
      (amc08-of-rational
       real-type
       (/ 1 (expt 2 98)))))))

(value-triple :itpeval-statement-checked)
:q
