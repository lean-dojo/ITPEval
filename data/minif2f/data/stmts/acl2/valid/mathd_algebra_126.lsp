;; Statement-only formalization of miniF2F artifact mathd_algebra_126:
;; over the real numbers, 2*3 = x - 9 and 2*(-5) = y + 1 imply
;; x = 15 and y = -11. This file contains no proof.
;;
;; The arbitrary ordered-field carrier and injective rational embedding make
;; the source's real quantifiers explicit instead of replacing them by
;; rationalp guards.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd126-real-p (real-type value) t)
(defstub mathd126-zero (real-type) t)
(defstub mathd126-one (real-type) t)
(defstub mathd126-add (real-type left right) t)
(defstub mathd126-mul (real-type left right) t)
(defstub mathd126-neg (real-type value) t)
(defstub mathd126-inv (real-type value) t)
(defstub mathd126-le (real-type left right) t)
(defstub mathd126-of-rational (real-type rational) t)

(defun mathd126-sub (real-type left right)
  (mathd126-add
   real-type left (mathd126-neg real-type right)))

(defun-sk mathd126-closure-laws-p (real-type)
  (forall (x y)
    (and
     (mathd126-real-p real-type (mathd126-zero real-type))
     (mathd126-real-p real-type (mathd126-one real-type))
     (implies
      (mathd126-real-p real-type x)
      (and
       (mathd126-real-p
        real-type (mathd126-neg real-type x))
       (mathd126-real-p
        real-type (mathd126-inv real-type x))))
     (implies
      (and
       (mathd126-real-p real-type x)
       (mathd126-real-p real-type y))
      (and
       (mathd126-real-p
        real-type (mathd126-add real-type x y))
       (mathd126-real-p
        real-type (mathd126-mul real-type x y)))))))

(defun-sk mathd126-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd126-real-p real-type x)
      (mathd126-real-p real-type y)
      (mathd126-real-p real-type z))
     (let ((zero (mathd126-zero real-type))
           (one (mathd126-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (mathd126-add real-type x y)
         (mathd126-add real-type y x))
        (equal
         (mathd126-add
          real-type (mathd126-add real-type x y) z)
         (mathd126-add
          real-type x (mathd126-add real-type y z)))
        (equal (mathd126-add real-type x zero) x)
        (equal
         (mathd126-add
          real-type x (mathd126-neg real-type x))
         zero)
        (equal
         (mathd126-mul real-type x y)
         (mathd126-mul real-type y x))
        (equal
         (mathd126-mul
          real-type (mathd126-mul real-type x y) z)
         (mathd126-mul
          real-type x (mathd126-mul real-type y z)))
        (equal (mathd126-mul real-type x one) x)
        (equal
         (mathd126-mul
          real-type x (mathd126-add real-type y z))
         (mathd126-add
          real-type
          (mathd126-mul real-type x y)
          (mathd126-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd126-mul
           real-type x (mathd126-inv real-type x))
          one)))))))

(defun-sk mathd126-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd126-real-p real-type x)
      (mathd126-real-p real-type y)
      (mathd126-real-p real-type z))
     (let ((zero (mathd126-zero real-type)))
       (and
        (mathd126-le real-type x x)
        (implies
         (and
          (mathd126-le real-type x y)
          (mathd126-le real-type y x))
         (equal x y))
        (implies
         (and
          (mathd126-le real-type x y)
          (mathd126-le real-type y z))
         (mathd126-le real-type x z))
        (or
         (mathd126-le real-type x y)
         (mathd126-le real-type y x))
        (implies
         (mathd126-le real-type x y)
         (mathd126-le
          real-type
          (mathd126-add real-type x z)
          (mathd126-add real-type y z)))
        (implies
         (and
          (mathd126-le real-type zero x)
          (mathd126-le real-type zero y))
         (mathd126-le
          real-type
          zero
          (mathd126-mul real-type x y))))))))

(defun-sk mathd126-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd126-real-p
       real-type (mathd126-of-rational real-type p))
      (equal
       (mathd126-of-rational real-type 0)
       (mathd126-zero real-type))
      (equal
       (mathd126-of-rational real-type 1)
       (mathd126-one real-type))
      (equal
       (mathd126-of-rational real-type (+ p q))
       (mathd126-add
        real-type
        (mathd126-of-rational real-type p)
        (mathd126-of-rational real-type q)))
      (equal
       (mathd126-of-rational real-type (* p q))
       (mathd126-mul
        real-type
        (mathd126-of-rational real-type p)
        (mathd126-of-rational real-type q)))
      (equal
       (mathd126-of-rational real-type (- p))
       (mathd126-neg
        real-type
        (mathd126-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (mathd126-of-rational real-type p)
        (mathd126-of-rational real-type q)))
      (iff
       (<= p q)
       (mathd126-le
        real-type
        (mathd126-of-rational real-type p)
        (mathd126-of-rational real-type q)))))))

(defun mathd126-real-structure-p (real-type)
  (and
   (mathd126-closure-laws-p real-type)
   (mathd126-field-laws-p real-type)
   (mathd126-order-laws-p real-type)
   (mathd126-rational-laws-p real-type)))

(defun-sk mathd-algebra-126-statement ()
  (forall (real-type x y)
    (implies
     (and
      (mathd126-real-structure-p real-type)
      (mathd126-real-p real-type x)
      (mathd126-real-p real-type y)
      (equal
       (mathd126-mul
        real-type
        (mathd126-of-rational real-type 2)
        (mathd126-of-rational real-type 3))
       (mathd126-sub
        real-type
        x
        (mathd126-of-rational real-type 9)))
      (equal
       (mathd126-mul
        real-type
        (mathd126-of-rational real-type 2)
        (mathd126-of-rational real-type -5))
       (mathd126-add
        real-type
        y
        (mathd126-of-rational real-type 1))))
     (and
      (equal
       x
       (mathd126-of-rational real-type 15))
      (equal
       y
       (mathd126-of-rational real-type -11))))))

(value-triple :itpeval-statement-checked)
:q
