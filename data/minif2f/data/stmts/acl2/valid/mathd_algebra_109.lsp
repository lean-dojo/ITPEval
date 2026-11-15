;; Statement-only formalization of miniF2F artifact mathd_algebra_109:
;; over the real numbers, 3*a + 2*b = 12 and a = 4 imply b = 0.
;; This file contains no proof.
;;
;; The explicitly axiomatized carrier avoids narrowing the two real variables
;; to ACL2 rationals. All field, order, and rational-embedding laws are
;; hypotheses of the statement, so DEFSTUB introduces no hidden assumptions.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd109-real-p (real-type value) t)
(defstub mathd109-zero (real-type) t)
(defstub mathd109-one (real-type) t)
(defstub mathd109-add (real-type left right) t)
(defstub mathd109-mul (real-type left right) t)
(defstub mathd109-neg (real-type value) t)
(defstub mathd109-inv (real-type value) t)
(defstub mathd109-le (real-type left right) t)
(defstub mathd109-of-rational (real-type rational) t)

(defun-sk mathd109-closure-laws-p (real-type)
  (forall (x y)
    (and
     (mathd109-real-p real-type (mathd109-zero real-type))
     (mathd109-real-p real-type (mathd109-one real-type))
     (implies
      (mathd109-real-p real-type x)
      (and
       (mathd109-real-p
        real-type (mathd109-neg real-type x))
       (mathd109-real-p
        real-type (mathd109-inv real-type x))))
     (implies
      (and
       (mathd109-real-p real-type x)
       (mathd109-real-p real-type y))
      (and
       (mathd109-real-p
        real-type (mathd109-add real-type x y))
       (mathd109-real-p
        real-type (mathd109-mul real-type x y)))))))

(defun-sk mathd109-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd109-real-p real-type x)
      (mathd109-real-p real-type y)
      (mathd109-real-p real-type z))
     (let ((zero (mathd109-zero real-type))
           (one (mathd109-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (mathd109-add real-type x y)
         (mathd109-add real-type y x))
        (equal
         (mathd109-add
          real-type (mathd109-add real-type x y) z)
         (mathd109-add
          real-type x (mathd109-add real-type y z)))
        (equal (mathd109-add real-type x zero) x)
        (equal
         (mathd109-add
          real-type x (mathd109-neg real-type x))
         zero)
        (equal
         (mathd109-mul real-type x y)
         (mathd109-mul real-type y x))
        (equal
         (mathd109-mul
          real-type (mathd109-mul real-type x y) z)
         (mathd109-mul
          real-type x (mathd109-mul real-type y z)))
        (equal (mathd109-mul real-type x one) x)
        (equal
         (mathd109-mul
          real-type x (mathd109-add real-type y z))
         (mathd109-add
          real-type
          (mathd109-mul real-type x y)
          (mathd109-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd109-mul
           real-type x (mathd109-inv real-type x))
          one)))))))

(defun-sk mathd109-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd109-real-p real-type x)
      (mathd109-real-p real-type y)
      (mathd109-real-p real-type z))
     (let ((zero (mathd109-zero real-type)))
       (and
        (mathd109-le real-type x x)
        (implies
         (and
          (mathd109-le real-type x y)
          (mathd109-le real-type y x))
         (equal x y))
        (implies
         (and
          (mathd109-le real-type x y)
          (mathd109-le real-type y z))
         (mathd109-le real-type x z))
        (or
         (mathd109-le real-type x y)
         (mathd109-le real-type y x))
        (implies
         (mathd109-le real-type x y)
         (mathd109-le
          real-type
          (mathd109-add real-type x z)
          (mathd109-add real-type y z)))
        (implies
         (and
          (mathd109-le real-type zero x)
          (mathd109-le real-type zero y))
         (mathd109-le
          real-type
          zero
          (mathd109-mul real-type x y))))))))

(defun-sk mathd109-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd109-real-p
       real-type (mathd109-of-rational real-type p))
      (equal
       (mathd109-of-rational real-type 0)
       (mathd109-zero real-type))
      (equal
       (mathd109-of-rational real-type 1)
       (mathd109-one real-type))
      (equal
       (mathd109-of-rational real-type (+ p q))
       (mathd109-add
        real-type
        (mathd109-of-rational real-type p)
        (mathd109-of-rational real-type q)))
      (equal
       (mathd109-of-rational real-type (* p q))
       (mathd109-mul
        real-type
        (mathd109-of-rational real-type p)
        (mathd109-of-rational real-type q)))
      (equal
       (mathd109-of-rational real-type (- p))
       (mathd109-neg
        real-type
        (mathd109-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (mathd109-of-rational real-type p)
        (mathd109-of-rational real-type q)))
      (iff
       (<= p q)
       (mathd109-le
        real-type
        (mathd109-of-rational real-type p)
        (mathd109-of-rational real-type q)))))))

(defun mathd109-real-structure-p (real-type)
  (and
   (mathd109-closure-laws-p real-type)
   (mathd109-field-laws-p real-type)
   (mathd109-order-laws-p real-type)
   (mathd109-rational-laws-p real-type)))

(defun-sk mathd-algebra-109-statement ()
  (forall (real-type a b)
    (implies
     (and
      (mathd109-real-structure-p real-type)
      (mathd109-real-p real-type a)
      (mathd109-real-p real-type b)
      (equal
       (mathd109-add
        real-type
        (mathd109-mul
         real-type
         (mathd109-of-rational real-type 3)
         a)
        (mathd109-mul
         real-type
         (mathd109-of-rational real-type 2)
         b))
       (mathd109-of-rational real-type 12))
      (equal
       a
       (mathd109-of-rational real-type 4)))
     (equal
      b
      (mathd109-zero real-type)))))

(value-triple :itpeval-statement-checked)
:q
