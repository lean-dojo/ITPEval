;; Statement-only formalization of miniF2F artifact mathd_algebra_104:
;; over the real numbers, 125/8 = x/12 implies x = 375/2.
;; This file contains no proof.
;;
;; Ordinary ACL2 does not have the full real field as a native first-class
;; domain. The arbitrary carrier below has every ordered-field law and its
;; injective rational embedding stated explicitly in the antecedent. Hence x
;; is not restricted to ACL2's rationals, and the real field is an instance
;; of the represented structure.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd104-real-p (real-type value) t)
(defstub mathd104-zero (real-type) t)
(defstub mathd104-one (real-type) t)
(defstub mathd104-add (real-type left right) t)
(defstub mathd104-mul (real-type left right) t)
(defstub mathd104-neg (real-type value) t)
(defstub mathd104-inv (real-type value) t)
(defstub mathd104-le (real-type left right) t)
(defstub mathd104-of-rational (real-type rational) t)

(defun mathd104-div (real-type left right)
  (mathd104-mul
   real-type left (mathd104-inv real-type right)))

(defun-sk mathd104-closure-laws-p (real-type)
  (forall (x y)
    (and
     (mathd104-real-p real-type (mathd104-zero real-type))
     (mathd104-real-p real-type (mathd104-one real-type))
     (implies
      (mathd104-real-p real-type x)
      (and
       (mathd104-real-p
        real-type (mathd104-neg real-type x))
       (mathd104-real-p
        real-type (mathd104-inv real-type x))))
     (implies
      (and
       (mathd104-real-p real-type x)
       (mathd104-real-p real-type y))
      (and
       (mathd104-real-p
        real-type (mathd104-add real-type x y))
       (mathd104-real-p
        real-type (mathd104-mul real-type x y)))))))

(defun-sk mathd104-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd104-real-p real-type x)
      (mathd104-real-p real-type y)
      (mathd104-real-p real-type z))
     (let ((zero (mathd104-zero real-type))
           (one (mathd104-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (mathd104-add real-type x y)
         (mathd104-add real-type y x))
        (equal
         (mathd104-add
          real-type (mathd104-add real-type x y) z)
         (mathd104-add
          real-type x (mathd104-add real-type y z)))
        (equal (mathd104-add real-type x zero) x)
        (equal
         (mathd104-add
          real-type x (mathd104-neg real-type x))
         zero)
        (equal
         (mathd104-mul real-type x y)
         (mathd104-mul real-type y x))
        (equal
         (mathd104-mul
          real-type (mathd104-mul real-type x y) z)
         (mathd104-mul
          real-type x (mathd104-mul real-type y z)))
        (equal (mathd104-mul real-type x one) x)
        (equal
         (mathd104-mul
          real-type x (mathd104-add real-type y z))
         (mathd104-add
          real-type
          (mathd104-mul real-type x y)
          (mathd104-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd104-mul
           real-type x (mathd104-inv real-type x))
          one)))))))

(defun-sk mathd104-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd104-real-p real-type x)
      (mathd104-real-p real-type y)
      (mathd104-real-p real-type z))
     (let ((zero (mathd104-zero real-type)))
       (and
        (mathd104-le real-type x x)
        (implies
         (and
          (mathd104-le real-type x y)
          (mathd104-le real-type y x))
         (equal x y))
        (implies
         (and
          (mathd104-le real-type x y)
          (mathd104-le real-type y z))
         (mathd104-le real-type x z))
        (or
         (mathd104-le real-type x y)
         (mathd104-le real-type y x))
        (implies
         (mathd104-le real-type x y)
         (mathd104-le
          real-type
          (mathd104-add real-type x z)
          (mathd104-add real-type y z)))
        (implies
         (and
          (mathd104-le real-type zero x)
          (mathd104-le real-type zero y))
         (mathd104-le
          real-type
          zero
          (mathd104-mul real-type x y))))))))

(defun-sk mathd104-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd104-real-p
       real-type (mathd104-of-rational real-type p))
      (equal
       (mathd104-of-rational real-type 0)
       (mathd104-zero real-type))
      (equal
       (mathd104-of-rational real-type 1)
       (mathd104-one real-type))
      (equal
       (mathd104-of-rational real-type (+ p q))
       (mathd104-add
        real-type
        (mathd104-of-rational real-type p)
        (mathd104-of-rational real-type q)))
      (equal
       (mathd104-of-rational real-type (* p q))
       (mathd104-mul
        real-type
        (mathd104-of-rational real-type p)
        (mathd104-of-rational real-type q)))
      (equal
       (mathd104-of-rational real-type (- p))
       (mathd104-neg
        real-type
        (mathd104-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (mathd104-of-rational real-type p)
        (mathd104-of-rational real-type q)))
      (iff
       (<= p q)
       (mathd104-le
        real-type
        (mathd104-of-rational real-type p)
        (mathd104-of-rational real-type q)))))))

(defun mathd104-real-structure-p (real-type)
  (and
   (mathd104-closure-laws-p real-type)
   (mathd104-field-laws-p real-type)
   (mathd104-order-laws-p real-type)
   (mathd104-rational-laws-p real-type)))

(defun-sk mathd-algebra-104-statement ()
  (forall (real-type x)
    (implies
     (and
      (mathd104-real-structure-p real-type)
      (mathd104-real-p real-type x)
      (equal
       (mathd104-of-rational real-type 125/8)
       (mathd104-div
        real-type
        x
        (mathd104-of-rational real-type 12))))
     (equal
      x
      (mathd104-of-rational real-type 375/2)))))

(value-triple :itpeval-statement-checked)
:q
