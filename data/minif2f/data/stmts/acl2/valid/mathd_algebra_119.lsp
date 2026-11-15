;; Statement-only formalization of miniF2F artifact mathd_algebra_119:
;; over the real numbers, 2*d = 17*e - 8 and 2*e = d - 9 imply e = 2.
;; This file contains no proof.
;;
;; The source variables range over an arbitrary explicitly axiomatized
;; ordered field with an injective rational embedding. In particular, this
;; includes the real field and does not narrow d and e to ACL2 rationals.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd119-real-p (real-type value) t)
(defstub mathd119-zero (real-type) t)
(defstub mathd119-one (real-type) t)
(defstub mathd119-add (real-type left right) t)
(defstub mathd119-mul (real-type left right) t)
(defstub mathd119-neg (real-type value) t)
(defstub mathd119-inv (real-type value) t)
(defstub mathd119-le (real-type left right) t)
(defstub mathd119-of-rational (real-type rational) t)

(defun mathd119-sub (real-type left right)
  (mathd119-add
   real-type left (mathd119-neg real-type right)))

(defun-sk mathd119-closure-laws-p (real-type)
  (forall (x y)
    (and
     (mathd119-real-p real-type (mathd119-zero real-type))
     (mathd119-real-p real-type (mathd119-one real-type))
     (implies
      (mathd119-real-p real-type x)
      (and
       (mathd119-real-p
        real-type (mathd119-neg real-type x))
       (mathd119-real-p
        real-type (mathd119-inv real-type x))))
     (implies
      (and
       (mathd119-real-p real-type x)
       (mathd119-real-p real-type y))
      (and
       (mathd119-real-p
        real-type (mathd119-add real-type x y))
       (mathd119-real-p
        real-type (mathd119-mul real-type x y)))))))

(defun-sk mathd119-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd119-real-p real-type x)
      (mathd119-real-p real-type y)
      (mathd119-real-p real-type z))
     (let ((zero (mathd119-zero real-type))
           (one (mathd119-one real-type)))
       (and
        (not (equal zero one))
        (equal
         (mathd119-add real-type x y)
         (mathd119-add real-type y x))
        (equal
         (mathd119-add
          real-type (mathd119-add real-type x y) z)
         (mathd119-add
          real-type x (mathd119-add real-type y z)))
        (equal (mathd119-add real-type x zero) x)
        (equal
         (mathd119-add
          real-type x (mathd119-neg real-type x))
         zero)
        (equal
         (mathd119-mul real-type x y)
         (mathd119-mul real-type y x))
        (equal
         (mathd119-mul
          real-type (mathd119-mul real-type x y) z)
         (mathd119-mul
          real-type x (mathd119-mul real-type y z)))
        (equal (mathd119-mul real-type x one) x)
        (equal
         (mathd119-mul
          real-type x (mathd119-add real-type y z))
         (mathd119-add
          real-type
          (mathd119-mul real-type x y)
          (mathd119-mul real-type x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd119-mul
           real-type x (mathd119-inv real-type x))
          one)))))))

(defun-sk mathd119-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (mathd119-real-p real-type x)
      (mathd119-real-p real-type y)
      (mathd119-real-p real-type z))
     (let ((zero (mathd119-zero real-type)))
       (and
        (mathd119-le real-type x x)
        (implies
         (and
          (mathd119-le real-type x y)
          (mathd119-le real-type y x))
         (equal x y))
        (implies
         (and
          (mathd119-le real-type x y)
          (mathd119-le real-type y z))
         (mathd119-le real-type x z))
        (or
         (mathd119-le real-type x y)
         (mathd119-le real-type y x))
        (implies
         (mathd119-le real-type x y)
         (mathd119-le
          real-type
          (mathd119-add real-type x z)
          (mathd119-add real-type y z)))
        (implies
         (and
          (mathd119-le real-type zero x)
          (mathd119-le real-type zero y))
         (mathd119-le
          real-type
          zero
          (mathd119-mul real-type x y))))))))

(defun-sk mathd119-rational-laws-p (real-type)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd119-real-p
       real-type (mathd119-of-rational real-type p))
      (equal
       (mathd119-of-rational real-type 0)
       (mathd119-zero real-type))
      (equal
       (mathd119-of-rational real-type 1)
       (mathd119-one real-type))
      (equal
       (mathd119-of-rational real-type (+ p q))
       (mathd119-add
        real-type
        (mathd119-of-rational real-type p)
        (mathd119-of-rational real-type q)))
      (equal
       (mathd119-of-rational real-type (* p q))
       (mathd119-mul
        real-type
        (mathd119-of-rational real-type p)
        (mathd119-of-rational real-type q)))
      (equal
       (mathd119-of-rational real-type (- p))
       (mathd119-neg
        real-type
        (mathd119-of-rational real-type p)))
      (iff
       (equal p q)
       (equal
        (mathd119-of-rational real-type p)
        (mathd119-of-rational real-type q)))
      (iff
       (<= p q)
       (mathd119-le
        real-type
        (mathd119-of-rational real-type p)
        (mathd119-of-rational real-type q)))))))

(defun mathd119-real-structure-p (real-type)
  (and
   (mathd119-closure-laws-p real-type)
   (mathd119-field-laws-p real-type)
   (mathd119-order-laws-p real-type)
   (mathd119-rational-laws-p real-type)))

(defun-sk mathd-algebra-119-statement ()
  (forall (real-type d e)
    (implies
     (and
      (mathd119-real-structure-p real-type)
      (mathd119-real-p real-type d)
      (mathd119-real-p real-type e)
      (equal
       (mathd119-mul
        real-type
        (mathd119-of-rational real-type 2)
        d)
       (mathd119-sub
        real-type
        (mathd119-mul
         real-type
         (mathd119-of-rational real-type 17)
         e)
        (mathd119-of-rational real-type 8)))
      (equal
       (mathd119-mul
        real-type
        (mathd119-of-rational real-type 2)
        e)
       (mathd119-sub
        real-type
        d
        (mathd119-of-rational real-type 9))))
     (equal
      e
      (mathd119-of-rational real-type 2)))))

(value-triple :itpeval-statement-checked)
:q
