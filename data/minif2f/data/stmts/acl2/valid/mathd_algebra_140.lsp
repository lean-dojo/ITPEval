;; Statement-only formalization of miniF2F artifact mathd_algebra_140:
;; positive real a, b, and c satisfying
;; 24*x^2 - 19*x - 35 = (a*x - 5)*(2*(b*x) + c) for every real x
;; also satisfy a*b - 3*c = -9. This file contains no proof.
;;
;; The universal polynomial identity is retained directly. The explicit
;; ordered-field carrier avoids narrowing the source variables to rationals.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd140-real-p (field value) t)
(defstub mathd140-zero (field) t)
(defstub mathd140-one (field) t)
(defstub mathd140-add (field left right) t)
(defstub mathd140-mul (field left right) t)
(defstub mathd140-neg (field value) t)
(defstub mathd140-inv (field value) t)
(defstub mathd140-le (field left right) t)
(defstub mathd140-of-rational (field rational) t)

(defun mathd140-sub (field left right)
  (mathd140-add field left (mathd140-neg field right)))

(defun mathd140-square (field value)
  (mathd140-mul field value value))

(defun mathd140-lt (field left right)
  (and
   (mathd140-le field left right)
   (not (equal left right))))

(defun mathd140-left-polynomial (field x)
  (mathd140-sub
   field
   (mathd140-sub
    field
    (mathd140-mul
     field
     (mathd140-of-rational field 24)
     (mathd140-square field x))
    (mathd140-mul
     field
     (mathd140-of-rational field 19)
     x))
   (mathd140-of-rational field 35)))

(defun mathd140-right-polynomial (field a b c x)
  (mathd140-mul
   field
   (mathd140-sub
    field
    (mathd140-mul field a x)
    (mathd140-of-rational field 5))
   (mathd140-add
    field
    (mathd140-mul
     field
     (mathd140-of-rational field 2)
     (mathd140-mul field b x))
    c)))

(defun-sk mathd140-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd140-real-p field (mathd140-zero field))
     (mathd140-real-p field (mathd140-one field))
     (implies
      (mathd140-real-p field x)
      (and
       (mathd140-real-p field (mathd140-neg field x))
       (mathd140-real-p field (mathd140-inv field x))))
     (implies
      (and
       (mathd140-real-p field x)
       (mathd140-real-p field y))
      (and
       (mathd140-real-p field (mathd140-add field x y))
       (mathd140-real-p field (mathd140-mul field x y)))))))

(defun-sk mathd140-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd140-real-p field x)
      (mathd140-real-p field y)
      (mathd140-real-p field z))
     (let ((zero (mathd140-zero field))
           (one (mathd140-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd140-add field x y)
         (mathd140-add field y x))
        (equal
         (mathd140-add field (mathd140-add field x y) z)
         (mathd140-add field x (mathd140-add field y z)))
        (equal (mathd140-add field x zero) x)
        (equal
         (mathd140-add field x (mathd140-neg field x))
         zero)
        (equal
         (mathd140-mul field x y)
         (mathd140-mul field y x))
        (equal
         (mathd140-mul field (mathd140-mul field x y) z)
         (mathd140-mul field x (mathd140-mul field y z)))
        (equal (mathd140-mul field x one) x)
        (equal
         (mathd140-mul field x (mathd140-add field y z))
         (mathd140-add
          field
          (mathd140-mul field x y)
          (mathd140-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd140-mul field x (mathd140-inv field x))
          one)))))))

(defun-sk mathd140-order-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd140-real-p field x)
      (mathd140-real-p field y)
      (mathd140-real-p field z))
     (let ((zero (mathd140-zero field)))
       (and
        (mathd140-le field x x)
        (implies
         (and
          (mathd140-le field x y)
          (mathd140-le field y x))
         (equal x y))
        (implies
         (and
          (mathd140-le field x y)
          (mathd140-le field y z))
         (mathd140-le field x z))
        (or
         (mathd140-le field x y)
         (mathd140-le field y x))
        (implies
         (mathd140-le field x y)
         (mathd140-le
          field
          (mathd140-add field x z)
          (mathd140-add field y z)))
        (implies
         (and
          (mathd140-le field zero x)
          (mathd140-le field zero y))
         (mathd140-le
          field zero (mathd140-mul field x y))))))))

(defun-sk mathd140-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd140-real-p
       field (mathd140-of-rational field p))
      (equal
       (mathd140-of-rational field 0)
       (mathd140-zero field))
      (equal
       (mathd140-of-rational field 1)
       (mathd140-one field))
      (equal
       (mathd140-of-rational field (+ p q))
       (mathd140-add
        field
        (mathd140-of-rational field p)
        (mathd140-of-rational field q)))
      (equal
       (mathd140-of-rational field (* p q))
       (mathd140-mul
        field
        (mathd140-of-rational field p)
        (mathd140-of-rational field q)))
      (equal
       (mathd140-of-rational field (- p))
       (mathd140-neg
        field (mathd140-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd140-of-rational field p)
        (mathd140-of-rational field q)))
      (iff
       (<= p q)
       (mathd140-le
        field
        (mathd140-of-rational field p)
        (mathd140-of-rational field q)))))))

(defun mathd140-ordered-field-p (field)
  (and
   (mathd140-closure-laws-p field)
   (mathd140-field-laws-p field)
   (mathd140-order-laws-p field)
   (mathd140-rational-laws-p field)))

(defun-sk mathd140-identity-p (field a b c)
  (forall (x)
    (implies
     (mathd140-real-p field x)
     (equal
      (mathd140-left-polynomial field x)
      (mathd140-right-polynomial field a b c x)))))

(defun-sk mathd-algebra-140-statement ()
  (forall (field a b c)
    (implies
     (and
      (mathd140-ordered-field-p field)
      (mathd140-real-p field a)
      (mathd140-real-p field b)
      (mathd140-real-p field c)
      (mathd140-lt field (mathd140-zero field) a)
      (mathd140-lt field (mathd140-zero field) b)
      (mathd140-lt field (mathd140-zero field) c)
      (mathd140-identity-p field a b c))
     (equal
      (mathd140-sub
       field
       (mathd140-mul field a b)
       (mathd140-mul
        field
        (mathd140-of-rational field 3)
        c))
      (mathd140-of-rational field -9)))))

(value-triple :itpeval-statement-checked)
:q
