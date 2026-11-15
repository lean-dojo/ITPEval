;; Statement-only formalization of miniF2F artifact mathd_algebra_206:
;; if the real quadratic f(x) = x^2 + a*x + b has the distinct roots 2*a
;; and b, then a + b = -1. This file contains no proof.
;;
;; The source's pointwise definition uniquely determines f, so the two root
;; hypotheses are stated as the corresponding polynomial equations. The
;; explicit characteristic-zero field preserves arbitrary real a and b.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd206-real-p (field value) t)
(defstub mathd206-zero (field) t)
(defstub mathd206-one (field) t)
(defstub mathd206-add (field left right) t)
(defstub mathd206-mul (field left right) t)
(defstub mathd206-neg (field value) t)
(defstub mathd206-inv (field value) t)
(defstub mathd206-of-rational (field rational) t)

(defun mathd206-polynomial (field x a b)
  (mathd206-add
   field
   (mathd206-add
    field
    (mathd206-mul field x x)
    (mathd206-mul field a x))
   b))

(defun-sk mathd206-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd206-real-p field (mathd206-zero field))
     (mathd206-real-p field (mathd206-one field))
     (implies
      (mathd206-real-p field x)
      (and
       (mathd206-real-p field (mathd206-neg field x))
       (mathd206-real-p field (mathd206-inv field x))))
     (implies
      (and
       (mathd206-real-p field x)
       (mathd206-real-p field y))
      (and
       (mathd206-real-p field (mathd206-add field x y))
       (mathd206-real-p field (mathd206-mul field x y)))))))

(defun-sk mathd206-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd206-real-p field x)
      (mathd206-real-p field y)
      (mathd206-real-p field z))
     (let ((zero (mathd206-zero field))
           (one (mathd206-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd206-add field x y)
         (mathd206-add field y x))
        (equal
         (mathd206-add field (mathd206-add field x y) z)
         (mathd206-add field x (mathd206-add field y z)))
        (equal (mathd206-add field x zero) x)
        (equal
         (mathd206-add field x (mathd206-neg field x))
         zero)
        (equal
         (mathd206-mul field x y)
         (mathd206-mul field y x))
        (equal
         (mathd206-mul field (mathd206-mul field x y) z)
         (mathd206-mul field x (mathd206-mul field y z)))
        (equal (mathd206-mul field x one) x)
        (equal
         (mathd206-mul field x (mathd206-add field y z))
         (mathd206-add
          field
          (mathd206-mul field x y)
          (mathd206-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd206-mul field x (mathd206-inv field x))
          one)))))))

(defun-sk mathd206-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd206-real-p
       field (mathd206-of-rational field p))
      (equal
       (mathd206-of-rational field 0)
       (mathd206-zero field))
      (equal
       (mathd206-of-rational field 1)
       (mathd206-one field))
      (equal
       (mathd206-of-rational field (+ p q))
       (mathd206-add
        field
        (mathd206-of-rational field p)
        (mathd206-of-rational field q)))
      (equal
       (mathd206-of-rational field (* p q))
       (mathd206-mul
        field
        (mathd206-of-rational field p)
        (mathd206-of-rational field q)))
      (equal
       (mathd206-of-rational field (- p))
       (mathd206-neg
        field (mathd206-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd206-of-rational field p)
        (mathd206-of-rational field q)))))))

(defun mathd206-field-p (field)
  (and
   (mathd206-closure-laws-p field)
   (mathd206-field-laws-p field)
   (mathd206-rational-laws-p field)))

(defun-sk mathd-algebra-206-statement ()
  (forall (field a b)
    (let ((two-a
           (mathd206-mul
            field
            (mathd206-of-rational field 2)
            a))
          (zero (mathd206-zero field)))
      (implies
       (and
        (mathd206-field-p field)
        (mathd206-real-p field a)
        (mathd206-real-p field b)
        (not (equal two-a b))
        (equal
         (mathd206-polynomial field two-a a b)
         zero)
        (equal
         (mathd206-polynomial field b a b)
         zero))
       (equal
        (mathd206-add field a b)
        (mathd206-of-rational field -1))))))

(value-triple :itpeval-statement-checked)
:q
