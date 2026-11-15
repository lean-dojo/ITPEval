;; Statement-only formalization of miniF2F artifact mathd_algebra_214:
;; a real quadratic of the form f(x) = a*(x-2)^2 + 3 that satisfies
;; f(4) = 4 also satisfies f(6) = 7. This file contains no proof.
;;
;; The pointwise source hypothesis uniquely determines f, so its values are
;; inlined. The explicit characteristic-zero field carrier preserves
;; arbitrary real coefficients instead of restricting a to ACL2 rationals.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd214-real-p (field value) t)
(defstub mathd214-zero (field) t)
(defstub mathd214-one (field) t)
(defstub mathd214-add (field left right) t)
(defstub mathd214-mul (field left right) t)
(defstub mathd214-neg (field value) t)
(defstub mathd214-inv (field value) t)
(defstub mathd214-of-rational (field rational) t)

(defun mathd214-sub (field left right)
  (mathd214-add field left (mathd214-neg field right)))

(defun mathd214-square (field value)
  (mathd214-mul field value value))

(defun mathd214-quadratic (field a x)
  (mathd214-add
   field
   (mathd214-mul
    field
    a
    (mathd214-square
     field
     (mathd214-sub
      field x (mathd214-of-rational field 2))))
   (mathd214-of-rational field 3)))

(defun-sk mathd214-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd214-real-p field (mathd214-zero field))
     (mathd214-real-p field (mathd214-one field))
     (implies
      (mathd214-real-p field x)
      (and
       (mathd214-real-p field (mathd214-neg field x))
       (mathd214-real-p field (mathd214-inv field x))))
     (implies
      (and
       (mathd214-real-p field x)
       (mathd214-real-p field y))
      (and
       (mathd214-real-p field (mathd214-add field x y))
       (mathd214-real-p field (mathd214-mul field x y)))))))

(defun-sk mathd214-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd214-real-p field x)
      (mathd214-real-p field y)
      (mathd214-real-p field z))
     (let ((zero (mathd214-zero field))
           (one (mathd214-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd214-add field x y)
         (mathd214-add field y x))
        (equal
         (mathd214-add field (mathd214-add field x y) z)
         (mathd214-add field x (mathd214-add field y z)))
        (equal (mathd214-add field x zero) x)
        (equal
         (mathd214-add field x (mathd214-neg field x))
         zero)
        (equal
         (mathd214-mul field x y)
         (mathd214-mul field y x))
        (equal
         (mathd214-mul field (mathd214-mul field x y) z)
         (mathd214-mul field x (mathd214-mul field y z)))
        (equal (mathd214-mul field x one) x)
        (equal
         (mathd214-mul field x (mathd214-add field y z))
         (mathd214-add
          field
          (mathd214-mul field x y)
          (mathd214-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd214-mul field x (mathd214-inv field x))
          one)))))))

(defun-sk mathd214-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd214-real-p
       field (mathd214-of-rational field p))
      (equal
       (mathd214-of-rational field 0)
       (mathd214-zero field))
      (equal
       (mathd214-of-rational field 1)
       (mathd214-one field))
      (equal
       (mathd214-of-rational field (+ p q))
       (mathd214-add
        field
        (mathd214-of-rational field p)
        (mathd214-of-rational field q)))
      (equal
       (mathd214-of-rational field (* p q))
       (mathd214-mul
        field
        (mathd214-of-rational field p)
        (mathd214-of-rational field q)))
      (equal
       (mathd214-of-rational field (- p))
       (mathd214-neg
        field (mathd214-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd214-of-rational field p)
        (mathd214-of-rational field q)))))))

(defun mathd214-field-p (field)
  (and
   (mathd214-closure-laws-p field)
   (mathd214-field-laws-p field)
   (mathd214-rational-laws-p field)))

(defun-sk mathd-algebra-214-statement ()
  (forall (field a)
    (implies
     (and
      (mathd214-field-p field)
      (mathd214-real-p field a)
      (equal
       (mathd214-quadratic
        field a (mathd214-of-rational field 4))
       (mathd214-of-rational field 4)))
     (equal
      (mathd214-quadratic
       field a (mathd214-of-rational field 6))
      (mathd214-of-rational field 7)))))

(value-triple :itpeval-statement-checked)
:q
