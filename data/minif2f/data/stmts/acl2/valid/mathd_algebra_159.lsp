;; Statement-only formalization of miniF2F artifact mathd_algebra_159:
;; a real coefficient b in the given quartic polynomial function is determined
;; by f(1) = 1, namely b = -2. This file contains no proof.
;;
;; The source definition of f determines f(1), so the function parameter can
;; be eliminated without solving the theorem. The explicitly axiomatized
;; characteristic-zero field keeps b and f(1) in the source domain instead of
;; letting unguarded ACL2 objects stand for real values.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd159-real-p (field value) t)
(defstub mathd159-zero (field) t)
(defstub mathd159-one (field) t)
(defstub mathd159-add (field left right) t)
(defstub mathd159-mul (field left right) t)
(defstub mathd159-neg (field value) t)
(defstub mathd159-inv (field value) t)
(defstub mathd159-of-rational (field rational) t)

(defun mathd159-sub (field left right)
  (mathd159-add
   field left (mathd159-neg field right)))

(defun mathd159-square (field value)
  (mathd159-mul field value value))

(defun mathd159-cube (field value)
  (mathd159-mul
   field (mathd159-square field value) value))

(defun mathd159-fourth-power (field value)
  (mathd159-square field (mathd159-square field value)))

(defun mathd159-polynomial (field b x)
  (mathd159-add
   field
   (mathd159-sub
    field
    (mathd159-add
     field
     (mathd159-sub
      field
      (mathd159-mul
       field
       (mathd159-of-rational field 3)
       (mathd159-fourth-power field x))
      (mathd159-mul
       field
       (mathd159-of-rational field 7)
       (mathd159-cube field x)))
     (mathd159-mul
      field
      (mathd159-of-rational field 2)
      (mathd159-square field x)))
    (mathd159-mul field b x))
   (mathd159-one field)))

(defun-sk mathd159-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd159-real-p field (mathd159-zero field))
     (mathd159-real-p field (mathd159-one field))
     (implies
      (mathd159-real-p field x)
      (and
       (mathd159-real-p field (mathd159-neg field x))
       (mathd159-real-p field (mathd159-inv field x))))
     (implies
      (and
       (mathd159-real-p field x)
       (mathd159-real-p field y))
      (and
       (mathd159-real-p field (mathd159-add field x y))
       (mathd159-real-p field (mathd159-mul field x y)))))))

(defun-sk mathd159-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd159-real-p field x)
      (mathd159-real-p field y)
      (mathd159-real-p field z))
     (let ((zero (mathd159-zero field))
           (one (mathd159-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd159-add field x y)
         (mathd159-add field y x))
        (equal
         (mathd159-add field (mathd159-add field x y) z)
         (mathd159-add field x (mathd159-add field y z)))
        (equal (mathd159-add field x zero) x)
        (equal
         (mathd159-add field x (mathd159-neg field x))
         zero)
        (equal
         (mathd159-mul field x y)
         (mathd159-mul field y x))
        (equal
         (mathd159-mul field (mathd159-mul field x y) z)
         (mathd159-mul field x (mathd159-mul field y z)))
        (equal (mathd159-mul field x one) x)
        (equal
         (mathd159-mul field x (mathd159-add field y z))
         (mathd159-add
          field
          (mathd159-mul field x y)
          (mathd159-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd159-mul field x (mathd159-inv field x))
          one)))))))

(defun-sk mathd159-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd159-real-p
       field (mathd159-of-rational field p))
      (equal
       (mathd159-of-rational field 0)
       (mathd159-zero field))
      (equal
       (mathd159-of-rational field 1)
       (mathd159-one field))
      (equal
       (mathd159-of-rational field (+ p q))
       (mathd159-add
        field
        (mathd159-of-rational field p)
        (mathd159-of-rational field q)))
      (equal
       (mathd159-of-rational field (* p q))
       (mathd159-mul
        field
        (mathd159-of-rational field p)
        (mathd159-of-rational field q)))
      (equal
       (mathd159-of-rational field (- p))
       (mathd159-neg
        field
        (mathd159-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd159-of-rational field p)
        (mathd159-of-rational field q)))))))

(defun mathd159-field-p (field)
  (and
   (mathd159-closure-laws-p field)
   (mathd159-field-laws-p field)
   (mathd159-rational-laws-p field)))

(defun-sk mathd-algebra-159-statement ()
  (forall (field b f-at-one)
    (implies
     (and
      (mathd159-field-p field)
      (mathd159-real-p field b)
      (mathd159-real-p field f-at-one)
      (equal
       f-at-one
       (mathd159-polynomial
        field b (mathd159-one field)))
      (equal f-at-one (mathd159-one field)))
     (equal
      b
      (mathd159-of-rational field -2)))))

(value-triple :itpeval-statement-checked)
:q
