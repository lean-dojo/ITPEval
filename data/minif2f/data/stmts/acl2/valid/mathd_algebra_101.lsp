;; Statement-only formalization of miniF2F artifact mathd_algebra_101:
;; every real x satisfying x^2 - 5*x - 4 <= 10 lies between -2 and 7.
;; This file contains no proof.
;;
;; ACL2's native rationals are not the full real domain. The source
;; implication is therefore stated directly over an explicit ordered-field
;; carrier with an injective, order-preserving rational embedding.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd101-real-p (field value) t)
(defstub mathd101-zero (field) t)
(defstub mathd101-one (field) t)
(defstub mathd101-add (field left right) t)
(defstub mathd101-mul (field left right) t)
(defstub mathd101-neg (field value) t)
(defstub mathd101-inv (field value) t)
(defstub mathd101-le (field left right) t)
(defstub mathd101-of-rational (field rational) t)

(defun mathd101-sub (field left right)
  (mathd101-add field left (mathd101-neg field right)))

(defun mathd101-square (field value)
  (mathd101-mul field value value))

(defun-sk mathd101-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd101-real-p field (mathd101-zero field))
     (mathd101-real-p field (mathd101-one field))
     (implies
      (mathd101-real-p field x)
      (and
       (mathd101-real-p field (mathd101-neg field x))
       (mathd101-real-p field (mathd101-inv field x))))
     (implies
      (and
       (mathd101-real-p field x)
       (mathd101-real-p field y))
      (and
       (mathd101-real-p field (mathd101-add field x y))
       (mathd101-real-p field (mathd101-mul field x y)))))))

(defun-sk mathd101-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd101-real-p field x)
      (mathd101-real-p field y)
      (mathd101-real-p field z))
     (let ((zero (mathd101-zero field))
           (one (mathd101-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd101-add field x y)
         (mathd101-add field y x))
        (equal
         (mathd101-add field (mathd101-add field x y) z)
         (mathd101-add field x (mathd101-add field y z)))
        (equal (mathd101-add field x zero) x)
        (equal
         (mathd101-add field x (mathd101-neg field x))
         zero)
        (equal
         (mathd101-mul field x y)
         (mathd101-mul field y x))
        (equal
         (mathd101-mul field (mathd101-mul field x y) z)
         (mathd101-mul field x (mathd101-mul field y z)))
        (equal (mathd101-mul field x one) x)
        (equal
         (mathd101-mul field x (mathd101-add field y z))
         (mathd101-add
          field
          (mathd101-mul field x y)
          (mathd101-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd101-mul field x (mathd101-inv field x))
          one)))))))

(defun-sk mathd101-order-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd101-real-p field x)
      (mathd101-real-p field y)
      (mathd101-real-p field z))
     (let ((zero (mathd101-zero field)))
       (and
        (mathd101-le field x x)
        (implies
         (and
          (mathd101-le field x y)
          (mathd101-le field y x))
         (equal x y))
        (implies
         (and
          (mathd101-le field x y)
          (mathd101-le field y z))
         (mathd101-le field x z))
        (or
         (mathd101-le field x y)
         (mathd101-le field y x))
        (implies
         (mathd101-le field x y)
         (mathd101-le
          field
          (mathd101-add field x z)
          (mathd101-add field y z)))
        (implies
         (and
          (mathd101-le field zero x)
          (mathd101-le field zero y))
         (mathd101-le
          field zero (mathd101-mul field x y))))))))

(defun-sk mathd101-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd101-real-p
       field (mathd101-of-rational field p))
      (equal
       (mathd101-of-rational field 0)
       (mathd101-zero field))
      (equal
       (mathd101-of-rational field 1)
       (mathd101-one field))
      (equal
       (mathd101-of-rational field (+ p q))
       (mathd101-add
        field
        (mathd101-of-rational field p)
        (mathd101-of-rational field q)))
      (equal
       (mathd101-of-rational field (* p q))
       (mathd101-mul
        field
        (mathd101-of-rational field p)
        (mathd101-of-rational field q)))
      (equal
       (mathd101-of-rational field (- p))
       (mathd101-neg
        field (mathd101-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd101-of-rational field p)
        (mathd101-of-rational field q)))
      (iff
       (<= p q)
       (mathd101-le
        field
        (mathd101-of-rational field p)
        (mathd101-of-rational field q)))))))

(defun mathd101-ordered-field-p (field)
  (and
   (mathd101-closure-laws-p field)
   (mathd101-field-laws-p field)
   (mathd101-order-laws-p field)
   (mathd101-rational-laws-p field)))

(defun-sk mathd-algebra-101-statement ()
  (forall (field x)
    (implies
     (and
      (mathd101-ordered-field-p field)
      (mathd101-real-p field x)
      (mathd101-le
       field
       (mathd101-sub
        field
        (mathd101-sub
         field
         (mathd101-square field x)
         (mathd101-mul
          field
          (mathd101-of-rational field 5)
          x))
        (mathd101-of-rational field 4))
       (mathd101-of-rational field 10)))
     (and
      (mathd101-le
       field (mathd101-of-rational field -2) x)
      (mathd101-le
       field x (mathd101-of-rational field 7))))))

(value-triple :itpeval-statement-checked)
:q
