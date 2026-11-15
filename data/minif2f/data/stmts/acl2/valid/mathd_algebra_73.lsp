;; Statement-only formalization of miniF2F artifact mathd_algebra_73:
;; for complex p, q, r, and x, if
;; (x-p)*(x-q) = (r-p)*(r-q) and x is not r, then x = p+q-r.
;; This file contains no proof.
;;
;; The source implication is stated directly over an explicit
;; characteristic-zero field carrier. In particular, this is not merely the
;; factorization identity used to prove the implication.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd73-complex-p (field value) t)
(defstub mathd73-zero (field) t)
(defstub mathd73-one (field) t)
(defstub mathd73-add (field left right) t)
(defstub mathd73-mul (field left right) t)
(defstub mathd73-neg (field value) t)
(defstub mathd73-inv (field value) t)
(defstub mathd73-of-rational (field rational) t)

(defun mathd73-sub (field left right)
  (mathd73-add field left (mathd73-neg field right)))

(defun-sk mathd73-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd73-complex-p field (mathd73-zero field))
     (mathd73-complex-p field (mathd73-one field))
     (implies
      (mathd73-complex-p field x)
      (and
       (mathd73-complex-p field (mathd73-neg field x))
       (mathd73-complex-p field (mathd73-inv field x))))
     (implies
      (and
       (mathd73-complex-p field x)
       (mathd73-complex-p field y))
      (and
       (mathd73-complex-p field (mathd73-add field x y))
       (mathd73-complex-p field (mathd73-mul field x y)))))))

(defun-sk mathd73-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd73-complex-p field x)
      (mathd73-complex-p field y)
      (mathd73-complex-p field z))
     (let ((zero (mathd73-zero field))
           (one (mathd73-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd73-add field x y)
         (mathd73-add field y x))
        (equal
         (mathd73-add field (mathd73-add field x y) z)
         (mathd73-add field x (mathd73-add field y z)))
        (equal (mathd73-add field x zero) x)
        (equal
         (mathd73-add field x (mathd73-neg field x))
         zero)
        (equal
         (mathd73-mul field x y)
         (mathd73-mul field y x))
        (equal
         (mathd73-mul field (mathd73-mul field x y) z)
         (mathd73-mul field x (mathd73-mul field y z)))
        (equal (mathd73-mul field x one) x)
        (equal
         (mathd73-mul field x (mathd73-add field y z))
         (mathd73-add
          field
          (mathd73-mul field x y)
          (mathd73-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd73-mul field x (mathd73-inv field x))
          one)))))))

(defun-sk mathd73-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd73-complex-p
       field (mathd73-of-rational field p))
      (equal
       (mathd73-of-rational field 0)
       (mathd73-zero field))
      (equal
       (mathd73-of-rational field 1)
       (mathd73-one field))
      (equal
       (mathd73-of-rational field (+ p q))
       (mathd73-add
        field
        (mathd73-of-rational field p)
        (mathd73-of-rational field q)))
      (equal
       (mathd73-of-rational field (* p q))
       (mathd73-mul
        field
        (mathd73-of-rational field p)
        (mathd73-of-rational field q)))
      (equal
       (mathd73-of-rational field (- p))
       (mathd73-neg
        field (mathd73-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd73-of-rational field p)
        (mathd73-of-rational field q)))))))

(defun mathd73-field-p (field)
  (and
   (mathd73-closure-laws-p field)
   (mathd73-field-laws-p field)
   (mathd73-rational-laws-p field)))

(defun-sk mathd-algebra-73-statement ()
  (forall (field p q r x)
    (implies
     (and
      (mathd73-field-p field)
      (mathd73-complex-p field p)
      (mathd73-complex-p field q)
      (mathd73-complex-p field r)
      (mathd73-complex-p field x)
      (equal
       (mathd73-mul
        field
        (mathd73-sub field x p)
        (mathd73-sub field x q))
       (mathd73-mul
        field
        (mathd73-sub field r p)
        (mathd73-sub field r q)))
      (not (equal x r)))
     (equal
      x
      (mathd73-sub
       field
       (mathd73-add field p q)
       r)))))

(value-triple :itpeval-statement-checked)
:q
