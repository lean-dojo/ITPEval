;; Statement-only formalization of miniF2F artifact mathd_algebra_132:
;; for real x, the functions f(t) = t + 2 and g(t) = t^2 commuting at x
;; imply x = -1/2. This file contains no proof.
;;
;; The pointwise source hypotheses uniquely determine f and g, so replacing
;; their applications by those expressions preserves the proposition. The
;; carrier below is an arbitrary characteristic-zero field, rather than the
;; improper rational restriction used by the previous candidate.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd132-real-p (field value) t)
(defstub mathd132-zero (field) t)
(defstub mathd132-one (field) t)
(defstub mathd132-add (field left right) t)
(defstub mathd132-mul (field left right) t)
(defstub mathd132-neg (field value) t)
(defstub mathd132-inv (field value) t)
(defstub mathd132-of-rational (field rational) t)

(defun mathd132-square (field value)
  (mathd132-mul field value value))

(defun mathd132-f (field value)
  (mathd132-add
   field
   value
   (mathd132-of-rational field 2)))

(defun mathd132-g (field value)
  (mathd132-square field value))

(defun-sk mathd132-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd132-real-p field (mathd132-zero field))
     (mathd132-real-p field (mathd132-one field))
     (implies
      (mathd132-real-p field x)
      (and
       (mathd132-real-p field (mathd132-neg field x))
       (mathd132-real-p field (mathd132-inv field x))))
     (implies
      (and
       (mathd132-real-p field x)
       (mathd132-real-p field y))
      (and
       (mathd132-real-p field (mathd132-add field x y))
       (mathd132-real-p field (mathd132-mul field x y)))))))

(defun-sk mathd132-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd132-real-p field x)
      (mathd132-real-p field y)
      (mathd132-real-p field z))
     (let ((zero (mathd132-zero field))
           (one (mathd132-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd132-add field x y)
         (mathd132-add field y x))
        (equal
         (mathd132-add field (mathd132-add field x y) z)
         (mathd132-add field x (mathd132-add field y z)))
        (equal (mathd132-add field x zero) x)
        (equal
         (mathd132-add field x (mathd132-neg field x))
         zero)
        (equal
         (mathd132-mul field x y)
         (mathd132-mul field y x))
        (equal
         (mathd132-mul field (mathd132-mul field x y) z)
         (mathd132-mul field x (mathd132-mul field y z)))
        (equal (mathd132-mul field x one) x)
        (equal
         (mathd132-mul field x (mathd132-add field y z))
         (mathd132-add
          field
          (mathd132-mul field x y)
          (mathd132-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd132-mul field x (mathd132-inv field x))
          one)))))))

(defun-sk mathd132-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd132-real-p
       field (mathd132-of-rational field p))
      (equal
       (mathd132-of-rational field 0)
       (mathd132-zero field))
      (equal
       (mathd132-of-rational field 1)
       (mathd132-one field))
      (equal
       (mathd132-of-rational field (+ p q))
       (mathd132-add
        field
        (mathd132-of-rational field p)
        (mathd132-of-rational field q)))
      (equal
       (mathd132-of-rational field (* p q))
       (mathd132-mul
        field
        (mathd132-of-rational field p)
        (mathd132-of-rational field q)))
      (equal
       (mathd132-of-rational field (- p))
       (mathd132-neg
        field
        (mathd132-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd132-of-rational field p)
        (mathd132-of-rational field q)))))))

(defun mathd132-field-p (field)
  (and
   (mathd132-closure-laws-p field)
   (mathd132-field-laws-p field)
   (mathd132-rational-laws-p field)))

(defun-sk mathd-algebra-132-statement ()
  (forall (field x)
    (implies
     (and
      (mathd132-field-p field)
      (mathd132-real-p field x)
      (equal
       (mathd132-f field (mathd132-g field x))
       (mathd132-g field (mathd132-f field x))))
     (equal
      x
      (mathd132-of-rational field -1/2)))))

(value-triple :itpeval-statement-checked)
:q
