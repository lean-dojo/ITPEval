;; Statement-only formalization of miniF2F artifact mathd_algebra_181:
;; for a real number n not equal to 3, (n + 5) / (n - 3) = 2 implies
;; n = 11. This file contains no proof.
;;
;; The field carrier and injective rational embedding are explicit premises,
;; so n ranges over the represented real field rather than only over ACL2
;; rationals. Division is field multiplication by the inverse, exactly as in
;; the source.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub mathd181-real-p (field value) t)
(defstub mathd181-zero (field) t)
(defstub mathd181-one (field) t)
(defstub mathd181-add (field left right) t)
(defstub mathd181-mul (field left right) t)
(defstub mathd181-neg (field value) t)
(defstub mathd181-inv (field value) t)
(defstub mathd181-of-rational (field rational) t)

(defun mathd181-sub (field left right)
  (mathd181-add field left (mathd181-neg field right)))

(defun mathd181-div (field left right)
  (mathd181-mul field left (mathd181-inv field right)))

(defun-sk mathd181-closure-laws-p (field)
  (forall (x y)
    (and
     (mathd181-real-p field (mathd181-zero field))
     (mathd181-real-p field (mathd181-one field))
     (implies
      (mathd181-real-p field x)
      (and
       (mathd181-real-p field (mathd181-neg field x))
       (mathd181-real-p field (mathd181-inv field x))))
     (implies
      (and
       (mathd181-real-p field x)
       (mathd181-real-p field y))
      (and
       (mathd181-real-p field (mathd181-add field x y))
       (mathd181-real-p field (mathd181-mul field x y)))))))

(defun-sk mathd181-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (mathd181-real-p field x)
      (mathd181-real-p field y)
      (mathd181-real-p field z))
     (let ((zero (mathd181-zero field))
           (one (mathd181-one field)))
       (and
        (not (equal zero one))
        (equal
         (mathd181-add field x y)
         (mathd181-add field y x))
        (equal
         (mathd181-add field (mathd181-add field x y) z)
         (mathd181-add field x (mathd181-add field y z)))
        (equal (mathd181-add field x zero) x)
        (equal
         (mathd181-add field x (mathd181-neg field x))
         zero)
        (equal
         (mathd181-mul field x y)
         (mathd181-mul field y x))
        (equal
         (mathd181-mul field (mathd181-mul field x y) z)
         (mathd181-mul field x (mathd181-mul field y z)))
        (equal (mathd181-mul field x one) x)
        (equal
         (mathd181-mul field x (mathd181-add field y z))
         (mathd181-add
          field
          (mathd181-mul field x y)
          (mathd181-mul field x z)))
        (implies
         (not (equal x zero))
         (equal
          (mathd181-mul field x (mathd181-inv field x))
          one)))))))

(defun-sk mathd181-rational-laws-p (field)
  (forall (p q)
    (implies
     (and (rationalp p) (rationalp q))
     (and
      (mathd181-real-p
       field (mathd181-of-rational field p))
      (equal
       (mathd181-of-rational field 0)
       (mathd181-zero field))
      (equal
       (mathd181-of-rational field 1)
       (mathd181-one field))
      (equal
       (mathd181-of-rational field (+ p q))
       (mathd181-add
        field
        (mathd181-of-rational field p)
        (mathd181-of-rational field q)))
      (equal
       (mathd181-of-rational field (* p q))
       (mathd181-mul
        field
        (mathd181-of-rational field p)
        (mathd181-of-rational field q)))
      (equal
       (mathd181-of-rational field (- p))
       (mathd181-neg
        field (mathd181-of-rational field p)))
      (iff
       (equal p q)
       (equal
        (mathd181-of-rational field p)
        (mathd181-of-rational field q)))))))

(defun mathd181-field-p (field)
  (and
   (mathd181-closure-laws-p field)
   (mathd181-field-laws-p field)
   (mathd181-rational-laws-p field)))

(defun-sk mathd-algebra-181-statement ()
  (forall (field n)
    (implies
     (and
      (mathd181-field-p field)
      (mathd181-real-p field n)
      (not
       (equal n (mathd181-of-rational field 3)))
      (equal
       (mathd181-div
        field
        (mathd181-add
         field n (mathd181-of-rational field 5))
        (mathd181-sub
         field n (mathd181-of-rational field 3)))
       (mathd181-of-rational field 2)))
     (equal
      n
      (mathd181-of-rational field 11)))))

(value-triple :itpeval-statement-checked)
:q
