;; Statement-only formalization of miniF2F corpus artifact
;; algebra_sqineq_2unitcircatblt1: real numbers a and b whose squares sum
;; to 2 have product at most 1. This file contains no proof.
;;
;; The conservative symbols below present an arbitrary real-closed ordered
;; field. Its full field, order, and real-closedness laws are explicit in the
;; statement predicate. Real-closed ordered fields have the same first-order
;; ordered-field theory as the real numbers, so this preserves the full real
;; domains without restricting a or b to ACL2's rational numbers.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub sqineq2uc-real-p (x) t)
(defstub sqineq2uc-add-op (x y) t)
(defstub sqineq2uc-multiply-op (x y) t)
(defstub sqineq2uc-negate-op (x) t)
(defstub sqineq2uc-inverse-op (x) t)
(defstub sqineq2uc-less-op (x y) t)

(defun sqineq2uc-member-p (x)
  (if (sqineq2uc-real-p x) t nil))

(defun sqineq2uc-add (x y)
  (sqineq2uc-add-op x y))

(defun sqineq2uc-mul (x y)
  (sqineq2uc-multiply-op x y))

(defun sqineq2uc-neg (x)
  (sqineq2uc-negate-op x))

(defun sqineq2uc-inv (x)
  (sqineq2uc-inverse-op x))

(defun sqineq2uc-less (x y)
  (if (sqineq2uc-less-op x y) t nil))

(defun sqineq2uc-square (x)
  (sqineq2uc-mul x x))

(defun sqineq2uc-positive-p (x zero)
  (and
   (sqineq2uc-member-p x)
   (sqineq2uc-less zero x)))

(defun-sk sqineq2uc-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (sqineq2uc-member-p x)
      (sqineq2uc-member-p y)
      (sqineq2uc-member-p z))
     (and
      (sqineq2uc-member-p
       (sqineq2uc-add x y))
      (sqineq2uc-member-p
       (sqineq2uc-mul x y))
      (sqineq2uc-member-p
       (sqineq2uc-neg x))
      (implies
       (not (equal x zero))
       (sqineq2uc-member-p
        (sqineq2uc-inv x)))
      (equal
       (sqineq2uc-add
        (sqineq2uc-add x y)
        z)
       (sqineq2uc-add
        x
        (sqineq2uc-add y z)))
      (equal
       (sqineq2uc-add x y)
       (sqineq2uc-add y x))
      (equal
       (sqineq2uc-add x zero)
       x)
      (equal
       (sqineq2uc-add
        x
        (sqineq2uc-neg x))
       zero)
      (equal
       (sqineq2uc-mul
        (sqineq2uc-mul x y)
        z)
       (sqineq2uc-mul
        x
        (sqineq2uc-mul y z)))
      (equal
       (sqineq2uc-mul x y)
       (sqineq2uc-mul y x))
      (equal
       (sqineq2uc-mul x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (sqineq2uc-mul
         x
         (sqineq2uc-inv x))
        one))
      (equal
       (sqineq2uc-mul
        x
        (sqineq2uc-add y z))
       (sqineq2uc-add
        (sqineq2uc-mul x y)
        (sqineq2uc-mul x z)))))))

(defun-sk sqineq2uc-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (sqineq2uc-member-p x)
      (sqineq2uc-member-p y)
      (sqineq2uc-member-p z))
     (and
      (not (sqineq2uc-less x x))
      (or
       (equal x y)
       (sqineq2uc-less x y)
       (sqineq2uc-less y x))
      (implies
       (and
        (sqineq2uc-less x y)
        (sqineq2uc-less y z))
       (sqineq2uc-less x z))
      (implies
       (sqineq2uc-less x y)
       (sqineq2uc-less
        (sqineq2uc-add x z)
        (sqineq2uc-add y z)))
      (implies
       (and
        (sqineq2uc-less zero x)
        (sqineq2uc-less zero y))
       (sqineq2uc-less
        zero
        (sqineq2uc-mul x y)))))))

(defun sqineq2uc-polynomial-p (coefficients)
  (if (endp coefficients)
      t
    (and
     (sqineq2uc-member-p (car coefficients))
     (sqineq2uc-polynomial-p (cdr coefficients)))))

(defun sqineq2uc-polynomial-value
    (coefficients x zero)
  (if (endp coefficients)
      zero
    (sqineq2uc-add
     (car coefficients)
     (sqineq2uc-mul
      x
      (sqineq2uc-polynomial-value
       (cdr coefficients)
       x
       zero)))))

(defun sqineq2uc-leading-coefficient (coefficients)
  (if (endp (cdr coefficients))
      (car coefficients)
    (sqineq2uc-leading-coefficient
     (cdr coefficients))))

(defun sqineq2uc-odd-degree-p (coefficients zero)
  (and
   (consp coefficients)
   (consp (cdr coefficients))
   (not
    (equal
     (sqineq2uc-leading-coefficient coefficients)
     zero))
   (equal
    (mod (1- (len coefficients)) 2)
    1)))

(defun-sk sqineq2uc-square-root-exists-p (x zero)
  (exists (root)
    (and
     (or
      (equal root zero)
      (sqineq2uc-positive-p root zero))
     (equal
      (sqineq2uc-square root)
      x))))

(defun-sk sqineq2uc-positive-square-roots-p (zero)
  (forall (x)
    (implies
     (sqineq2uc-positive-p x zero)
     (sqineq2uc-square-root-exists-p
      x
      zero))))

(defun-sk sqineq2uc-polynomial-root-exists-p
    (coefficients zero)
  (exists (root)
    (and
     (sqineq2uc-member-p root)
     (equal
      (sqineq2uc-polynomial-value
       coefficients
       root
       zero)
      zero))))

(defun-sk sqineq2uc-odd-polynomial-roots-p (zero)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (sqineq2uc-polynomial-p coefficients)
      (sqineq2uc-odd-degree-p coefficients zero))
     (sqineq2uc-polynomial-root-exists-p
      coefficients
      zero))))

(defun sqineq2uc-real-closed-field-p (zero one)
  (and
   (sqineq2uc-member-p zero)
   (sqineq2uc-member-p one)
   (not (equal zero one))
   (sqineq2uc-less zero one)
   (sqineq2uc-field-laws-p zero one)
   (sqineq2uc-order-laws-p zero)
   (sqineq2uc-positive-square-roots-p zero)
   (sqineq2uc-odd-polynomial-roots-p zero)))

(defun sqineq2uc-natural (zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (sqineq2uc-add
     one
     (sqineq2uc-natural
      zero
      one
      (- n 1)))))

(defun-sk algebra-sqineq-2unitcircatblt1-statement (zero one)
  (forall (a b)
    (implies
     (and
      (sqineq2uc-real-closed-field-p zero one)
      (sqineq2uc-member-p a)
      (sqineq2uc-member-p b)
      (equal
       (sqineq2uc-add
        (sqineq2uc-square a)
        (sqineq2uc-square b))
       (sqineq2uc-natural zero one 2)))
     (not
      (sqineq2uc-less
       one
       (sqineq2uc-mul a b))))))

(value-triple :itpeval-statement-checked)
:q
