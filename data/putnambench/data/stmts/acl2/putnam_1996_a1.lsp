;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_a1:
;; the least area of a rectangle satisfying the stated packing inequalities
;; for every positive unit-circle pair is (1 + sqrt(2))/2. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's conservative interfaces below present an arbitrary real closed
;; ordered field. The field, order, nonnegative-square-root, and odd-degree
;; polynomial-root laws are the standard first-order characterization of the
;; real scalar theory needed by this statement. The real numbers instantiate
;; these laws, and all real closed fields satisfy the same first-order
;; sentences, so this preserves the source proposition without restricting
;; its variables to rationals or to externally supplied algebraic tuples.
;;
;; Every mathematical quantifier from the source is internal: A-PROP
;; universally quantifies over all positive unit-circle pairs and its packing
;; rectangle is existential; the final lower bound universally quantifies over
;; every area whose A-PROP holds.

(defstub putnam-1996-a1-real-p (value) t)
(defstub putnam-1996-a1-zero () t)
(defstub putnam-1996-a1-one () t)
(defstub putnam-1996-a1-add (left right) t)
(defstub putnam-1996-a1-mul (left right) t)
(defstub putnam-1996-a1-neg (value) t)
(defstub putnam-1996-a1-inv (value) t)
(defstub putnam-1996-a1-lt (left right) t)

(defun putnam-1996-a1-square (value)
  (putnam-1996-a1-mul value value))

(defun putnam-1996-a1-two ()
  (putnam-1996-a1-add
   (putnam-1996-a1-one)
   (putnam-1996-a1-one)))

(defun putnam-1996-a1-div (left right)
  (putnam-1996-a1-mul
   left
   (putnam-1996-a1-inv right)))

(defun putnam-1996-a1-le (left right)
  (not (putnam-1996-a1-lt right left)))

(defun putnam-1996-a1-max (left right)
  (if (putnam-1996-a1-lt left right)
      right
    left))

(defun putnam-1996-a1-min (left right)
  (if (putnam-1996-a1-lt left right)
      left
    right))

(defun-sk putnam-1996-a1-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1996-a1-real-p x)
      (putnam-1996-a1-real-p y)
      (putnam-1996-a1-real-p z))
     (and
      (putnam-1996-a1-real-p
       (putnam-1996-a1-add x y))
      (putnam-1996-a1-real-p
       (putnam-1996-a1-mul x y))
      (putnam-1996-a1-real-p
       (putnam-1996-a1-neg x))
      (putnam-1996-a1-real-p
       (putnam-1996-a1-inv x))
      (equal
       (putnam-1996-a1-add
        (putnam-1996-a1-add x y) z)
       (putnam-1996-a1-add
        x (putnam-1996-a1-add y z)))
      (equal
       (putnam-1996-a1-add x y)
       (putnam-1996-a1-add y x))
      (equal
       (putnam-1996-a1-add x (putnam-1996-a1-zero))
       x)
      (equal
       (putnam-1996-a1-add x (putnam-1996-a1-neg x))
       (putnam-1996-a1-zero))
      (equal
       (putnam-1996-a1-mul
        (putnam-1996-a1-mul x y) z)
       (putnam-1996-a1-mul
        x (putnam-1996-a1-mul y z)))
      (equal
       (putnam-1996-a1-mul x y)
       (putnam-1996-a1-mul y x))
      (equal
       (putnam-1996-a1-mul x (putnam-1996-a1-one))
       x)
      (implies
       (equal x (putnam-1996-a1-zero))
       (equal
        (putnam-1996-a1-inv x)
        (putnam-1996-a1-zero)))
      (implies
       (not (equal x (putnam-1996-a1-zero)))
       (equal
        (putnam-1996-a1-mul
         x (putnam-1996-a1-inv x))
        (putnam-1996-a1-one)))
      (equal
       (putnam-1996-a1-mul
        x (putnam-1996-a1-add y z))
       (putnam-1996-a1-add
        (putnam-1996-a1-mul x y)
        (putnam-1996-a1-mul x z)))))))

(defun-sk putnam-1996-a1-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1996-a1-real-p x)
      (putnam-1996-a1-real-p y)
      (putnam-1996-a1-real-p z))
     (and
      (not (putnam-1996-a1-lt x x))
      (or
       (equal x y)
       (putnam-1996-a1-lt x y)
       (putnam-1996-a1-lt y x))
      (implies
       (and
        (putnam-1996-a1-lt x y)
        (putnam-1996-a1-lt y z))
       (putnam-1996-a1-lt x z))
      (implies
       (putnam-1996-a1-lt x y)
       (putnam-1996-a1-lt
        (putnam-1996-a1-add x z)
        (putnam-1996-a1-add y z)))
      (implies
       (and
        (putnam-1996-a1-lt
         (putnam-1996-a1-zero) x)
        (putnam-1996-a1-lt
         (putnam-1996-a1-zero) y))
       (putnam-1996-a1-lt
        (putnam-1996-a1-zero)
        (putnam-1996-a1-mul x y)))))))

(defun putnam-1996-a1-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (putnam-1996-a1-real-p (car coefficients))
       (putnam-1996-a1-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients are in ascending degree order.
(defun putnam-1996-a1-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-1996-a1-coefficient-list-p coefficients)
   (or
    (equal (len coefficients) 1)
    (not
     (equal
      (car (last coefficients))
      (putnam-1996-a1-zero))))))

(defun putnam-1996-a1-polynomial-eval (coefficients x)
  (if (consp coefficients)
      (putnam-1996-a1-add
       (car coefficients)
       (putnam-1996-a1-mul
        x
        (putnam-1996-a1-polynomial-eval
         (cdr coefficients) x)))
    (putnam-1996-a1-zero)))

(defun-sk putnam-1996-a1-square-root-exists-p (x)
  (exists (root)
    (and
     (putnam-1996-a1-real-p root)
     (equal
      (putnam-1996-a1-square root)
      x))))

(defun-sk putnam-1996-a1-nonnegative-square-root-law-p ()
  (forall (x)
    (implies
     (and
      (putnam-1996-a1-real-p x)
      (not
       (putnam-1996-a1-lt
        x (putnam-1996-a1-zero))))
     (putnam-1996-a1-square-root-exists-p x))))

(defun-sk putnam-1996-a1-polynomial-root-exists-p
    (coefficients)
  (exists (root)
    (and
     (putnam-1996-a1-real-p root)
     (equal
      (putnam-1996-a1-polynomial-eval
       coefficients root)
      (putnam-1996-a1-zero)))))

(defun-sk putnam-1996-a1-odd-polynomial-root-law-p ()
  (forall (coefficients)
    (implies
     (and
      (putnam-1996-a1-polynomial-p coefficients)
      (oddp (- (len coefficients) 1)))
     (putnam-1996-a1-polynomial-root-exists-p
      coefficients))))

(defun putnam-1996-a1-real-closed-field-p ()
  (and
   (putnam-1996-a1-real-p (putnam-1996-a1-zero))
   (putnam-1996-a1-real-p (putnam-1996-a1-one))
   (not
    (equal
     (putnam-1996-a1-zero)
     (putnam-1996-a1-one)))
   (putnam-1996-a1-lt
    (putnam-1996-a1-zero)
    (putnam-1996-a1-one))
   (putnam-1996-a1-field-laws-p)
   (putnam-1996-a1-order-laws-p)
   (putnam-1996-a1-nonnegative-square-root-law-p)
   (putnam-1996-a1-odd-polynomial-root-law-p)))

(defun putnam-1996-a1-positive-p (value)
  (and
   (putnam-1996-a1-real-p value)
   (putnam-1996-a1-lt
    (putnam-1996-a1-zero) value)))

(defun putnam-1996-a1-admissible-pair-p (n1 n2)
  (and
   (putnam-1996-a1-positive-p n1)
   (putnam-1996-a1-positive-p n2)
   (equal
    (putnam-1996-a1-add
     (putnam-1996-a1-square n1)
     (putnam-1996-a1-square n2))
    (putnam-1996-a1-one))))

(defun putnam-1996-a1-packable-p (n1 n2 side1 side2)
  (and
   (putnam-1996-a1-le
    (putnam-1996-a1-add n1 n2)
    (putnam-1996-a1-max side1 side2))
   (putnam-1996-a1-le
    (putnam-1996-a1-max n1 n2)
    (putnam-1996-a1-min side1 side2))))

(defun-sk putnam-1996-a1-packing-rectangle-exists-p
    (area n1 n2)
  (exists (side1 side2)
    (and
     (putnam-1996-a1-positive-p side1)
     (putnam-1996-a1-positive-p side2)
     (equal
      (putnam-1996-a1-mul side1 side2)
      area)
     (putnam-1996-a1-packable-p
      n1 n2 side1 side2))))

(defun-sk putnam-1996-a1-aprop-quantified-p (area)
  (forall (n1 n2)
    (implies
     (putnam-1996-a1-admissible-pair-p n1 n2)
     (putnam-1996-a1-packing-rectangle-exists-p
      area n1 n2))))

(defun putnam-1996-a1-aprop-p (area)
  (and
   (putnam-1996-a1-real-p area)
   (putnam-1996-a1-aprop-quantified-p area)))

(defun-sk putnam-1996-a1-lower-bound-p (solution)
  (forall (area)
    (implies
     (putnam-1996-a1-real-p area)
     (implies
      (putnam-1996-a1-aprop-p area)
      (putnam-1996-a1-le solution area)))))

(defun putnam-1996-a1-sqrt-two-p (sqrt-two)
  (and
   (putnam-1996-a1-positive-p sqrt-two)
   (equal
    (putnam-1996-a1-square sqrt-two)
    (putnam-1996-a1-two))))

(defun putnam-1996-a1-solution (sqrt-two)
  (putnam-1996-a1-div
   (putnam-1996-a1-add
    (putnam-1996-a1-one)
    sqrt-two)
   (putnam-1996-a1-two)))

(defun putnam-1996-a1-conclusion-at-root-p (sqrt-two)
  (let ((solution
         (putnam-1996-a1-solution sqrt-two)))
    (and
     (putnam-1996-a1-aprop-p solution)
     (putnam-1996-a1-lower-bound-p solution))))

(defun-sk putnambench-putnam-1996-a1-statement ()
  (forall (sqrt-two)
    (implies
     (and
      (putnam-1996-a1-real-closed-field-p)
      (putnam-1996-a1-sqrt-two-p sqrt-two))
     (putnam-1996-a1-conclusion-at-root-p
      sqrt-two))))

(value-triple :itpeval-statement-checked)
:q
