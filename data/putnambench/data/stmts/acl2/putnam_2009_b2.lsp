;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_b2:
;; the costs attainable by finitely many strictly rightward real jumps from
;; 0 to 1 are exactly the real numbers c with 1/3 < c <= 1. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative DEFSTUB symbols present an arbitrary scalar carrier and its
;; operations without restricting them to APPLY$-tame function objects. Every
;; field, order, closure, real-closedness, and Archimedean law used below is an
;; explicit hypothesis of the statement.
;;
;; This is an exact field-independent presentation of the source real-number
;; statement. Every Archimedean real-closed ordered field embeds as a
;; real-closed ordered subfield of the reals, and model completeness transfers
;; each fixed finite-path formula in both directions.
;;
;; A path is internally existentially quantified as the finite prefix
;; s(0),...,s(n). Adjacent strict increase is equivalent to strict increase on
;; that prefix, and every such prefix ending at 1 extends to a strictly
;; increasing sequence on all naturals by continuing with 2,3,4,... .

(defstub putnam-2009-b2-carrier (x) t)
(defstub putnam-2009-b2-add-op (x y) t)
(defstub putnam-2009-b2-multiply-op (x y) t)
(defstub putnam-2009-b2-negate-op (x) t)
(defstub putnam-2009-b2-inverse-op (x) t)
(defstub putnam-2009-b2-less-op (x y) t)

(defun putnam-2009-b2-member-p (value)
  (if (putnam-2009-b2-carrier value) t nil))

(defun putnam-2009-b2-add (left right)
  (putnam-2009-b2-add-op left right))

(defun putnam-2009-b2-multiply (left right)
  (putnam-2009-b2-multiply-op left right))

(defun putnam-2009-b2-negate (value)
  (putnam-2009-b2-negate-op value))

(defun putnam-2009-b2-inverse (value)
  (putnam-2009-b2-inverse-op value))

(defun putnam-2009-b2-less-p (left right)
  (if (putnam-2009-b2-less-op left right) t nil))

(defun putnam-2009-b2-less-equal-p (left right)
  (not (putnam-2009-b2-less-p right left)))

(defun putnam-2009-b2-subtract (left right)
  (putnam-2009-b2-add
   left (putnam-2009-b2-negate right)))

(defun putnam-2009-b2-divide (numerator denominator)
  (putnam-2009-b2-multiply
   numerator (putnam-2009-b2-inverse denominator)))

(defun putnam-2009-b2-natural-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2009-b2-add
     one
     (putnam-2009-b2-natural-value (1- n) zero one))))

(defun-sk putnam-2009-b2-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-2009-b2-member-p x)
      (putnam-2009-b2-member-p y)
      (putnam-2009-b2-member-p z))
     (let* ((xy-add
             (putnam-2009-b2-add x y))
            (yz-add
             (putnam-2009-b2-add y z))
            (xy-multiply
             (putnam-2009-b2-multiply x y))
            (yz-multiply
             (putnam-2009-b2-multiply y z))
            (negative-x
             (putnam-2009-b2-negate x))
            (inverse-x
             (putnam-2009-b2-inverse x)))
       (and
        (putnam-2009-b2-member-p xy-add)
        (putnam-2009-b2-member-p xy-multiply)
        (putnam-2009-b2-member-p negative-x)
        (putnam-2009-b2-member-p inverse-x)
        (equal
         (putnam-2009-b2-add xy-add z)
         (putnam-2009-b2-add x yz-add))
        (equal xy-add
               (putnam-2009-b2-add y x))
        (equal
         (putnam-2009-b2-add x zero)
         x)
        (equal
         (putnam-2009-b2-add x negative-x)
         zero)
        (equal
         (putnam-2009-b2-multiply xy-multiply z)
         (putnam-2009-b2-multiply x yz-multiply))
        (equal
         xy-multiply
         (putnam-2009-b2-multiply y x))
        (equal
         (putnam-2009-b2-multiply x one)
         x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-2009-b2-multiply x inverse-x)
          one))
        (equal
         (putnam-2009-b2-multiply x yz-add)
         (putnam-2009-b2-add
          (putnam-2009-b2-multiply x y)
          (putnam-2009-b2-multiply x z))))))))

(defun-sk putnam-2009-b2-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (putnam-2009-b2-member-p x)
      (putnam-2009-b2-member-p y)
      (putnam-2009-b2-member-p z))
     (and
      (not (putnam-2009-b2-less-p x x))
      (or
       (equal x y)
       (putnam-2009-b2-less-p x y)
       (putnam-2009-b2-less-p y x))
      (implies
       (and
        (putnam-2009-b2-less-p x y)
        (putnam-2009-b2-less-p y z))
       (putnam-2009-b2-less-p x z))
      (implies
       (putnam-2009-b2-less-p x y)
       (putnam-2009-b2-less-p
        (putnam-2009-b2-add x z)
        (putnam-2009-b2-add y z)))
      (implies
       (and
        (putnam-2009-b2-less-p zero x)
        (putnam-2009-b2-less-p zero y))
       (putnam-2009-b2-less-p
        zero (putnam-2009-b2-multiply x y)))))))

(defun putnam-2009-b2-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (putnam-2009-b2-member-p (car coefficients))
       (putnam-2009-b2-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2009-b2-polynomial-value
    (coefficients x zero)
  (if (consp coefficients)
      (putnam-2009-b2-add
       (car coefficients)
       (putnam-2009-b2-multiply
        x
        (putnam-2009-b2-polynomial-value
         (cdr coefficients) x zero)))
    zero))

(defun putnam-2009-b2-odd-degree-polynomial-p
    (coefficients zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (evenp (len coefficients))
   (putnam-2009-b2-coefficient-list-p coefficients)
   (not (equal (car (last coefficients)) zero))))

(defun-sk putnam-2009-b2-square-root-exists-p (x)
  (exists (root)
    (and
     (putnam-2009-b2-member-p root)
     (equal
      (putnam-2009-b2-multiply root root)
      x))))

(defun-sk putnam-2009-b2-square-root-law-p (zero)
  (forall (x)
    (implies
     (and
      (putnam-2009-b2-member-p x)
      (putnam-2009-b2-less-equal-p zero x))
     (putnam-2009-b2-square-root-exists-p x))))

(defun-sk putnam-2009-b2-odd-root-exists-p
    (zero coefficients)
  (exists (root)
    (and
     (putnam-2009-b2-member-p root)
     (equal
      (putnam-2009-b2-polynomial-value
       coefficients root zero)
      zero))))

(defun-sk putnam-2009-b2-odd-root-law-p (zero)
  (forall (coefficients)
    (implies
     (putnam-2009-b2-odd-degree-polynomial-p
      coefficients zero)
     (putnam-2009-b2-odd-root-exists-p
      zero coefficients))))

(defun-sk putnam-2009-b2-archimedean-bound-exists-p
    (zero one x)
  (exists (n)
    (and
     (natp n)
     (putnam-2009-b2-less-p
      x
      (putnam-2009-b2-natural-value n zero one)))))

(defun-sk putnam-2009-b2-archimedean-law-p
    (zero one)
  (forall (x)
    (implies
     (putnam-2009-b2-member-p x)
     (putnam-2009-b2-archimedean-bound-exists-p
      zero one x))))

(defun putnam-2009-b2-real-context-p (zero one)
  (and
   (putnam-2009-b2-member-p zero)
   (putnam-2009-b2-member-p one)
   (not (equal zero one))
   (putnam-2009-b2-field-laws-p zero one)
   (putnam-2009-b2-order-laws-p zero)
   (putnam-2009-b2-less-p zero one)
   (putnam-2009-b2-square-root-law-p zero)
   (putnam-2009-b2-odd-root-law-p zero)
   (putnam-2009-b2-archimedean-law-p zero one)))

(defun putnam-2009-b2-carrier-list-p (values)
  (if (consp values)
      (and
       (putnam-2009-b2-member-p (car values))
       (putnam-2009-b2-carrier-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2009-b2-adjacent-increasing-p (values)
  (if (and (consp values)
           (consp (cdr values)))
      (and
       (putnam-2009-b2-less-p
        (car values) (cadr values))
       (putnam-2009-b2-adjacent-increasing-p
        (cdr values)))
    t))

(defun putnam-2009-b2-jump-cost (left right)
  (let* ((right-squared
          (putnam-2009-b2-multiply right right))
         (right-cubed
          (putnam-2009-b2-multiply right right-squared))
         (left-times-right-squared
          (putnam-2009-b2-multiply left right-squared)))
    (putnam-2009-b2-subtract
     right-cubed left-times-right-squared)))

(defun putnam-2009-b2-total-cost (values zero)
  (if (and (consp values)
           (consp (cdr values)))
      (putnam-2009-b2-add
       (putnam-2009-b2-jump-cost
        (car values) (cadr values))
       (putnam-2009-b2-total-cost
        (cdr values) zero))
    zero))

(defun putnam-2009-b2-path-witness-p
    (path c zero one)
  (and
   (true-listp path)
   (consp path)
   (consp (cdr path))
   (putnam-2009-b2-carrier-list-p path)
   (equal (car path) zero)
   (equal (car (last path)) one)
   (putnam-2009-b2-adjacent-increasing-p path)
   (equal
    (putnam-2009-b2-total-cost path zero)
    c)))

(defun-sk putnam-2009-b2-attainable-p
    (c zero one)
  (exists (path)
    (putnam-2009-b2-path-witness-p
     path c zero one)))

(defun putnam-2009-b2-one-third (one)
  (let ((three
         (putnam-2009-b2-add
          one (putnam-2009-b2-add one one))))
    (putnam-2009-b2-divide one three)))

(defun putnam-2009-b2-in-solution-interval-p
    (c one)
  (and
   (putnam-2009-b2-less-p
    (putnam-2009-b2-one-third one)
    c)
   (putnam-2009-b2-less-equal-p c one)))

(defun-sk putnambench-putnam-2009-b2-statement
    (zero one)
  (forall (c)
    (implies
     (and
      (putnam-2009-b2-real-context-p zero one)
      (putnam-2009-b2-member-p c))
     (iff
      (putnam-2009-b2-attainable-p c zero one)
      (putnam-2009-b2-in-solution-interval-p
       c one)))))

(value-triple :itpeval-statement-checked)
:q
