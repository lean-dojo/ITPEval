;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_a2:
;; a real quadratic form with negative discriminant remains nonzero near the
;; origin after adding arbitrary homogeneous cubic terms. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has only rational native scalars, so the source real numbers
;; are presented as an arbitrary linearly ordered field. The theorem is
;; algebraic and holds over every such field; no completeness or Archimedean
;; axiom is needed. In particular, the existential radius and the universal
;; points below range over the same full scalar carrier, preserving the source
;; quantifier order without a coded-number-field restriction.

(defstub p1970a2-scalar-p (x) t)
(defstub p1970a2-add-op (x y) t)
(defstub p1970a2-multiply-op (x y) t)
(defstub p1970a2-negate-op (x) t)
(defstub p1970a2-inverse-op (x) t)
(defstub p1970a2-less-op (x y) t)

(defun p1970a2-add (x y)
  (p1970a2-add-op x y))

(defun p1970a2-multiply (x y)
  (p1970a2-multiply-op x y))

(defun p1970a2-negate (x)
  (p1970a2-negate-op x))

(defun p1970a2-inverse (x)
  (p1970a2-inverse-op x))

(defun p1970a2-subtract (x y)
  (p1970a2-add x (p1970a2-negate y)))

(defun p1970a2-less-p (x y)
  (if (p1970a2-less-op x y) t nil))

(defun p1970a2-square (x)
  (p1970a2-multiply x x))

(defun p1970a2-cube (x)
  (p1970a2-multiply (p1970a2-square x) x))

(defun p1970a2-four (one)
  (p1970a2-add
   (p1970a2-add one one)
   (p1970a2-add one one)))

(defun-sk p1970a2-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1970a2-scalar-p x)
      (p1970a2-scalar-p y)
      (p1970a2-scalar-p z))
     (and
      (p1970a2-scalar-p (p1970a2-add x y))
      (p1970a2-scalar-p (p1970a2-multiply x y))
      (p1970a2-scalar-p (p1970a2-negate x))
      (implies
       (not (equal x zero))
       (p1970a2-scalar-p (p1970a2-inverse x)))
      (equal
       (p1970a2-add (p1970a2-add x y) z)
       (p1970a2-add x (p1970a2-add y z)))
      (equal (p1970a2-add x y)
             (p1970a2-add y x))
      (equal (p1970a2-add x zero) x)
      (equal
       (p1970a2-add x (p1970a2-negate x))
       zero)
      (equal
       (p1970a2-multiply (p1970a2-multiply x y) z)
       (p1970a2-multiply x (p1970a2-multiply y z)))
      (equal (p1970a2-multiply x y)
             (p1970a2-multiply y x))
      (equal (p1970a2-multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1970a2-multiply x (p1970a2-inverse x))
        one))
      (equal
       (p1970a2-multiply x (p1970a2-add y z))
       (p1970a2-add
        (p1970a2-multiply x y)
        (p1970a2-multiply x z)))))))

(defun-sk p1970a2-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1970a2-scalar-p x)
      (p1970a2-scalar-p y)
      (p1970a2-scalar-p z))
     (and
      (not (p1970a2-less-p x x))
      (or
       (equal x y)
       (p1970a2-less-p x y)
       (p1970a2-less-p y x))
      (implies
       (and
        (p1970a2-less-p x y)
        (p1970a2-less-p y z))
       (p1970a2-less-p x z))
      (implies
       (p1970a2-less-p x y)
       (p1970a2-less-p
        (p1970a2-add x z)
        (p1970a2-add y z)))
      (implies
       (and
        (p1970a2-less-p zero x)
        (p1970a2-less-p zero y))
       (p1970a2-less-p
        zero
        (p1970a2-multiply x y)))))))

(defun p1970a2-ordered-field-p (zero one)
  (and
   (p1970a2-scalar-p zero)
   (p1970a2-scalar-p one)
   (not (equal zero one))
   (p1970a2-less-p zero one)
   (p1970a2-field-laws-p zero one)
   (p1970a2-order-laws-p zero)))

(defun p1970a2-discriminant (one a b c)
  (p1970a2-subtract
   (p1970a2-square b)
   (p1970a2-multiply
    (p1970a2-four one)
    (p1970a2-multiply a c))))

(defun p1970a2-polynomial (a b c d e f g x y)
  (p1970a2-add
   (p1970a2-multiply a (p1970a2-square x))
   (p1970a2-add
    (p1970a2-multiply
     b (p1970a2-multiply x y))
    (p1970a2-add
     (p1970a2-multiply c (p1970a2-square y))
     (p1970a2-add
      (p1970a2-multiply d (p1970a2-cube x))
      (p1970a2-add
       (p1970a2-multiply
        e
        (p1970a2-multiply (p1970a2-square x) y))
       (p1970a2-add
        (p1970a2-multiply
         f
         (p1970a2-multiply x (p1970a2-square y)))
        (p1970a2-multiply g (p1970a2-cube y)))))))))

(defun p1970a2-distance-squared (x y)
  (p1970a2-add
   (p1970a2-square x)
   (p1970a2-square y)))

(defun-sk p1970a2-radius-excludes-zero-p
    (zero radius a b c d e f g)
  (forall (x y)
    (implies
     (and
      (p1970a2-scalar-p x)
      (p1970a2-scalar-p y)
      (p1970a2-less-p
       zero
       (p1970a2-distance-squared x y))
      (p1970a2-less-p
       (p1970a2-distance-squared x y)
       (p1970a2-square radius)))
     (not
      (equal
       (p1970a2-polynomial a b c d e f g x y)
       zero)))))

(defun-sk p1970a2-positive-radius-exists-p
    (zero a b c d e f g)
  (exists (radius)
    (and
     (p1970a2-scalar-p radius)
     (p1970a2-less-p zero radius)
     (p1970a2-radius-excludes-zero-p
      zero radius a b c d e f g))))

(defun putnambench-putnam-1970-a2-statement
    (zero one a b c d e f g)
  (implies
   (and
    (p1970a2-ordered-field-p zero one)
    (p1970a2-scalar-p a)
    (p1970a2-scalar-p b)
    (p1970a2-scalar-p c)
    (p1970a2-scalar-p d)
    (p1970a2-scalar-p e)
    (p1970a2-scalar-p f)
    (p1970a2-scalar-p g)
    (p1970a2-less-p
     (p1970a2-discriminant one a b c)
     zero))
   (p1970a2-positive-radius-exists-p
    zero a b c d e f g)))

(value-triple :itpeval-statement-checked)
:q
