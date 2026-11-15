;; Statement-only formalization of Hundred Theorems artifact 061,
;; "Theorem of Ceva." In a nondegenerate real triangle, points X, Y, Z lie
;; on the three side lines and the cevians AX, BY, CZ are concurrent. The
;; corresponding products of Euclidean distances are equal. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive full real-number sort. The scalar operations below
;; therefore describe an arbitrary real-closed ordered field, with every
;; algebraic, order, and real-closure law used by the statement made explicit.

(defstub ht061-carrier (x) t)
(defstub ht061-add-op (x y) t)
(defstub ht061-multiply-op (x y) t)
(defstub ht061-negate-op (x) t)
(defstub ht061-inverse-op (x) t)
(defstub ht061-less-op (x y) t)

(defun ht061-member-p (x)
  (if (ht061-carrier x) t nil))

(defun ht061-add (x y)
  (ht061-add-op x y))

(defun ht061-multiply (x y)
  (ht061-multiply-op x y))

(defun ht061-negate (x)
  (ht061-negate-op x))

(defun ht061-inverse (x)
  (ht061-inverse-op x))

(defun ht061-subtract (x y)
  (ht061-add x (ht061-negate y)))

(defun ht061-less (x y)
  (if (ht061-less-op x y) t nil))

(defun ht061-square (x)
  (ht061-multiply x x))

(defun-sk ht061-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht061-member-p x)
      (ht061-member-p y)
      (ht061-member-p z))
     (and
      (ht061-member-p (ht061-add x y))
      (ht061-member-p (ht061-multiply x y))
      (ht061-member-p (ht061-negate x))
      (ht061-member-p (ht061-inverse x))
      (equal (ht061-add (ht061-add x y) z)
             (ht061-add x (ht061-add y z)))
      (equal (ht061-add x y)
             (ht061-add y x))
      (equal (ht061-add x zero) x)
      (equal (ht061-add x (ht061-negate x)) zero)
      (equal (ht061-multiply (ht061-multiply x y) z)
             (ht061-multiply x (ht061-multiply y z)))
      (equal (ht061-multiply x y)
             (ht061-multiply y x))
      (equal (ht061-multiply x one) x)
      (equal
       (ht061-multiply x (ht061-add y z))
       (ht061-add
        (ht061-multiply x y)
        (ht061-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht061-multiply x (ht061-inverse x))
        one))))))

(defun-sk ht061-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht061-member-p x)
      (ht061-member-p y)
      (ht061-member-p z))
     (and
      (not (ht061-less x x))
      (or
       (equal x y)
       (ht061-less x y)
       (ht061-less y x))
      (implies
       (and
        (ht061-less x y)
        (ht061-less y z))
       (ht061-less x z))
      (implies
       (ht061-less x y)
       (ht061-less
        (ht061-add x z)
        (ht061-add y z)))
      (implies
       (and
        (ht061-less zero x)
        (ht061-less zero y))
       (ht061-less zero (ht061-multiply x y)))))))

(defun ht061-carrier-list-p (values)
  (if (consp values)
      (and
       (ht061-member-p (car values))
       (ht061-carrier-list-p (cdr values)))
    (equal values nil)))

(defun ht061-polynomial-value (coefficients x zero)
  (if (consp coefficients)
      (ht061-add
       (car coefficients)
       (ht061-multiply
        x
        (ht061-polynomial-value
         (cdr coefficients) x zero)))
    zero))

(defun ht061-odd-degree-polynomial-p
    (coefficients zero)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht061-carrier-list-p coefficients)
   (evenp (len coefficients))
   (not (equal (car (last coefficients)) zero))))

(defun-sk ht061-has-square-root-p (x)
  (exists (root)
    (and
     (ht061-member-p root)
     (equal (ht061-square root) x))))

(defun-sk ht061-polynomial-has-root-p
    (coefficients zero)
  (exists (root)
    (and
     (ht061-member-p root)
     (equal
      (ht061-polynomial-value coefficients root zero)
      zero))))

(defun-sk ht061-real-closure-laws-p (zero)
  (forall (x coefficients)
    (and
     (implies
      (and
       (ht061-member-p x)
       (not (ht061-less x zero)))
      (ht061-has-square-root-p x))
     (implies
      (ht061-odd-degree-polynomial-p coefficients zero)
      (ht061-polynomial-has-root-p coefficients zero)))))

(defun ht061-real-scalar-context-p (zero one)
  (and
   (ht061-member-p zero)
   (ht061-member-p one)
   (not (equal zero one))
   (ht061-less zero one)
   (ht061-field-laws-p zero one)
   (ht061-order-laws-p zero)
   (ht061-real-closure-laws-p zero)))

;; A point is a dotted pair (x . y) of field elements.

(defun ht061-point-p (point)
  (and
   (consp point)
   (ht061-member-p (car point))
   (ht061-member-p (cdr point))))

(defun ht061-collinear-p (point-a point-b point-c)
  (equal
   (ht061-multiply
    (ht061-subtract (car point-b) (car point-a))
    (ht061-subtract (cdr point-c) (cdr point-a)))
   (ht061-multiply
    (ht061-subtract (cdr point-b) (cdr point-a))
    (ht061-subtract (car point-c) (car point-a)))))

(defun ht061-distance-squared (left right)
  (let ((dx (ht061-subtract (car left) (car right)))
        (dy (ht061-subtract (cdr left) (cdr right))))
    (ht061-add
     (ht061-square dx)
     (ht061-square dy))))

(defun ht061-distance-value-p
    (left right distance zero)
  (and
   (ht061-point-p left)
   (ht061-point-p right)
   (ht061-member-p distance)
   (not (ht061-less distance zero))
   (equal
    (ht061-square distance)
    (ht061-distance-squared left right))))

(defun ht061-ceva-configuration-p
    (point-a point-b point-c
     point-x point-y point-z concurrent-point
     distance-bx distance-cy distance-az
     distance-xc distance-ya distance-zb
     zero)
  (and
   (ht061-point-p point-a)
   (ht061-point-p point-b)
   (ht061-point-p point-c)
   (ht061-point-p point-x)
   (ht061-point-p point-y)
   (ht061-point-p point-z)
   (ht061-point-p concurrent-point)
   (not (ht061-collinear-p point-a point-b point-c))

   ;; X, Y, Z lie on BC, CA, AB.
   (ht061-collinear-p point-b point-x point-c)
   (ht061-collinear-p point-c point-y point-a)
   (ht061-collinear-p point-a point-z point-b)

   ;; The three cevians are concurrent.
   (ht061-collinear-p point-a concurrent-point point-x)
   (ht061-collinear-p point-b concurrent-point point-y)
   (ht061-collinear-p point-c concurrent-point point-z)

   ;; These six nonnegative values are the Euclidean distances in the source.
   (ht061-distance-value-p
    point-b point-x distance-bx zero)
   (ht061-distance-value-p
    point-c point-y distance-cy zero)
   (ht061-distance-value-p
    point-a point-z distance-az zero)
   (ht061-distance-value-p
    point-x point-c distance-xc zero)
   (ht061-distance-value-p
    point-y point-a distance-ya zero)
   (ht061-distance-value-p
    point-z point-b distance-zb zero)))

(defun ht061-ceva-product (first second third)
  (ht061-multiply
   first
   (ht061-multiply second third)))

(defun-sk hundred-theorems-061-theorem-of-ceva-statement
    (zero one)
  (forall
   (point-a point-b point-c
    point-x point-y point-z concurrent-point
    distance-bx distance-cy distance-az
    distance-xc distance-ya distance-zb)
   (implies
    (and
     (ht061-real-scalar-context-p zero one)
     (ht061-ceva-configuration-p
      point-a point-b point-c
      point-x point-y point-z concurrent-point
      distance-bx distance-cy distance-az
      distance-xc distance-ya distance-zb
      zero))
    (equal
     (ht061-ceva-product
      distance-bx distance-cy distance-az)
     (ht061-ceva-product
      distance-xc distance-ya distance-zb)))))

(value-triple :itpeval-statement-checked)
:q
