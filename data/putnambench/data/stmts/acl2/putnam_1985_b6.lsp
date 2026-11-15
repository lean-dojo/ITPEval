;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_b6:
;; a finite group of real square matrices whose traces sum to zero has zero
;; matrix sum. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar interface presents an arbitrary real-closed ordered field.
;; Matrices below contain arbitrary carrier values, so the statement directly
;; ranges over all finite real matrix groups rather than an algebraic subset.

(defstub putnam-1985-b6-real-p (real-type value) t)
(defstub putnam-1985-b6-zero (real-type) t)
(defstub putnam-1985-b6-one (real-type) t)
(defstub putnam-1985-b6-add (real-type left right) t)
(defstub putnam-1985-b6-mul (real-type left right) t)
(defstub putnam-1985-b6-neg (real-type value) t)
(defstub putnam-1985-b6-inv (real-type value) t)
(defstub putnam-1985-b6-less (real-type left right) t)

(defun putnam-1985-b6-leq (real-type left right)
  (not (putnam-1985-b6-less real-type right left)))

(defun-sk putnam-1985-b6-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1985-b6-real-p real-type x)
      (putnam-1985-b6-real-p real-type y)
      (putnam-1985-b6-real-p real-type z))
     (let* ((zero (putnam-1985-b6-zero real-type))
            (one (putnam-1985-b6-one real-type))
            (x-plus-y (putnam-1985-b6-add real-type x y))
            (y-plus-z (putnam-1985-b6-add real-type y z))
            (x-times-y (putnam-1985-b6-mul real-type x y))
            (y-times-z (putnam-1985-b6-mul real-type y z))
            (minus-x (putnam-1985-b6-neg real-type x))
            (inverse-x (putnam-1985-b6-inv real-type x)))
       (and
        (putnam-1985-b6-real-p real-type x-plus-y)
        (putnam-1985-b6-real-p real-type x-times-y)
        (putnam-1985-b6-real-p real-type minus-x)
        (putnam-1985-b6-real-p real-type inverse-x)
        (equal
         (putnam-1985-b6-add real-type x-plus-y z)
         (putnam-1985-b6-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1985-b6-add real-type y x))
        (equal (putnam-1985-b6-add real-type x zero) x)
        (equal (putnam-1985-b6-add real-type x minus-x) zero)
        (equal
         (putnam-1985-b6-mul real-type x-times-y z)
         (putnam-1985-b6-mul real-type x y-times-z))
        (equal x-times-y (putnam-1985-b6-mul real-type y x))
        (equal (putnam-1985-b6-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1985-b6-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1985-b6-mul real-type x y-plus-z)
         (putnam-1985-b6-add
          real-type
          (putnam-1985-b6-mul real-type x y)
          (putnam-1985-b6-mul real-type x z))))))))

(defun-sk putnam-1985-b6-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1985-b6-real-p real-type x)
      (putnam-1985-b6-real-p real-type y)
      (putnam-1985-b6-real-p real-type z))
     (let ((zero (putnam-1985-b6-zero real-type)))
       (and
        (not (putnam-1985-b6-less real-type x x))
        (or
         (putnam-1985-b6-less real-type x y)
         (equal x y)
         (putnam-1985-b6-less real-type y x))
        (implies
         (and
          (putnam-1985-b6-less real-type x y)
          (putnam-1985-b6-less real-type y z))
         (putnam-1985-b6-less real-type x z))
        (implies
         (putnam-1985-b6-less real-type x y)
         (putnam-1985-b6-less
          real-type
          (putnam-1985-b6-add real-type x z)
          (putnam-1985-b6-add real-type y z)))
        (implies
         (and
          (putnam-1985-b6-less real-type zero x)
          (putnam-1985-b6-less real-type zero y))
         (putnam-1985-b6-less
          real-type
          zero
          (putnam-1985-b6-mul real-type x y))))))))

(defun putnam-1985-b6-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1985-b6-real-p real-type (car values))
       (putnam-1985-b6-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1985-b6-polynomial-value
    (real-type coefficients x)
  (if (consp coefficients)
      (putnam-1985-b6-add
       real-type
       (car coefficients)
       (putnam-1985-b6-mul
        real-type
        x
        (putnam-1985-b6-polynomial-value
         real-type (cdr coefficients) x)))
    (putnam-1985-b6-zero real-type)))

(defun-sk putnam-1985-b6-square-root-exists-p
    (real-type x)
  (exists (root)
    (and
     (putnam-1985-b6-real-p real-type root)
     (putnam-1985-b6-leq
      real-type (putnam-1985-b6-zero real-type) root)
     (equal
      (putnam-1985-b6-mul real-type root root)
      x))))

(defun-sk putnam-1985-b6-square-root-property-p
    (real-type)
  (forall (x)
    (implies
     (and
      (putnam-1985-b6-real-p real-type x)
      (putnam-1985-b6-leq
       real-type (putnam-1985-b6-zero real-type) x))
     (putnam-1985-b6-square-root-exists-p
      real-type x))))

(defun putnam-1985-b6-odd-degree-polynomial-p
    (real-type coefficients)
  (and
   (true-listp coefficients)
   (<= 2 (len coefficients))
   (evenp (len coefficients))
   (putnam-1985-b6-real-list-p real-type coefficients)
   (not
    (equal
     (car (last coefficients))
     (putnam-1985-b6-zero real-type)))))

(defun-sk putnam-1985-b6-polynomial-root-exists-p
    (real-type coefficients)
  (exists (root)
    (and
     (putnam-1985-b6-real-p real-type root)
     (equal
      (putnam-1985-b6-polynomial-value
       real-type coefficients root)
      (putnam-1985-b6-zero real-type)))))

(defun-sk putnam-1985-b6-odd-degree-root-property-p
    (real-type)
  (forall (coefficients)
    (implies
     (putnam-1985-b6-odd-degree-polynomial-p
      real-type coefficients)
     (putnam-1985-b6-polynomial-root-exists-p
      real-type coefficients))))

(defun putnam-1985-b6-real-closed-field-p (real-type)
  (let ((zero (putnam-1985-b6-zero real-type))
        (one (putnam-1985-b6-one real-type)))
    (and
     (putnam-1985-b6-real-p real-type zero)
     (putnam-1985-b6-real-p real-type one)
     (not (equal zero one))
     (putnam-1985-b6-field-laws-p real-type)
     (putnam-1985-b6-order-laws-p real-type)
     (putnam-1985-b6-less real-type zero one)
     (putnam-1985-b6-square-root-property-p real-type)
     (putnam-1985-b6-odd-degree-root-property-p real-type))))

;; Matrices are flat row-major true lists of n*n arbitrary carrier values.

(defun putnam-1985-b6-matrix-p (real-type n matrix)
  (and
   (natp n)
   (true-listp matrix)
   (equal (len matrix) (* n n))
   (putnam-1985-b6-real-list-p real-type matrix)))

(defun putnam-1985-b6-matrix-list-p
    (real-type n matrices)
  (if (consp matrices)
      (and
       (putnam-1985-b6-matrix-p
        real-type n (car matrices))
       (putnam-1985-b6-matrix-list-p
        real-type n (cdr matrices)))
    (equal matrices nil)))

(defun putnam-1985-b6-zero-list (real-type count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (putnam-1985-b6-zero real-type)
     (putnam-1985-b6-zero-list
      real-type (- count 1)))))

(defun putnam-1985-b6-zero-matrix (real-type n)
  (putnam-1985-b6-zero-list real-type (* n n)))

(defun putnam-1985-b6-identity-entries
    (real-type n index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let ((row (floor (nfix index) n))
          (column (mod (nfix index) n)))
      (cons
       (if (equal row column)
           (putnam-1985-b6-one real-type)
         (putnam-1985-b6-zero real-type))
       (putnam-1985-b6-identity-entries
        real-type n (+ index 1) (- remaining 1))))))

(defun putnam-1985-b6-identity-matrix (real-type n)
  (if (posp n)
      (putnam-1985-b6-identity-entries
       real-type n 0 (* n n))
    nil))

(defun putnam-1985-b6-matrix-add
    (real-type left right)
  (if (consp left)
      (cons
       (putnam-1985-b6-add
        real-type (car left) (car right))
       (putnam-1985-b6-matrix-add
        real-type (cdr left) (cdr right)))
    nil))

(defun putnam-1985-b6-dot-product
    (real-type n row column left right k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (putnam-1985-b6-zero real-type)
    (let* ((index (- k 1))
           (left-entry
            (nth (+ (* row n) index) left))
           (right-entry
            (nth (+ (* index n) column) right)))
      (putnam-1985-b6-add
       real-type
       (putnam-1985-b6-mul
        real-type left-entry right-entry)
       (putnam-1985-b6-dot-product
        real-type n row column left right index)))))

(defun putnam-1985-b6-matrix-product-entries
    (real-type n left right index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let ((row (floor (nfix index) n))
          (column (mod (nfix index) n)))
      (cons
       (putnam-1985-b6-dot-product
        real-type n row column left right n)
       (putnam-1985-b6-matrix-product-entries
        real-type
        n
        left
        right
        (+ index 1)
        (- remaining 1))))))

(defun putnam-1985-b6-matrix-product
    (real-type n left right)
  (if (posp n)
      (putnam-1985-b6-matrix-product-entries
       real-type n left right 0 (* n n))
    nil))

(defun putnam-1985-b6-trace-aux
    (real-type n matrix index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-1985-b6-zero real-type)
    (putnam-1985-b6-add
     real-type
     (nth (+ (* index n) index) matrix)
     (putnam-1985-b6-trace-aux
      real-type n matrix (+ index 1) (- remaining 1)))))

(defun putnam-1985-b6-trace (real-type n matrix)
  (putnam-1985-b6-trace-aux
   real-type n matrix 0 n))

(defun putnam-1985-b6-trace-sum
    (real-type n matrices)
  (if (consp matrices)
      (putnam-1985-b6-add
       real-type
       (putnam-1985-b6-trace
        real-type n (car matrices))
       (putnam-1985-b6-trace-sum
        real-type n (cdr matrices)))
    (putnam-1985-b6-zero real-type)))

(defun putnam-1985-b6-matrix-sum
    (real-type n matrices)
  (if (consp matrices)
      (putnam-1985-b6-matrix-add
       real-type
       (car matrices)
       (putnam-1985-b6-matrix-sum
        real-type n (cdr matrices)))
    (putnam-1985-b6-zero-matrix real-type n)))

;; The list has set semantics through no-duplicatesp-equal. Closure,
;; identity, and a right inverse inside the list reproduce groupG exactly.

(defun putnam-1985-b6-products-in-group-p
    (real-type n left rights group)
  (if (consp rights)
      (and
       (member-equal
        (putnam-1985-b6-matrix-product
         real-type n left (car rights))
        group)
       (putnam-1985-b6-products-in-group-p
        real-type n left (cdr rights) group))
    t))

(defun putnam-1985-b6-closed-p
    (real-type n remaining group)
  (if (consp remaining)
      (and
       (putnam-1985-b6-products-in-group-p
        real-type n (car remaining) group group)
       (putnam-1985-b6-closed-p
        real-type n (cdr remaining) group))
    t))

(defun putnam-1985-b6-right-inverse-in-group-p
    (real-type n matrix candidates identity)
  (if (consp candidates)
      (or
       (equal
        (putnam-1985-b6-matrix-product
         real-type n matrix (car candidates))
        identity)
       (putnam-1985-b6-right-inverse-in-group-p
        real-type
        n
        matrix
        (cdr candidates)
        identity))
    nil))

(defun putnam-1985-b6-all-right-inverses-p
    (real-type n remaining group identity)
  (if (consp remaining)
      (and
       (putnam-1985-b6-right-inverse-in-group-p
        real-type n (car remaining) group identity)
       (putnam-1985-b6-all-right-inverses-p
        real-type n (cdr remaining) group identity))
    t))

(defun putnam-1985-b6-group-p
    (real-type n matrices)
  (let ((identity
         (putnam-1985-b6-identity-matrix real-type n)))
    (and
     (true-listp matrices)
     (putnam-1985-b6-matrix-list-p
      real-type n matrices)
     (no-duplicatesp-equal matrices)
     (putnam-1985-b6-closed-p
      real-type n matrices matrices)
     (member-equal identity matrices)
     (putnam-1985-b6-all-right-inverses-p
      real-type n matrices matrices identity))))

(defun putnambench-putnam-1985-b6-statement
    (real-type n matrices)
  (implies
   (and
    (putnam-1985-b6-real-closed-field-p real-type)
    (posp n)
    (putnam-1985-b6-group-p real-type n matrices)
    (equal
     (putnam-1985-b6-trace-sum
      real-type n matrices)
     (putnam-1985-b6-zero real-type)))
   (equal
    (putnam-1985-b6-matrix-sum
     real-type n matrices)
    (putnam-1985-b6-zero-matrix real-type n))))

(value-triple :itpeval-statement-checked)
:q
