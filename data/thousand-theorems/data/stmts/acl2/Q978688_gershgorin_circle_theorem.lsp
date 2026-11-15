;; Statement-only formalization of thousand-theorems corpus artifact Q978688,
;; "Gershgorin circle theorem": every eigenvalue of a finite square matrix
;; over an arbitrary normed field lies in a closed ball centered at a diagonal
;; entry with radius the sum of the off-diagonal row norms.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces present arbitrary index carriers, field
;; carriers, field operations, and norm upper cuts. Q978688-NORM-LT(FIELD,X,Q)
;; means ||X|| < Q for the positive rational Q.

(defstub q978688-index-member-p (index-type index) t)
(defstub q978688-field-member-p (field value) t)
(defstub q978688-zero (field) t)
(defstub q978688-one (field) t)
(defstub q978688-add (field left right) t)
(defstub q978688-multiply (field left right) t)
(defstub q978688-negate (field value) t)
(defstub q978688-inverse (field value) t)
(defstub q978688-norm-lt (field value rational-bound) t)

(defun q978688-positive-rational-p (value)
  (and (rationalp value)
       (< 0 value)))

(defun q978688-subtract (field left right)
  (q978688-add
   field left (q978688-negate field right)))

;; An exhaustive duplicate-free list is a presentation, not a restriction, of
;; the arbitrary finite index type. Tables aligned with this list are
;; bijective representations of functions on that finite carrier.

(defun-sk q978688-index-exhaustive-p (index-type indices)
  (forall (index)
    (iff
     (q978688-index-member-p index-type index)
     (member-equal index indices))))

(defun q978688-finite-index-p (index-type indices)
  (and
   (true-listp indices)
   (no-duplicatesp-equal indices)
   (q978688-index-exhaustive-p index-type indices)))

;; Rounded, inhabited rational upper cuts represent finite nonnegative real
;; numbers exactly. The following auxiliary predicates keep all quantifiers
;; internal to the ACL2 statement.

(defun-sk q978688-norm-finite-p (field value)
  (exists (bound)
    (and
     (q978688-positive-rational-p bound)
     (q978688-norm-lt field value bound))))

(defun-sk q978688-norm-rounded-p (field value bound)
  (exists (smaller)
    (and
     (q978688-positive-rational-p smaller)
     (rationalp bound)
     (< smaller bound)
     (q978688-norm-lt field value smaller))))

(defun-sk q978688-zero-cut-p (field value)
  (forall (bound)
    (implies
     (q978688-positive-rational-p bound)
     (q978688-norm-lt field value bound))))

(defun-sk q978688-product-cut-p (field left right bound)
  (exists (left-bound right-bound)
    (and
     (q978688-positive-rational-p bound)
     (q978688-positive-rational-p left-bound)
     (q978688-positive-rational-p right-bound)
     (q978688-norm-lt field left left-bound)
     (q978688-norm-lt field right right-bound)
     (< (* left-bound right-bound) bound))))

;; Exact first-order presentation of a normed field. The cut equations state
;; definiteness, negation invariance, the triangle inequality, and
;; multiplicativity of the norm without replacing real values by rationals.

(defun-sk q978688-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (q978688-field-member-p field x)
      (q978688-field-member-p field y)
      (q978688-field-member-p field z))
     (let* ((zero (q978688-zero field))
            (one (q978688-one field))
            (xy-add (q978688-add field x y))
            (yz-add (q978688-add field y z))
            (xy-mul (q978688-multiply field x y))
            (yz-mul (q978688-multiply field y z))
            (neg-x (q978688-negate field x))
            (inv-x (q978688-inverse field x)))
       (and
        (q978688-field-member-p field xy-add)
        (q978688-field-member-p field xy-mul)
        (q978688-field-member-p field neg-x)
        (q978688-field-member-p field inv-x)
        (equal
         (q978688-add field xy-add z)
         (q978688-add field x yz-add))
        (equal xy-add (q978688-add field y x))
        (equal (q978688-add field x zero) x)
        (equal (q978688-add field x neg-x) zero)
        (equal
         (q978688-multiply field xy-mul z)
         (q978688-multiply field x yz-mul))
        (equal xy-mul (q978688-multiply field y x))
        (equal (q978688-multiply field x one) x)
        (equal
         (q978688-multiply field x yz-add)
         (q978688-add
          field
          (q978688-multiply field x y)
          (q978688-multiply field x z)))
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q978688-multiply field x inv-x)
          one)))))))

(defun-sk q978688-norm-cut-laws-p (field)
  (forall (x bound larger)
    (implies
     (q978688-field-member-p field x)
     (and
      (q978688-norm-finite-p field x)
      (implies
       (q978688-norm-lt field x bound)
       (q978688-positive-rational-p bound))
      (implies
       (and
        (q978688-norm-lt field x bound)
        (rationalp larger)
        (< bound larger))
       (q978688-norm-lt field x larger))
      (iff
       (q978688-norm-lt field x bound)
       (and
        (q978688-positive-rational-p bound)
        (q978688-norm-rounded-p field x bound)))))))

(defun-sk q978688-norm-zero-laws-p (field)
  (forall (x)
    (implies
     (q978688-field-member-p field x)
     (iff
      (equal x (q978688-zero field))
      (q978688-zero-cut-p field x)))))

(defun-sk q978688-norm-negation-laws-p (field)
  (forall (x bound)
    (implies
     (q978688-field-member-p field x)
     (iff
      (q978688-norm-lt
       field (q978688-negate field x) bound)
      (q978688-norm-lt field x bound)))))

(defun-sk q978688-norm-triangle-laws-p (field)
  (forall (x y left-bound right-bound)
    (implies
     (and
      (q978688-field-member-p field x)
      (q978688-field-member-p field y)
      (q978688-positive-rational-p left-bound)
      (q978688-positive-rational-p right-bound)
      (q978688-norm-lt field x left-bound)
      (q978688-norm-lt field y right-bound))
     (q978688-norm-lt
      field
      (q978688-add field x y)
      (+ left-bound right-bound)))))

(defun-sk q978688-norm-product-laws-p (field)
  (forall (x y bound)
    (implies
     (and
      (q978688-field-member-p field x)
      (q978688-field-member-p field y))
     (iff
      (q978688-norm-lt
       field (q978688-multiply field x y) bound)
      (and
       (q978688-positive-rational-p bound)
       (q978688-product-cut-p
        field x y bound))))))

(defun q978688-normed-field-p (field)
  (let ((zero (q978688-zero field))
        (one (q978688-one field)))
    (and
     (q978688-field-member-p field zero)
     (q978688-field-member-p field one)
     (not (equal zero one))
     (q978688-field-laws-p field)
     (q978688-norm-cut-laws-p field)
     (q978688-norm-zero-laws-p field)
     (q978688-norm-negation-laws-p field)
     (q978688-norm-triangle-laws-p field)
     (q978688-norm-product-laws-p field))))

;; Matrices and vectors are exact finite-function tables aligned with INDICES.

(defun q978688-field-list-p (field values)
  (if (consp values)
      (and
       (q978688-field-member-p field (car values))
       (q978688-field-list-p field (cdr values)))
    (equal values nil)))

(defun q978688-vector-p (field indices vector)
  (and
   (true-listp vector)
   (equal (len vector) (len indices))
   (q978688-field-list-p field vector)))

(defun q978688-matrix-rows-p (field indices rows)
  (if (consp rows)
      (and
       (q978688-vector-p field indices (car rows))
       (q978688-matrix-rows-p field indices (cdr rows)))
    (equal rows nil)))

(defun q978688-matrix-p (field indices matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) (len indices))
   (q978688-matrix-rows-p field indices matrix)))

(defun q978688-lookup-aligned (key keys values default)
  (cond
   ((or (endp keys) (endp values)) default)
   ((equal key (car keys)) (car values))
   (t
    (q978688-lookup-aligned
     key (cdr keys) (cdr values) default))))

(defun q978688-vector-nonzero-p (field vector)
  (if (consp vector)
      (or
       (not (equal (car vector) (q978688-zero field)))
       (q978688-vector-nonzero-p field (cdr vector)))
    nil))

(defun q978688-dot-product (field row vector)
  (if (and (consp row) (consp vector))
      (q978688-add
       field
       (q978688-multiply field (car row) (car vector))
       (q978688-dot-product field (cdr row) (cdr vector)))
    (q978688-zero field)))

(defun q978688-eigen-equations-p
    (field rows vector eigenvalue)
  (if (and (consp rows) (consp vector))
      (and
       (equal
        (q978688-dot-product field (car rows) vector)
        (q978688-multiply field eigenvalue (car vector)))
       (q978688-eigen-equations-p
        field (cdr rows) (cdr vector) eigenvalue))
    (and (endp rows) (endp vector))))

(defun q978688-eigenvector-p
    (field indices matrix eigenvalue vector)
  (and
   (q978688-vector-p field indices vector)
   (q978688-vector-nonzero-p field vector)
   (q978688-eigen-equations-p
    field matrix vector eigenvalue)))

(defun-sk q978688-has-eigenvalue-p
    (field indices matrix eigenvalue)
  (exists (vector)
    (q978688-eigenvector-p
     field indices matrix eigenvalue vector)))

;; The strict upper cut of the finite off-diagonal norm sum is represented by
;; simultaneous rational upper bounds for its finitely many summands.

(defun q978688-rational-list-sum (values)
  (if (consp values)
      (+ (car values)
         (q978688-rational-list-sum (cdr values)))
    0))

(defun q978688-offdiag-bounds-p
    (field columns row-key row bounds)
  (cond
   ((or (endp columns) (endp row))
    (and
     (endp columns)
     (endp row)
     (endp bounds)))
   ((equal row-key (car columns))
    (q978688-offdiag-bounds-p
     field (cdr columns) row-key (cdr row) bounds))
   (t
    (and
     (consp bounds)
     (q978688-positive-rational-p (car bounds))
     (q978688-norm-lt field (car row) (car bounds))
     (q978688-offdiag-bounds-p
      field (cdr columns) row-key (cdr row) (cdr bounds))))))

(defun q978688-row-sum-witness-p
    (field indices row-key row bound bounds)
  (and
   (q978688-positive-rational-p bound)
   (true-listp bounds)
   (q978688-offdiag-bounds-p
    field indices row-key row bounds)
   (< (q978688-rational-list-sum bounds) bound)))

(defun-sk q978688-row-sum-lt-p
    (field indices row-key row bound)
  (exists (bounds)
    (q978688-row-sum-witness-p
     field indices row-key row bound bounds)))

;; Inclusion of rational upper cuts is exactly
;; ||eigenvalue - A(k,k)|| <= sum_(j != k) ||A(k,j)||.

(defun-sk q978688-row-bound-p
    (field indices row-key row eigenvalue)
  (forall (bound)
    (implies
     (q978688-row-sum-lt-p
      field indices row-key row bound)
     (q978688-norm-lt
      field
      (q978688-subtract
       field
       eigenvalue
       (q978688-lookup-aligned
        row-key indices row (q978688-zero field)))
      bound))))

(defun-sk q978688-some-row-bound-p
    (field index-type indices matrix eigenvalue)
  (exists (row-key)
    (and
     (q978688-index-member-p index-type row-key)
     (q978688-row-bound-p
      field
      indices
      row-key
      (q978688-lookup-aligned
       row-key indices matrix nil)
      eigenvalue))))

(defun thousand-theorems-q978688-gershgorin-circle-theorem-statement
    (field index-type indices matrix eigenvalue)
  (implies
   (and
    (q978688-normed-field-p field)
    (q978688-finite-index-p index-type indices)
    (q978688-matrix-p field indices matrix)
    (q978688-field-member-p field eigenvalue)
    (q978688-has-eigenvalue-p
     field indices matrix eigenvalue))
   (q978688-some-row-bound-p
    field index-type indices matrix eigenvalue)))

(value-triple :itpeval-statement-checked)
:q
