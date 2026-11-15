;; Statement-only formalization of thousand-theorems corpus artifact Q1752621,
;; "Sylvester's law of inertia": every finite-dimensional real quadratic form
;; is linearly equivalent to a weighted sum of squares with weights -1, 0, or
;; 1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite-dimensional real quadratic form becomes a symmetric matrix after
;; choosing a basis. Its equivalence to a weighted sum of squares is exactly
;; congruence
;;
;;                     A = transpose(T) diag(w) T
;;
;; for an invertible matrix T. The scalar field below is an arbitrary real
;; closed ordered field. Real closed fields have the same first-order theory,
;; so the resulting finite matrix sentence is equivalent to the source
;; statement over the real numbers. The carrier remains unbounded; only the
;; matrices are finite, as required by finite dimensionality.

;; Conservative generic symbols for the scalar field.

(defstub q1752621-scalar-p (x) t)
(defstub q1752621-zero () t)
(defstub q1752621-one () t)
(defstub q1752621-add (x y) t)
(defstub q1752621-mul (x y) t)
(defstub q1752621-neg (x) t)
(defstub q1752621-inv (x) t)
(defstub q1752621-lt (x y) t)

;; Field and order laws.

(defun-sk q1752621-field-laws-p ()
  (forall (x y z)
    (and
     (implies
      (and
       (q1752621-scalar-p x)
       (q1752621-scalar-p y))
      (and
       (q1752621-scalar-p (q1752621-add x y))
       (q1752621-scalar-p (q1752621-mul x y))
       (equal (q1752621-add x y)
              (q1752621-add y x))
       (equal (q1752621-mul x y)
              (q1752621-mul y x))))
     (implies
      (q1752621-scalar-p x)
      (and
       (q1752621-scalar-p (q1752621-neg x))
       (q1752621-scalar-p (q1752621-inv x))
       (equal (q1752621-add x (q1752621-zero)) x)
       (equal (q1752621-add x (q1752621-neg x))
              (q1752621-zero))
       (equal (q1752621-mul x (q1752621-one)) x)
       (implies
        (not (equal x (q1752621-zero)))
        (equal (q1752621-mul x (q1752621-inv x))
               (q1752621-one)))))
     (implies
      (and
       (q1752621-scalar-p x)
       (q1752621-scalar-p y)
       (q1752621-scalar-p z))
      (and
       (equal
        (q1752621-add (q1752621-add x y) z)
        (q1752621-add x (q1752621-add y z)))
       (equal
        (q1752621-mul (q1752621-mul x y) z)
        (q1752621-mul x (q1752621-mul y z)))
       (equal
        (q1752621-mul x (q1752621-add y z))
        (q1752621-add
         (q1752621-mul x y)
         (q1752621-mul x z))))))))

(defun q1752621-field-p ()
  (and
   (q1752621-scalar-p (q1752621-zero))
   (q1752621-scalar-p (q1752621-one))
   (not (equal (q1752621-zero) (q1752621-one)))
   (q1752621-field-laws-p)))

(defun-sk q1752621-order-laws-p ()
  (forall (x y z)
    (and
     (implies
      (q1752621-scalar-p x)
      (not (q1752621-lt x x)))
     (implies
      (and
       (q1752621-scalar-p x)
       (q1752621-scalar-p y))
      (and
       (or
        (q1752621-lt x y)
        (equal x y)
        (q1752621-lt y x))
       (not
        (and
         (q1752621-lt x y)
         (q1752621-lt y x)))))
     (implies
      (and
       (q1752621-scalar-p x)
       (q1752621-scalar-p y)
       (q1752621-scalar-p z)
       (q1752621-lt x y)
       (q1752621-lt y z))
      (q1752621-lt x z))
     (implies
      (and
       (q1752621-scalar-p x)
       (q1752621-scalar-p y)
       (q1752621-scalar-p z)
       (q1752621-lt x y))
      (q1752621-lt
       (q1752621-add x z)
       (q1752621-add y z)))
     (implies
      (and
       (q1752621-scalar-p x)
       (q1752621-scalar-p y)
       (q1752621-lt (q1752621-zero) x)
       (q1752621-lt (q1752621-zero) y))
      (q1752621-lt
       (q1752621-zero)
       (q1752621-mul x y))))))

(defun q1752621-ordered-field-p ()
  (and
   (q1752621-field-p)
   (q1752621-order-laws-p)
   (q1752621-lt (q1752621-zero) (q1752621-one))))

;; Real-closedness: nonnegative scalars are squares and every odd-degree
;; polynomial has a root. All witnesses remain existential in the statement.

(defun-sk q1752621-has-square-root-p (x)
  (exists (root)
    (and
     (q1752621-scalar-p root)
     (equal (q1752621-mul root root) x))))

(defun-sk q1752621-nonnegative-scalars-are-squares-p ()
  (forall (x)
    (implies
     (and
      (q1752621-scalar-p x)
      (not (q1752621-lt x (q1752621-zero))))
     (q1752621-has-square-root-p x))))

(defun q1752621-scalar-list-p (values)
  (if (consp values)
      (and
       (q1752621-scalar-p (car values))
       (q1752621-scalar-list-p (cdr values)))
    (equal values nil)))

(defun q1752621-positive-odd-degree-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (consp (cdr coefficients))
   (q1752621-scalar-list-p coefficients)
   (not
    (equal
     (car (last coefficients))
     (q1752621-zero)))
   (evenp (len coefficients))))

;; Coefficients are in ascending degree order.

(defun q1752621-polynomial-eval (coefficients x)
  (if (consp coefficients)
      (q1752621-add
       (car coefficients)
       (q1752621-mul
        x
        (q1752621-polynomial-eval (cdr coefficients) x)))
    (q1752621-zero)))

(defun-sk q1752621-polynomial-has-root-p (coefficients)
  (exists (root)
    (and
     (q1752621-scalar-p root)
     (equal
      (q1752621-polynomial-eval coefficients root)
      (q1752621-zero)))))

(defun-sk q1752621-odd-degree-polynomials-have-roots-p ()
  (forall (coefficients)
    (implies
     (q1752621-positive-odd-degree-polynomial-p coefficients)
     (q1752621-polynomial-has-root-p coefficients))))

(defun q1752621-real-closed-field-p ()
  (and
   (q1752621-ordered-field-p)
   (q1752621-nonnegative-scalars-are-squares-p)
   (q1752621-odd-degree-polynomials-have-roots-p)))

;; Finite vectors and matrices over the scalar carrier.

(defun q1752621-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (q1752621-range-from (+ 1 start) (- count 1)))))

(defun q1752621-rows-valid-p (dimension rows)
  (if (consp rows)
      (and
       (true-listp (car rows))
       (equal (len (car rows)) dimension)
       (q1752621-scalar-list-p (car rows))
       (q1752621-rows-valid-p dimension (cdr rows)))
    (equal rows nil)))

(defun q1752621-matrix-valid-p (dimension matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) dimension)
   (q1752621-rows-valid-p dimension matrix)))

(defun q1752621-matrix-entry (matrix row column)
  (nth column (nth row matrix)))

(defun q1752621-symmetric-row-p (matrix row columns)
  (if (consp columns)
      (and
       (equal
        (q1752621-matrix-entry matrix row (car columns))
        (q1752621-matrix-entry matrix (car columns) row))
       (q1752621-symmetric-row-p matrix row (cdr columns)))
    (equal columns nil)))

(defun q1752621-symmetric-matrix-p (matrix rows columns)
  (if (consp rows)
      (and
       (q1752621-symmetric-row-p matrix (car rows) columns)
       (q1752621-symmetric-matrix-p matrix (cdr rows) columns))
    (equal rows nil)))

(defun q1752621-weight-list-p (weights)
  (if (consp weights)
      (and
       (q1752621-scalar-p (car weights))
       (or
        (equal (car weights)
               (q1752621-neg (q1752621-one)))
        (equal (car weights) (q1752621-zero))
        (equal (car weights) (q1752621-one)))
       (q1752621-weight-list-p (cdr weights)))
    (equal weights nil)))

;; Matrix products and invertibility.

(defun q1752621-product-entry
    (left right row column indices)
  (if (consp indices)
      (q1752621-add
       (q1752621-mul
        (q1752621-matrix-entry left row (car indices))
        (q1752621-matrix-entry right (car indices) column))
       (q1752621-product-entry
        left right row column (cdr indices)))
    (q1752621-zero)))

(defun q1752621-inverse-row-p
    (left right row columns indices)
  (if (consp columns)
      (and
       (equal
        (q1752621-product-entry
         left right row (car columns) indices)
        (if (equal row (car columns))
            (q1752621-one)
          (q1752621-zero)))
       (q1752621-inverse-row-p
        left right row (cdr columns) indices))
    (equal columns nil)))

(defun q1752621-inverse-product-p
    (left right rows columns indices)
  (if (consp rows)
      (and
       (q1752621-inverse-row-p
        left right (car rows) columns indices)
       (q1752621-inverse-product-p
        left right (cdr rows) columns indices))
    (equal rows nil)))

;; The (row,column) entry of transpose(T) diag(weights) T.

(defun q1752621-congruence-entry
    (weights transform row column indices)
  (if (consp indices)
      (q1752621-add
       (q1752621-mul
        (nth (car indices) weights)
        (q1752621-mul
         (q1752621-matrix-entry
          transform (car indices) row)
         (q1752621-matrix-entry
          transform (car indices) column)))
       (q1752621-congruence-entry
        weights transform row column (cdr indices)))
    (q1752621-zero)))

(defun q1752621-congruence-row-p
    (matrix weights transform row columns indices)
  (if (consp columns)
      (and
       (equal
        (q1752621-matrix-entry matrix row (car columns))
        (q1752621-congruence-entry
         weights transform row (car columns) indices))
       (q1752621-congruence-row-p
        matrix weights transform row (cdr columns) indices))
    (equal columns nil)))

(defun q1752621-congruent-to-weighted-squares-p
    (matrix weights transform rows columns indices)
  (if (consp rows)
      (and
       (q1752621-congruence-row-p
        matrix weights transform (car rows) columns indices)
       (q1752621-congruent-to-weighted-squares-p
        matrix weights transform (cdr rows) columns indices))
    (equal rows nil)))

(defun q1752621-sylvester-witness-p
    (dimension matrix weights transform inverse)
  (let ((indices (q1752621-range-from 0 dimension)))
    (and
     (true-listp weights)
     (equal (len weights) dimension)
     (q1752621-weight-list-p weights)
     (q1752621-matrix-valid-p dimension transform)
     (q1752621-matrix-valid-p dimension inverse)
     (q1752621-inverse-product-p
      transform inverse indices indices indices)
     (q1752621-inverse-product-p
      inverse transform indices indices indices)
     (q1752621-congruent-to-weighted-squares-p
      matrix weights transform indices indices indices))))

(defun-sk q1752621-sylvester-witness-exists-p
    (dimension matrix)
  (exists (weights transform inverse)
    (q1752621-sylvester-witness-p
     dimension matrix weights transform inverse)))

(defun-sk
    thousand-theorems-q1752621-sylvester-s-law-of-inertia-statement
    ()
  (forall (dimension matrix)
    (let ((indices (q1752621-range-from 0 dimension)))
      (implies
       (and
        (q1752621-real-closed-field-p)
        (natp dimension)
        (q1752621-matrix-valid-p dimension matrix)
        (q1752621-symmetric-matrix-p matrix indices indices))
       (q1752621-sylvester-witness-exists-p
        dimension matrix)))))

(value-triple :itpeval-statement-checked)
:q
