;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_b3:
;; over a finite field of odd cardinality n, exactly (n-1)/2 constant shifts
;; of a monic irreducible quadratic remain irreducible. This file contains no
;; proof.

(in-package "ACL2")

;; A duplicate-free carrier and complete operation tables represent an
;; arbitrary finite field extensionally. Since the source field is finite,
;; every field structure has such tables, and the axioms below recover the
;; corresponding operations without restricting the field's isomorphism type.

(defun putnam-1979-b3-set-list-p (xs)
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (putnam-1979-b3-set-list-p (cdr xs)))
    (equal xs nil)))

(defun putnam-1979-b3-unary-table-p (table carrier)
  (if (consp table)
      (let* ((entry (car table))
             (argument (car entry))
             (value (cdr entry)))
        (and
         (consp entry)
         (member-equal argument carrier)
         (member-equal value carrier)
         (not (assoc-equal argument (cdr table)))
         (putnam-1979-b3-unary-table-p
          (cdr table) carrier)))
    (equal table nil)))

(defun putnam-1979-b3-binary-table-p (table carrier)
  (if (consp table)
      (let* ((entry (car table))
             (arguments (car entry))
             (value (cdr entry)))
        (and
         (consp entry)
         (true-listp arguments)
         (equal (len arguments) 2)
         (member-equal (car arguments) carrier)
         (member-equal (cadr arguments) carrier)
         (member-equal value carrier)
         (not (assoc-equal arguments (cdr table)))
         (putnam-1979-b3-binary-table-p
          (cdr table) carrier)))
    (equal table nil)))

(defun putnam-1979-b3-unary-value (argument table)
  (cdr (assoc-equal argument table)))

(defun putnam-1979-b3-binary-value (left right table)
  (cdr (assoc-equal (list left right) table)))

(defun putnam-1979-b3-field-xyz-axioms-p
    (zs x y add-table mul-table)
  (if (endp zs)
      t
    (let* ((z (car zs))
           (x-plus-y
            (putnam-1979-b3-binary-value
             x y add-table))
           (y-plus-z
            (putnam-1979-b3-binary-value
             y z add-table))
           (x-times-y
            (putnam-1979-b3-binary-value
             x y mul-table))
           (y-times-z
            (putnam-1979-b3-binary-value
             y z mul-table)))
      (and
       (equal
        (putnam-1979-b3-binary-value
         x-plus-y z add-table)
        (putnam-1979-b3-binary-value
         x y-plus-z add-table))
       (equal
        (putnam-1979-b3-binary-value
         x-times-y z mul-table)
        (putnam-1979-b3-binary-value
         x y-times-z mul-table))
       (equal
        (putnam-1979-b3-binary-value
         x y-plus-z mul-table)
        (putnam-1979-b3-binary-value
         (putnam-1979-b3-binary-value
          x y mul-table)
         (putnam-1979-b3-binary-value
          x z mul-table)
         add-table))
       (putnam-1979-b3-field-xyz-axioms-p
        (cdr zs) x y add-table mul-table)))))

(defun putnam-1979-b3-field-xy-axioms-p
    (ys carrier x add-table mul-table)
  (if (endp ys)
      t
    (let ((y (car ys)))
      (and
       (assoc-equal (list x y) add-table)
       (assoc-equal (list x y) mul-table)
       (equal
        (putnam-1979-b3-binary-value
         x y add-table)
        (putnam-1979-b3-binary-value
         y x add-table))
       (equal
        (putnam-1979-b3-binary-value
         x y mul-table)
        (putnam-1979-b3-binary-value
         y x mul-table))
       (putnam-1979-b3-field-xyz-axioms-p
        carrier x y add-table mul-table)
       (putnam-1979-b3-field-xy-axioms-p
        (cdr ys) carrier x add-table mul-table)))))

(defun putnam-1979-b3-field-x-axioms-p
    (xs carrier zero one add-table mul-table neg-table inv-table)
  (if (endp xs)
      t
    (let* ((x (car xs))
           (negative
            (putnam-1979-b3-unary-value x neg-table))
           (inverse
            (putnam-1979-b3-unary-value x inv-table)))
      (and
       (assoc-equal x neg-table)
       (assoc-equal x inv-table)
       (equal
        (putnam-1979-b3-binary-value
         x zero add-table)
        x)
       (equal
        (putnam-1979-b3-binary-value
         x negative add-table)
        zero)
       (equal
        (putnam-1979-b3-binary-value
         x one mul-table)
        x)
       (implies
        (not (equal x zero))
        (equal
         (putnam-1979-b3-binary-value
          x inverse mul-table)
         one))
       (putnam-1979-b3-field-xy-axioms-p
        carrier carrier x add-table mul-table)
       (putnam-1979-b3-field-x-axioms-p
        (cdr xs) carrier zero one add-table mul-table
        neg-table inv-table)))))

(defun putnam-1979-b3-finite-field-p
    (carrier zero one add-table mul-table neg-table inv-table)
  (and
   (putnam-1979-b3-set-list-p carrier)
   (consp carrier)
   (member-equal zero carrier)
   (member-equal one carrier)
   (not (equal zero one))
   (putnam-1979-b3-binary-table-p add-table carrier)
   (putnam-1979-b3-binary-table-p mul-table carrier)
   (putnam-1979-b3-unary-table-p neg-table carrier)
   (putnam-1979-b3-unary-table-p inv-table carrier)
   (putnam-1979-b3-field-x-axioms-p
    carrier carrier zero one add-table mul-table
    neg-table inv-table)))

(defun putnam-1979-b3-quadratic-value
    (x b constant add-table mul-table)
  (putnam-1979-b3-binary-value
   (putnam-1979-b3-binary-value
    (putnam-1979-b3-binary-value
     x x mul-table)
    (putnam-1979-b3-binary-value
     b x mul-table)
    add-table)
   constant
   add-table))

(defun putnam-1979-b3-quadratic-has-root-p
    (xs zero b constant add-table mul-table)
  (if (endp xs)
      nil
    (or
     (equal
      (putnam-1979-b3-quadratic-value
       (car xs) b constant add-table mul-table)
      zero)
     (putnam-1979-b3-quadratic-has-root-p
      (cdr xs) zero b constant add-table mul-table))))

;; A monic degree-two polynomial over a field is irreducible exactly when it
;; has no root in that field. This eliminates the source's definitionally
;; fixed polynomial parameter while preserving its irreducibility hypothesis.
(defun putnam-1979-b3-quadratic-irreducible-p
    (carrier zero b constant add-table mul-table)
  (not
   (putnam-1979-b3-quadratic-has-root-p
    carrier zero b constant add-table mul-table)))

(defun putnam-1979-b3-irreducible-shift-count
    (shifts carrier zero b c add-table mul-table)
  (if (endp shifts)
      0
    (let ((shifted-constant
           (putnam-1979-b3-binary-value
            c (car shifts) add-table)))
      (+
       (if
        (putnam-1979-b3-quadratic-irreducible-p
         carrier zero b shifted-constant add-table mul-table)
        1
        0)
       (putnam-1979-b3-irreducible-shift-count
        (cdr shifts) carrier zero b c add-table mul-table)))))

(defun putnam-1979-b3-solution (n)
  (floor (nfix (- n 1)) 2))

(defun putnambench-putnam-1979-b3-statement
    (carrier zero one add-table mul-table neg-table inv-table n b c)
  (implies
   (and
    (putnam-1979-b3-finite-field-p
     carrier zero one add-table mul-table neg-table inv-table)
    (natp n)
    (equal n (len carrier))
    (oddp n)
    (member-equal b carrier)
    (member-equal c carrier)
    (putnam-1979-b3-quadratic-irreducible-p
     carrier zero b c add-table mul-table))
   (equal
    (putnam-1979-b3-irreducible-shift-count
     carrier carrier zero b c add-table mul-table)
    (putnam-1979-b3-solution n))))

(value-triple :itpeval-statement-checked)
:q
