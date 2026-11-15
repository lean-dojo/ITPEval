;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_b5:
;; a complex 2n-by-n matrix whose left kernel has no nonzero real vector
;; has a surjective real-part map onto the real 2n-vectors.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar domain is an arbitrary real closed ordered field.  Real closed
;; fields have the same first-order theory as the reals, and for each positive
;; n the matrix assertion below is first-order.  Thus this presentation is
;; bidirectionally equivalent to the source statement over R and C.
;;
;; Complex values are exact pairs of field elements.  Matrices and vectors are
;; exact finite row-major lists of the source dimensions.  DEFUN-SK keeps the
;; universal kernel vector, every real target vector, and the existential
;; complex preimage internal to the statement.  In particular, entries range
;; over the whole represented field, not an algebraic or rational subfield.

(defun p87b5-r-carrier (ctx) (nth 0 ctx))
(defun p87b5-r-zero (ctx) (nth 1 ctx))
(defun p87b5-r-one (ctx) (nth 2 ctx))
(defun p87b5-r-add (ctx) (nth 3 ctx))
(defun p87b5-r-mul (ctx) (nth 4 ctx))
(defun p87b5-r-neg (ctx) (nth 5 ctx))
(defun p87b5-r-inv (ctx) (nth 6 ctx))
(defun p87b5-r-lt (ctx) (nth 7 ctx))

(defun p87b5-member-p (ctx x)
  (if (apply$ (p87b5-r-carrier ctx) (list x)) t nil))

(defun p87b5-unary-value (operation x)
  (apply$ operation (list x)))

(defun p87b5-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun p87b5-add (ctx x y)
  (p87b5-binary-value (p87b5-r-add ctx) x y))

(defun p87b5-mul (ctx x y)
  (p87b5-binary-value (p87b5-r-mul ctx) x y))

(defun p87b5-neg (ctx x)
  (p87b5-unary-value (p87b5-r-neg ctx) x))

(defun p87b5-inv (ctx x)
  (p87b5-unary-value (p87b5-r-inv ctx) x))

(defun p87b5-lt-p (ctx x y)
  (if (p87b5-binary-value (p87b5-r-lt ctx) x y) t nil))

(defun-sk p87b5-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p87b5-member-p ctx x)
      (p87b5-member-p ctx y)
      (p87b5-member-p ctx z))
     (and
      (p87b5-member-p ctx (p87b5-add ctx x y))
      (p87b5-member-p ctx (p87b5-mul ctx x y))
      (p87b5-member-p ctx (p87b5-neg ctx x))
      (p87b5-member-p ctx (p87b5-inv ctx x))
      (equal
       (p87b5-add ctx (p87b5-add ctx x y) z)
       (p87b5-add ctx x (p87b5-add ctx y z)))
      (equal (p87b5-add ctx x y) (p87b5-add ctx y x))
      (equal (p87b5-add ctx x (p87b5-r-zero ctx)) x)
      (equal
       (p87b5-add ctx x (p87b5-neg ctx x))
       (p87b5-r-zero ctx))
      (equal
       (p87b5-mul ctx (p87b5-mul ctx x y) z)
       (p87b5-mul ctx x (p87b5-mul ctx y z)))
      (equal (p87b5-mul ctx x y) (p87b5-mul ctx y x))
      (equal (p87b5-mul ctx x (p87b5-r-one ctx)) x)
      (implies
       (equal x (p87b5-r-zero ctx))
       (equal (p87b5-inv ctx x) (p87b5-r-zero ctx)))
      (implies
       (not (equal x (p87b5-r-zero ctx)))
       (equal
        (p87b5-mul ctx x (p87b5-inv ctx x))
        (p87b5-r-one ctx)))
      (equal
       (p87b5-mul ctx x (p87b5-add ctx y z))
       (p87b5-add
        ctx
        (p87b5-mul ctx x y)
        (p87b5-mul ctx x z)))))))

(defun-sk p87b5-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p87b5-member-p ctx x)
      (p87b5-member-p ctx y)
      (p87b5-member-p ctx z))
     (and
      (not (p87b5-lt-p ctx x x))
      (or
       (equal x y)
       (p87b5-lt-p ctx x y)
       (p87b5-lt-p ctx y x))
      (implies
       (and
        (p87b5-lt-p ctx x y)
        (p87b5-lt-p ctx y z))
       (p87b5-lt-p ctx x z))
      (implies
       (p87b5-lt-p ctx x y)
       (p87b5-lt-p
        ctx
        (p87b5-add ctx x z)
        (p87b5-add ctx y z)))
      (implies
       (and
        (p87b5-lt-p ctx (p87b5-r-zero ctx) x)
        (p87b5-lt-p ctx (p87b5-r-zero ctx) y))
       (p87b5-lt-p
        ctx
        (p87b5-r-zero ctx)
        (p87b5-mul ctx x y)))))))

(defun p87b5-carrier-list-p (values ctx)
  (if (endp values)
      (equal values nil)
    (and
     (p87b5-member-p ctx (car values))
     (p87b5-carrier-list-p (cdr values) ctx))))

(defun p87b5-polynomial-p (coefficients ctx)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p87b5-carrier-list-p coefficients ctx)
   (or
    (equal (len coefficients) 1)
    (not
     (equal
      (car (last coefficients))
      (p87b5-r-zero ctx))))))

(defun p87b5-polynomial-eval (ctx coefficients x)
  (if (endp coefficients)
      (p87b5-r-zero ctx)
    (p87b5-add
     ctx
     (car coefficients)
     (p87b5-mul
      ctx
      x
      (p87b5-polynomial-eval ctx (cdr coefficients) x)))))

(defun-sk p87b5-square-root-exists-p (ctx x)
  (exists (root)
    (and
     (p87b5-member-p ctx root)
     (equal (p87b5-mul ctx root root) x))))

(defun-sk p87b5-odd-root-exists-p (ctx coefficients)
  (exists (root)
    (and
     (p87b5-member-p ctx root)
     (equal
      (p87b5-polynomial-eval ctx coefficients root)
      (p87b5-r-zero ctx)))))

(defun-sk p87b5-real-closed-laws-p (ctx)
  (forall (x coefficients)
    (and
     (implies
      (and
       (p87b5-member-p ctx x)
       (not (p87b5-lt-p ctx x (p87b5-r-zero ctx))))
      (p87b5-square-root-exists-p ctx x))
     (implies
      (and
       (p87b5-polynomial-p coefficients ctx)
       (evenp (len coefficients)))
      (p87b5-odd-root-exists-p ctx coefficients)))))

(defun p87b5-real-closed-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (p87b5-r-carrier ctx))
   (tamep-functionp (p87b5-r-add ctx))
   (tamep-functionp (p87b5-r-mul ctx))
   (tamep-functionp (p87b5-r-neg ctx))
   (tamep-functionp (p87b5-r-inv ctx))
   (tamep-functionp (p87b5-r-lt ctx))
   (p87b5-member-p ctx (p87b5-r-zero ctx))
   (p87b5-member-p ctx (p87b5-r-one ctx))
   (not (equal (p87b5-r-zero ctx) (p87b5-r-one ctx)))
   (p87b5-field-laws-p ctx)
   (p87b5-order-laws-p ctx)
   (p87b5-lt-p ctx (p87b5-r-zero ctx) (p87b5-r-one ctx))
   (p87b5-real-closed-laws-p ctx)))

(defun p87b5-complex-p (value ctx)
  (and
   (true-listp value)
   (equal (len value) 2)
   (p87b5-member-p ctx (car value))
   (p87b5-member-p ctx (cadr value))))

(defun p87b5-complex-list-p (values ctx)
  (if (endp values)
      (equal values nil)
    (and
     (p87b5-complex-p (car values) ctx)
     (p87b5-complex-list-p (cdr values) ctx))))

(defun p87b5-complex-vector-p (vector length ctx)
  (and
   (natp length)
   (true-listp vector)
   (equal (len vector) length)
   (p87b5-complex-list-p vector ctx)))

(defun p87b5-real-vector-p (vector length ctx)
  (and
   (natp length)
   (true-listp vector)
   (equal (len vector) length)
   (p87b5-carrier-list-p vector ctx)))

(defun p87b5-complex-matrix-p (matrix rows columns ctx)
  (and
   (natp rows)
   (natp columns)
   (true-listp matrix)
   (equal (len matrix) (* rows columns))
   (p87b5-complex-list-p matrix ctx)))

(defun p87b5-complex-zero (ctx)
  (list (p87b5-r-zero ctx) (p87b5-r-zero ctx)))

(defun p87b5-complex-add (ctx left right)
  (list
   (p87b5-add ctx (car left) (car right))
   (p87b5-add ctx (cadr left) (cadr right))))

(defun p87b5-complex-mul (ctx left right)
  (list
   (p87b5-add
    ctx
    (p87b5-mul ctx (car left) (car right))
    (p87b5-neg
     ctx
     (p87b5-mul ctx (cadr left) (cadr right))))
   (p87b5-add
    ctx
    (p87b5-mul ctx (car left) (cadr right))
    (p87b5-mul ctx (cadr left) (car right)))))

(defun p87b5-left-product-entry
    (ctx vector matrix columns column row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p87b5-complex-zero ctx)
    (p87b5-complex-add
     ctx
     (p87b5-complex-mul
      ctx
      (nth row vector)
      (nth (+ (* row columns) column) matrix))
     (p87b5-left-product-entry
      ctx vector matrix columns column
      (+ row 1) (- remaining 1)))))

(defun p87b5-left-product-zero-p
    (ctx vector matrix rows columns column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (p87b5-left-product-entry
       ctx vector matrix columns column 0 rows)
      (p87b5-complex-zero ctx))
     (p87b5-left-product-zero-p
      ctx vector matrix rows columns
      (+ column 1) (- remaining 1)))))

(defun p87b5-complex-vector-zero-p (ctx vector)
  (if (endp vector)
      t
    (and
     (equal (car vector) (p87b5-complex-zero ctx))
     (p87b5-complex-vector-zero-p ctx (cdr vector)))))

(defun p87b5-has-nonreal-coordinate-p (ctx vector)
  (if (endp vector)
      nil
    (or
     (not (equal (cadar vector) (p87b5-r-zero ctx)))
     (p87b5-has-nonreal-coordinate-p ctx (cdr vector)))))

(defun-sk p87b5-kernel-condition-p (ctx n matrix)
  (forall (z)
    (implies
     (and
      (p87b5-complex-vector-p z (* 2 n) ctx)
      (p87b5-left-product-zero-p
       ctx z matrix (* 2 n) n 0 n)
      (not (p87b5-complex-vector-zero-p ctx z)))
     (p87b5-has-nonreal-coordinate-p ctx z))))

(defun p87b5-right-product-entry
    (ctx matrix vector columns row column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p87b5-complex-zero ctx)
    (p87b5-complex-add
     ctx
     (p87b5-complex-mul
      ctx
      (nth (+ (* row columns) column) matrix)
      (nth column vector))
     (p87b5-right-product-entry
      ctx matrix vector columns row
      (+ column 1) (- remaining 1)))))

(defun p87b5-real-part-equations-p
    (ctx matrix vector target columns row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (car
       (p87b5-right-product-entry
        ctx matrix vector columns row 0 columns))
      (nth row target))
     (p87b5-real-part-equations-p
      ctx matrix vector target columns
      (+ row 1) (- remaining 1)))))

(defun p87b5-preimage-p (ctx n matrix target vector)
  (and
   (p87b5-complex-vector-p vector n ctx)
   (p87b5-real-part-equations-p
    ctx matrix vector target n 0 (* 2 n))))

(defun-sk p87b5-target-has-preimage-p (ctx n matrix target)
  (exists (vector)
    (p87b5-preimage-p ctx n matrix target vector)))

(defun-sk p87b5-surjective-real-part-p (ctx n matrix)
  (forall (target)
    (implies
     (p87b5-real-vector-p target (* 2 n) ctx)
     (p87b5-target-has-preimage-p
      ctx n matrix target))))

(defun putnambench-putnam-1987-b5-statement (ctx n matrix)
  (implies
   (and
    (p87b5-real-closed-field-p ctx)
    (posp n)
    (p87b5-complex-matrix-p matrix (* 2 n) n ctx)
    (p87b5-kernel-condition-p ctx n matrix))
   (p87b5-surjective-real-part-p ctx n matrix)))

(value-triple :itpeval-statement-checked)
:q
