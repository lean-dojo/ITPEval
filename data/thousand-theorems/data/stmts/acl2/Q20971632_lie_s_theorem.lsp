;; Statement-only formalization of thousand-theorems corpus artifact Q20971632,
;; "Lie's theorem": a nonzero finite-dimensional triangularizable module over
;; a solvable Lie algebra in characteristic zero has a nonzero vector on which
;; every Lie element acts by some scalar. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Structure tags index arbitrary, unbounded carriers and operations.  The
;; field, vector-space, Lie-algebra, representation, finiteness, solvability,
;; and triangularizability laws are all explicit below.

(defstub q20971632-field-member-p (field value) t)
(defstub q20971632-field-zero (field) t)
(defstub q20971632-field-one (field) t)
(defstub q20971632-field-add (field left right) t)
(defstub q20971632-field-multiply (field left right) t)
(defstub q20971632-field-negate (field value) t)
(defstub q20971632-field-inverse (field value) t)

(defstub q20971632-vector-member-p (field space value) t)
(defstub q20971632-vector-zero (field space) t)
(defstub q20971632-vector-add (field space left right) t)
(defstub q20971632-vector-negate (field space value) t)
(defstub q20971632-vector-smul (field space scalar value) t)

(defstub q20971632-lie-bracket (field lie-algebra left right) t)
(defstub q20971632-lie-action
  (field lie-algebra module lie-element vector)
  t)

;; Fields of characteristic zero.

(defun-sk q20971632-field-laws-p (field)
  (forall (x y z)
    (and
     (implies
      (and
       (q20971632-field-member-p field x)
       (q20971632-field-member-p field y))
      (and
       (q20971632-field-member-p
        field (q20971632-field-add field x y))
       (q20971632-field-member-p
        field (q20971632-field-multiply field x y))
       (equal
        (q20971632-field-add field x y)
        (q20971632-field-add field y x))
       (equal
        (q20971632-field-multiply field x y)
        (q20971632-field-multiply field y x))))
     (implies
      (q20971632-field-member-p field x)
      (and
       (q20971632-field-member-p
        field (q20971632-field-negate field x))
       (q20971632-field-member-p
        field (q20971632-field-inverse field x))
       (equal
        (q20971632-field-add
         field x (q20971632-field-zero field))
        x)
       (equal
        (q20971632-field-add
         field x (q20971632-field-negate field x))
        (q20971632-field-zero field))
       (equal
        (q20971632-field-multiply
         field x (q20971632-field-one field))
        x)
       (equal
        (q20971632-field-multiply
         field x (q20971632-field-zero field))
        (q20971632-field-zero field))
       (implies
        (not (equal x (q20971632-field-zero field)))
        (equal
         (q20971632-field-multiply
          field x (q20971632-field-inverse field x))
         (q20971632-field-one field)))))
     (implies
      (and
       (q20971632-field-member-p field x)
       (q20971632-field-member-p field y)
       (q20971632-field-member-p field z))
      (and
       (equal
        (q20971632-field-add
         field (q20971632-field-add field x y) z)
        (q20971632-field-add
         field x (q20971632-field-add field y z)))
       (equal
        (q20971632-field-multiply
         field (q20971632-field-multiply field x y) z)
        (q20971632-field-multiply
         field x (q20971632-field-multiply field y z)))
       (equal
        (q20971632-field-multiply
         field x (q20971632-field-add field y z))
        (q20971632-field-add
         field
         (q20971632-field-multiply field x y)
         (q20971632-field-multiply field x z))))))))

(defun q20971632-field-p (field)
  (and
   (q20971632-field-member-p
    field (q20971632-field-zero field))
   (q20971632-field-member-p
    field (q20971632-field-one field))
   (not
    (equal
     (q20971632-field-zero field)
     (q20971632-field-one field)))
   (q20971632-field-laws-p field)))

(defun q20971632-natural-multiple-of-one (field n)
  (if (zp n)
      (q20971632-field-zero field)
    (q20971632-field-add
     field
     (q20971632-field-one field)
     (q20971632-natural-multiple-of-one field (- n 1)))))

(defun-sk q20971632-characteristic-zero-p (field)
  (forall (n)
    (implies
     (and (integerp n) (< 0 n))
     (not
      (equal
       (q20971632-natural-multiple-of-one field n)
       (q20971632-field-zero field))))))

;; Vector spaces over FIELD.  The same interface is used for the Lie algebra
;; carrier and for its module carrier.

(defun-sk q20971632-vector-space-laws-p (field space)
  (forall (a b u v w)
    (and
     (implies
      (and
       (q20971632-vector-member-p field space u)
       (q20971632-vector-member-p field space v))
      (and
       (q20971632-vector-member-p
        field space (q20971632-vector-add field space u v))
       (equal
        (q20971632-vector-add field space u v)
        (q20971632-vector-add field space v u))))
     (implies
      (q20971632-vector-member-p field space u)
      (and
       (q20971632-vector-member-p
        field space (q20971632-vector-negate field space u))
       (equal
        (q20971632-vector-add
         field space u (q20971632-vector-zero field space))
        u)
       (equal
        (q20971632-vector-add
         field space u
         (q20971632-vector-negate field space u))
        (q20971632-vector-zero field space))
       (equal
        (q20971632-vector-smul
         field space (q20971632-field-one field) u)
        u)
       (equal
        (q20971632-vector-smul
         field space (q20971632-field-zero field) u)
        (q20971632-vector-zero field space))))
     (implies
      (and
       (q20971632-vector-member-p field space u)
       (q20971632-vector-member-p field space v)
       (q20971632-vector-member-p field space w))
      (equal
       (q20971632-vector-add
        field space (q20971632-vector-add field space u v) w)
       (q20971632-vector-add
        field space u (q20971632-vector-add field space v w))))
     (implies
      (and
       (q20971632-field-member-p field a)
       (q20971632-vector-member-p field space u))
      (q20971632-vector-member-p
       field space (q20971632-vector-smul field space a u)))
     (implies
      (q20971632-field-member-p field a)
      (equal
       (q20971632-vector-smul
        field space a (q20971632-vector-zero field space))
       (q20971632-vector-zero field space)))
     (implies
      (and
       (q20971632-field-member-p field a)
       (q20971632-vector-member-p field space u)
       (q20971632-vector-member-p field space v))
      (equal
       (q20971632-vector-smul
        field space a (q20971632-vector-add field space u v))
       (q20971632-vector-add
        field space
        (q20971632-vector-smul field space a u)
        (q20971632-vector-smul field space a v))))
     (implies
      (and
       (q20971632-field-member-p field a)
       (q20971632-field-member-p field b)
       (q20971632-vector-member-p field space u))
      (and
       (equal
        (q20971632-vector-smul
         field space (q20971632-field-add field a b) u)
        (q20971632-vector-add
         field space
         (q20971632-vector-smul field space a u)
         (q20971632-vector-smul field space b u)))
       (equal
        (q20971632-vector-smul
         field space (q20971632-field-multiply field a b) u)
        (q20971632-vector-smul
         field space a
         (q20971632-vector-smul field space b u))))))))

(defun q20971632-vector-space-p (field space)
  (and
   (q20971632-field-p field)
   (q20971632-vector-member-p
    field space (q20971632-vector-zero field space))
   (q20971632-vector-space-laws-p field space)))

;; Lie algebra structure: a bilinear alternating bracket satisfying Jacobi.

(defun-sk q20971632-lie-algebra-laws-p (field lie-algebra)
  (forall (a x y z)
    (and
     (implies
      (and
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field lie-algebra y))
      (q20971632-vector-member-p
       field lie-algebra
       (q20971632-lie-bracket field lie-algebra x y)))
     (implies
      (q20971632-vector-member-p field lie-algebra x)
      (equal
       (q20971632-lie-bracket field lie-algebra x x)
       (q20971632-vector-zero field lie-algebra)))
     (implies
      (and
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field lie-algebra y)
       (q20971632-vector-member-p field lie-algebra z))
      (and
       (equal
        (q20971632-lie-bracket
         field lie-algebra
         (q20971632-vector-add field lie-algebra x y)
         z)
        (q20971632-vector-add
         field lie-algebra
         (q20971632-lie-bracket field lie-algebra x z)
         (q20971632-lie-bracket field lie-algebra y z)))
       (equal
        (q20971632-lie-bracket
         field lie-algebra
         x
         (q20971632-vector-add field lie-algebra y z))
        (q20971632-vector-add
         field lie-algebra
         (q20971632-lie-bracket field lie-algebra x y)
         (q20971632-lie-bracket field lie-algebra x z)))
       (equal
        (q20971632-lie-bracket
         field lie-algebra x
         (q20971632-lie-bracket field lie-algebra y z))
        (q20971632-vector-add
         field lie-algebra
         (q20971632-lie-bracket
          field lie-algebra
          (q20971632-lie-bracket field lie-algebra x y)
          z)
         (q20971632-lie-bracket
          field lie-algebra y
          (q20971632-lie-bracket field lie-algebra x z))))))
     (implies
      (and
       (q20971632-field-member-p field a)
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field lie-algebra y))
      (and
       (equal
        (q20971632-lie-bracket
         field lie-algebra
         (q20971632-vector-smul field lie-algebra a x)
         y)
        (q20971632-vector-smul
         field lie-algebra a
         (q20971632-lie-bracket field lie-algebra x y)))
       (equal
        (q20971632-lie-bracket
         field lie-algebra x
         (q20971632-vector-smul field lie-algebra a y))
        (q20971632-vector-smul
         field lie-algebra a
         (q20971632-lie-bracket field lie-algebra x y))))))))

(defun q20971632-lie-algebra-p (field lie-algebra)
  (and
   (q20971632-vector-space-p field lie-algebra)
   (q20971632-lie-algebra-laws-p field lie-algebra)))

;; Lie module structure.  ACTION([x,y],v) is the commutator of the two
;; action endomorphisms.

(defun-sk q20971632-lie-module-laws-p
    (field lie-algebra module)
  (forall (a x y u v)
    (and
     (implies
      (and
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field module u))
      (q20971632-vector-member-p
       field module
       (q20971632-lie-action
        field lie-algebra module x u)))
     (implies
      (and
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field lie-algebra y)
       (q20971632-vector-member-p field module u))
      (equal
       (q20971632-lie-action
        field lie-algebra module
        (q20971632-vector-add field lie-algebra x y)
        u)
       (q20971632-vector-add
        field module
        (q20971632-lie-action
         field lie-algebra module x u)
        (q20971632-lie-action
         field lie-algebra module y u))))
     (implies
      (and
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field module u)
       (q20971632-vector-member-p field module v))
      (equal
       (q20971632-lie-action
        field lie-algebra module x
        (q20971632-vector-add field module u v))
       (q20971632-vector-add
        field module
        (q20971632-lie-action
         field lie-algebra module x u)
        (q20971632-lie-action
         field lie-algebra module x v))))
     (implies
      (and
       (q20971632-field-member-p field a)
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field module u))
      (and
       (equal
        (q20971632-lie-action
         field lie-algebra module
         (q20971632-vector-smul field lie-algebra a x)
         u)
        (q20971632-vector-smul
         field module a
         (q20971632-lie-action
          field lie-algebra module x u)))
       (equal
        (q20971632-lie-action
         field lie-algebra module x
         (q20971632-vector-smul field module a u))
        (q20971632-vector-smul
         field module a
         (q20971632-lie-action
          field lie-algebra module x u)))))
     (implies
      (and
       (q20971632-vector-member-p field lie-algebra x)
       (q20971632-vector-member-p field lie-algebra y)
       (q20971632-vector-member-p field module u))
      (equal
       (q20971632-lie-action
        field lie-algebra module
        (q20971632-lie-bracket field lie-algebra x y)
        u)
       (q20971632-vector-add
        field module
        (q20971632-lie-action
         field lie-algebra module x
         (q20971632-lie-action
          field lie-algebra module y u))
        (q20971632-vector-negate
         field module
         (q20971632-lie-action
          field lie-algebra module y
          (q20971632-lie-action
           field lie-algebra module x u)))))))))

(defun q20971632-lie-module-p
    (field lie-algebra module)
  (and
   (q20971632-lie-algebra-p field lie-algebra)
   (q20971632-vector-space-p field module)
   (q20971632-lie-module-laws-p
    field lie-algebra module)))

;; Finite bases and finite linear combinations represent precisely the
;; source's finite-dimensional module hypothesis.

(defun q20971632-field-list-p (field values)
  (if (consp values)
      (and
       (q20971632-field-member-p field (car values))
       (q20971632-field-list-p field (cdr values)))
    (equal values nil)))

(defun q20971632-vector-list-p (field space values)
  (if (consp values)
      (and
       (q20971632-vector-member-p field space (car values))
       (q20971632-vector-list-p field space (cdr values)))
    (equal values nil)))

(defun q20971632-linear-combination
    (field space coefficients vectors)
  (if (and (consp coefficients) (consp vectors))
      (q20971632-vector-add
       field space
       (q20971632-vector-smul
        field space (car coefficients) (car vectors))
       (q20971632-linear-combination
        field space (cdr coefficients) (cdr vectors)))
    (q20971632-vector-zero field space)))

(defun q20971632-all-zero-coefficients-p (field coefficients)
  (if (consp coefficients)
      (and
       (equal
        (car coefficients)
        (q20971632-field-zero field))
       (q20971632-all-zero-coefficients-p
        field (cdr coefficients)))
    (equal coefficients nil)))

(defun-sk q20971632-basis-independent-p
    (field space basis)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (equal (len coefficients) (len basis))
      (q20971632-field-list-p field coefficients)
      (equal
       (q20971632-linear-combination
        field space coefficients basis)
       (q20971632-vector-zero field space)))
     (q20971632-all-zero-coefficients-p
      field coefficients))))

(defun-sk q20971632-coordinate-list-exists-p
    (field space basis value)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len basis))
     (q20971632-field-list-p field coefficients)
     (equal
      (q20971632-linear-combination
       field space coefficients basis)
      value))))

(defun-sk q20971632-basis-spans-p
    (field space basis)
  (forall (value)
    (implies
     (q20971632-vector-member-p field space value)
     (q20971632-coordinate-list-exists-p
      field space basis value))))

(defun q20971632-basis-p (field space basis)
  (and
   (true-listp basis)
   (q20971632-vector-list-p field space basis)
   (q20971632-basis-independent-p field space basis)
   (q20971632-basis-spans-p field space basis)))

(defun-sk q20971632-finite-dimensional-p (field space)
  (exists (basis)
    (q20971632-basis-p field space basis)))

(defun-sk q20971632-nontrivial-space-p (field space)
  (exists (value)
    (and
     (q20971632-vector-member-p field space value)
     (not
      (equal
       value
       (q20971632-vector-zero field space))))))

;; The derived series is represented extensionally.  A level-zero expression
;; denotes any Lie-algebra element.  At successor level, finite expression
;; trees generate exactly the linear span of brackets from the prior level.

(defun q20971632-derived-expression-p
    (field lie-algebra level expression)
  (cond
   ((zp level)
    (and
     (true-listp expression)
     (equal (len expression) 2)
     (equal (car expression) :q20971632-atom)
     (q20971632-vector-member-p
      field lie-algebra (cadr expression))))
   ((atom expression) nil)
   ((equal (car expression) :q20971632-zero)
    (and
     (true-listp expression)
     (equal (len expression) 1)))
   ((equal (car expression) :q20971632-add)
    (and
     (true-listp expression)
     (equal (len expression) 3)
     (q20971632-derived-expression-p
      field lie-algebra level (cadr expression))
     (q20971632-derived-expression-p
      field lie-algebra level (caddr expression))))
   ((equal (car expression) :q20971632-smul)
    (and
     (true-listp expression)
     (equal (len expression) 3)
     (q20971632-field-member-p field (cadr expression))
     (q20971632-derived-expression-p
      field lie-algebra level (caddr expression))))
   ((equal (car expression) :q20971632-bracket)
    (and
     (true-listp expression)
     (equal (len expression) 3)
     (q20971632-derived-expression-p
      field lie-algebra (- level 1) (cadr expression))
     (q20971632-derived-expression-p
      field lie-algebra (- level 1) (caddr expression))))
   (t nil)))

(defun q20971632-derived-expression-value
    (field lie-algebra level expression)
  (cond
   ((zp level)
    (if (consp expression)
        (cadr expression)
      (q20971632-vector-zero field lie-algebra)))
   ((atom expression)
    (q20971632-vector-zero field lie-algebra))
   ((equal (car expression) :q20971632-zero)
    (q20971632-vector-zero field lie-algebra))
   ((equal (car expression) :q20971632-add)
    (q20971632-vector-add
     field lie-algebra
     (q20971632-derived-expression-value
      field lie-algebra level (cadr expression))
     (q20971632-derived-expression-value
      field lie-algebra level (caddr expression))))
   ((equal (car expression) :q20971632-smul)
    (q20971632-vector-smul
     field lie-algebra
     (cadr expression)
     (q20971632-derived-expression-value
      field lie-algebra level (caddr expression))))
   ((equal (car expression) :q20971632-bracket)
    (q20971632-lie-bracket
     field lie-algebra
     (q20971632-derived-expression-value
      field lie-algebra (- level 1) (cadr expression))
     (q20971632-derived-expression-value
      field lie-algebra (- level 1) (caddr expression))))
   (t
    (q20971632-vector-zero field lie-algebra))))

(defun-sk q20971632-derived-member-p
    (field lie-algebra level value)
  (exists (expression)
    (and
     (q20971632-derived-expression-p
      field lie-algebra level expression)
     (equal
      (q20971632-derived-expression-value
       field lie-algebra level expression)
      value))))

(defun-sk q20971632-derived-level-zero-p
    (field lie-algebra level)
  (forall (value)
    (implies
     (q20971632-derived-member-p
      field lie-algebra level value)
     (equal
      value
      (q20971632-vector-zero field lie-algebra)))))

(defun-sk q20971632-solvable-p (field lie-algebra)
  (exists (level)
    (and
     (natp level)
     (q20971632-derived-level-zero-p
      field lie-algebra level))))

;; A finite-dimensional endomorphism is triangularizable exactly when it has
;; an ordered basis for which every basis vector is sent into its prefix span.

(defun q20971632-list-prefix (count values)
  (if (or (zp count) (atom values))
      nil
    (cons
     (car values)
     (q20971632-list-prefix (- count 1) (cdr values)))))

(defun-sk q20971632-prefix-span-member-p
    (field space basis count value)
  (exists (coefficients)
    (let ((prefix
           (q20971632-list-prefix count basis)))
      (and
       (true-listp coefficients)
       (equal (len coefficients) (len prefix))
       (q20971632-field-list-p field coefficients)
       (equal
        (q20971632-linear-combination
         field space coefficients prefix)
        value)))))

(defun-sk q20971632-upper-triangular-action-p
    (field lie-algebra module lie-element basis)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index (len basis)))
     (q20971632-prefix-span-member-p
      field module basis (+ 1 index)
      (q20971632-lie-action
       field lie-algebra module
       lie-element (nth index basis))))))

(defun-sk q20971632-action-triangularizable-p
    (field lie-algebra module lie-element)
  (exists (basis)
    (and
     (q20971632-basis-p field module basis)
     (q20971632-upper-triangular-action-p
      field lie-algebra module lie-element basis))))

(defun-sk q20971632-triangularizable-module-p
    (field lie-algebra module)
  (forall (lie-element)
    (implies
     (q20971632-vector-member-p
      field lie-algebra lie-element)
     (q20971632-action-triangularizable-p
      field lie-algebra module lie-element))))

;; For a fixed nonzero vector, each Lie element has an internal scalar
;; eigenvalue witness.  Nonzeroness makes that scalar unique, and the linear
;; action laws make the resulting assignment a linear functional.

(defun-sk q20971632-eigenvalue-exists-p
    (field lie-algebra module vector lie-element)
  (exists (scalar)
    (and
     (q20971632-field-member-p field scalar)
     (equal
      (q20971632-lie-action
       field lie-algebra module lie-element vector)
      (q20971632-vector-smul
       field module scalar vector)))))

(defun-sk q20971632-common-eigenvector-p
    (field lie-algebra module vector)
  (forall (lie-element)
    (implies
     (q20971632-vector-member-p
      field lie-algebra lie-element)
     (q20971632-eigenvalue-exists-p
      field lie-algebra module vector lie-element))))

(defun-sk q20971632-nontrivial-weight-space-exists-p
    (field lie-algebra module)
  (exists (vector)
    (and
     (q20971632-vector-member-p field module vector)
     (not
      (equal
       vector
       (q20971632-vector-zero field module)))
     (q20971632-common-eigenvector-p
      field lie-algebra module vector))))

(defun-sk thousand-theorems-q20971632-lie-s-theorem-statement ()
  (forall (field lie-algebra module)
    (implies
     (and
      (q20971632-field-p field)
      (q20971632-characteristic-zero-p field)
      (q20971632-lie-module-p
       field lie-algebra module)
      (q20971632-finite-dimensional-p field module)
      (q20971632-nontrivial-space-p field module)
      (q20971632-solvable-p field lie-algebra)
      (q20971632-triangularizable-module-p
       field lie-algebra module))
     (q20971632-nontrivial-weight-space-exists-p
      field lie-algebra module))))

(value-triple :itpeval-statement-checked)
:q
