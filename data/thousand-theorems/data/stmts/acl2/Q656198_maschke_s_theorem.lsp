;; Statement-only formalization of thousand-theorems corpus artifact Q656198,
;; "Maschke's theorem": over a field in which the order of a finite group is
;; nonzero, every submodule of a module over the group algebra has a
;; complementary submodule. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative tag-indexed interfaces represent arbitrary fields, groups,
;; modules, and submodules. The tags do not supply laws: every required
;; algebraic, typing, closure, and finiteness condition is explicit below.

(defstub q656198-field-element-p (field value) t)
(defstub q656198-field-zero (field) t)
(defstub q656198-field-one (field) t)
(defstub q656198-field-add (field left right) t)
(defstub q656198-field-multiply (field left right) t)
(defstub q656198-field-negate (field value) t)
(defstub q656198-field-inverse (field value) t)

(defstub q656198-group-element-p (group value) t)
(defstub q656198-group-identity (group) t)
(defstub q656198-group-multiply (group left right) t)
(defstub q656198-group-inverse (group value) t)

(defstub q656198-module-element-p (field group module value) t)
(defstub q656198-module-zero (field group module) t)
(defstub q656198-module-add (field group module left right) t)
(defstub q656198-module-negate (field group module value) t)
(defstub q656198-module-smul
  (field group module group-algebra-element value)
  t)

(defstub q656198-submodule-member-p
  (field group module submodule value)
  t)

;; Field structure.

(defun-sk q656198-field-laws-p (field)
  (forall
   (x y z)
   (implies
    (and (q656198-field-element-p field x)
         (q656198-field-element-p field y)
         (q656198-field-element-p field z))
    (and
     (q656198-field-element-p
      field
      (q656198-field-add field x y))
     (q656198-field-element-p
      field
      (q656198-field-multiply field x y))
     (q656198-field-element-p
      field
      (q656198-field-negate field x))
     (q656198-field-element-p
      field
      (q656198-field-inverse field x))
     (equal (q656198-field-add
             field
             (q656198-field-add field x y)
             z)
            (q656198-field-add
             field
             x
             (q656198-field-add field y z)))
     (equal (q656198-field-add field x y)
            (q656198-field-add field y x))
     (equal (q656198-field-add
             field
             (q656198-field-zero field)
             x)
            x)
     (equal (q656198-field-add
             field
             x
             (q656198-field-zero field))
            x)
     (equal (q656198-field-add
             field
             (q656198-field-negate field x)
             x)
            (q656198-field-zero field))
     (equal (q656198-field-add
             field
             x
             (q656198-field-negate field x))
            (q656198-field-zero field))
     (equal (q656198-field-multiply
             field
             (q656198-field-multiply field x y)
             z)
            (q656198-field-multiply
             field
             x
             (q656198-field-multiply field y z)))
     (equal (q656198-field-multiply field x y)
            (q656198-field-multiply field y x))
     (equal (q656198-field-multiply
             field
             (q656198-field-one field)
             x)
            x)
     (equal (q656198-field-multiply
             field
             x
             (q656198-field-one field))
            x)
     (equal (q656198-field-multiply
             field
             (q656198-field-zero field)
             x)
            (q656198-field-zero field))
     (equal (q656198-field-multiply
             field
             x
             (q656198-field-zero field))
            (q656198-field-zero field))
     (equal (q656198-field-inverse
             field
             (q656198-field-zero field))
            (q656198-field-zero field))
     (implies
      (not (equal x (q656198-field-zero field)))
      (and
       (equal (q656198-field-multiply
               field
               (q656198-field-inverse field x)
               x)
              (q656198-field-one field))
       (equal (q656198-field-multiply
               field
               x
               (q656198-field-inverse field x))
              (q656198-field-one field))))
     (equal
      (q656198-field-multiply
       field
       x
       (q656198-field-add field y z))
      (q656198-field-add
       field
       (q656198-field-multiply field x y)
       (q656198-field-multiply field x z)))
     (equal
      (q656198-field-multiply
       field
       (q656198-field-add field x y)
       z)
      (q656198-field-add
       field
       (q656198-field-multiply field x z)
       (q656198-field-multiply field y z)))))))

(defun q656198-field-p (field)
  (and
   (q656198-field-element-p field (q656198-field-zero field))
   (q656198-field-element-p field (q656198-field-one field))
   (not (equal (q656198-field-zero field)
               (q656198-field-one field)))
   (q656198-field-laws-p field)))

;; Finite group structure. GROUP-ELEMENTS is an exact duplicate-free
;; enumeration of the otherwise arbitrary tag-indexed group carrier.

(defun-sk q656198-group-carrier-exact-p (group group-elements)
  (forall
   (x)
   (iff
    (q656198-group-element-p group x)
    (if (member-equal x group-elements) t nil))))

(defun-sk q656198-group-laws-p (group)
  (forall
   (x y z)
   (implies
    (and (q656198-group-element-p group x)
         (q656198-group-element-p group y)
         (q656198-group-element-p group z))
    (and
     (q656198-group-element-p
      group
      (q656198-group-multiply group x y))
     (q656198-group-element-p
      group
      (q656198-group-inverse group x))
     (equal
      (q656198-group-multiply
       group
       (q656198-group-multiply group x y)
       z)
      (q656198-group-multiply
       group
       x
       (q656198-group-multiply group y z)))
     (equal
      (q656198-group-multiply
       group
       (q656198-group-identity group)
       x)
      x)
     (equal
      (q656198-group-multiply
       group
       x
       (q656198-group-identity group))
      x)
     (equal
      (q656198-group-multiply
       group
       (q656198-group-inverse group x)
       x)
      (q656198-group-identity group))
     (equal
      (q656198-group-multiply
       group
       x
       (q656198-group-inverse group x))
      (q656198-group-identity group))))))

(defun q656198-finite-group-p (group group-elements)
  (and
   (true-listp group-elements)
   (no-duplicatesp-equal group-elements)
   (q656198-group-carrier-exact-p group group-elements)
   (q656198-group-element-p
    group
    (q656198-group-identity group))
   (q656198-group-laws-p group)))

;; The characteristic condition is the nonvanishing of the field-valued
;; natural-number cast of the finite group's cardinality.

(defun q656198-field-nat-cast (field n)
  (if (zp n)
      (q656198-field-zero field)
    (q656198-field-add
     field
     (q656198-field-one field)
     (q656198-field-nat-cast field (1- n)))))

(defun q656198-cardinality-nonzero-p (field group-elements)
  (not
   (equal
    (q656198-field-nat-cast field (len group-elements))
    (q656198-field-zero field))))

;; Since the group is finite, a group-algebra element is represented exactly
;; by its coefficient list in GROUP-ELEMENTS order.

(defun q656198-all-field-elements-p (field values)
  (if (endp values)
      t
    (and
     (q656198-field-element-p field (car values))
     (q656198-all-field-elements-p field (cdr values)))))

(defun q656198-group-algebra-element-p
    (field group-elements coefficients)
  (and
   (true-listp coefficients)
   (equal (len coefficients) (len group-elements))
   (q656198-all-field-elements-p field coefficients)))

(defun q656198-coefficient
    (field group-element group-elements coefficients)
  (if (or (endp group-elements)
          (endp coefficients))
      (q656198-field-zero field)
    (if (equal group-element (car group-elements))
        (car coefficients)
      (q656198-coefficient
       field
       group-element
       (cdr group-elements)
       (cdr coefficients)))))

(defun q656198-group-algebra-zero (field group-elements)
  (if (endp group-elements)
      nil
    (cons
     (q656198-field-zero field)
     (q656198-group-algebra-zero field (cdr group-elements)))))

(defun q656198-group-algebra-one (field group group-elements)
  (if (endp group-elements)
      nil
    (cons
     (if (equal (car group-elements)
                (q656198-group-identity group))
         (q656198-field-one field)
       (q656198-field-zero field))
     (q656198-group-algebra-one
      field
      group
      (cdr group-elements)))))

(defun q656198-group-algebra-add (field left right)
  (if (or (endp left) (endp right))
      nil
    (cons
     (q656198-field-add field (car left) (car right))
     (q656198-group-algebra-add
      field
      (cdr left)
      (cdr right)))))

(defun q656198-group-algebra-negate (field coefficients)
  (if (endp coefficients)
      nil
    (cons
     (q656198-field-negate field (car coefficients))
     (q656198-group-algebra-negate
      field
      (cdr coefficients)))))

(defun q656198-convolution-coefficient
    (field group target summands group-elements left right)
  (if (endp summands)
      (q656198-field-zero field)
    (q656198-field-add
     field
     (q656198-field-multiply
      field
      (q656198-coefficient
       field
       (car summands)
       group-elements
       left)
      (q656198-coefficient
       field
       (q656198-group-multiply
        group
        (q656198-group-inverse group (car summands))
        target)
       group-elements
       right))
     (q656198-convolution-coefficient
      field
      group
      target
      (cdr summands)
      group-elements
      left
      right))))

(defun q656198-group-algebra-multiply-aux
    (field group targets group-elements left right)
  (if (endp targets)
      nil
    (cons
     (q656198-convolution-coefficient
      field
      group
      (car targets)
      group-elements
      group-elements
      left
      right)
     (q656198-group-algebra-multiply-aux
      field
      group
      (cdr targets)
      group-elements
      left
      right))))

(defun q656198-group-algebra-multiply
    (field group group-elements left right)
  (q656198-group-algebra-multiply-aux
   field
   group
   group-elements
   group-elements
   left
   right))

;; An arbitrary additive commutative group equipped with a left action of the
;; represented group algebra. All module axioms are explicit.

(defun-sk q656198-module-laws-p
    (field group group-elements module)
  (forall
   (a b u v w)
   (implies
    (and
     (q656198-group-algebra-element-p
      field group-elements a)
     (q656198-group-algebra-element-p
      field group-elements b)
     (q656198-module-element-p field group module u)
     (q656198-module-element-p field group module v)
     (q656198-module-element-p field group module w))
    (and
     (q656198-module-element-p
      field
      group
      module
      (q656198-module-add field group module u v))
     (q656198-module-element-p
      field
      group
      module
      (q656198-module-negate field group module u))
     (q656198-module-element-p
      field
      group
      module
      (q656198-module-smul field group module a u))
     (equal
      (q656198-module-add
       field
       group
       module
       (q656198-module-add field group module u v)
       w)
      (q656198-module-add
       field
       group
       module
       u
       (q656198-module-add field group module v w)))
     (equal
      (q656198-module-add field group module u v)
      (q656198-module-add field group module v u))
     (equal
      (q656198-module-add
       field
       group
       module
       (q656198-module-zero field group module)
       u)
      u)
     (equal
      (q656198-module-add
       field
       group
       module
       u
       (q656198-module-zero field group module))
      u)
     (equal
      (q656198-module-add
       field
       group
       module
       (q656198-module-negate field group module u)
       u)
      (q656198-module-zero field group module))
     (equal
      (q656198-module-add
       field
       group
       module
       u
       (q656198-module-negate field group module u))
      (q656198-module-zero field group module))
     (equal
      (q656198-module-smul
       field
       group
       module
       (q656198-group-algebra-one field group group-elements)
       u)
      u)
     (equal
      (q656198-module-smul
       field
       group
       module
       (q656198-group-algebra-zero field group-elements)
       u)
      (q656198-module-zero field group module))
     (equal
      (q656198-module-smul
       field
       group
       module
       a
       (q656198-module-zero field group module))
      (q656198-module-zero field group module))
     (equal
      (q656198-module-smul
       field
       group
       module
       a
       (q656198-module-add field group module u v))
      (q656198-module-add
       field
       group
       module
       (q656198-module-smul field group module a u)
       (q656198-module-smul field group module a v)))
     (equal
      (q656198-module-smul
       field
       group
       module
       (q656198-group-algebra-add field a b)
       u)
      (q656198-module-add
       field
       group
       module
       (q656198-module-smul field group module a u)
       (q656198-module-smul field group module b u)))
     (equal
      (q656198-module-smul
       field
       group
       module
       (q656198-group-algebra-multiply
        field group group-elements a b)
       u)
      (q656198-module-smul
       field
       group
       module
       a
       (q656198-module-smul field group module b u)))))))

(defun q656198-module-p (field group group-elements module)
  (and
   (q656198-module-element-p
    field
    group
    module
    (q656198-module-zero field group module))
   (q656198-module-laws-p
    field group group-elements module)))

;; A submodule is an arbitrary internally tagged predicate on the module,
;; closed under zero, addition, negation, and every group-algebra scalar.

(defun-sk q656198-submodule-laws-p
    (field group group-elements module submodule)
  (forall
   (a u v)
   (implies
    (and
     (q656198-group-algebra-element-p
      field group-elements a)
     (q656198-submodule-member-p
      field group module submodule u)
     (q656198-submodule-member-p
      field group module submodule v))
    (and
     (q656198-module-element-p field group module u)
     (q656198-module-element-p field group module v)
     (q656198-submodule-member-p
      field
      group
      module
      submodule
      (q656198-module-add field group module u v))
     (q656198-submodule-member-p
      field
      group
      module
      submodule
      (q656198-module-negate field group module u))
     (q656198-submodule-member-p
      field
      group
      module
      submodule
      (q656198-module-smul field group module a u))))))

(defun q656198-submodule-p
    (field group group-elements module submodule)
  (and
   (q656198-submodule-member-p
    field
    group
    module
    submodule
    (q656198-module-zero field group module))
   (q656198-submodule-laws-p
    field group group-elements module submodule)))

;; The existential witnesses for a sum decomposition, and the complement
;; submodule itself, remain internal to the translated statement.

(defun-sk q656198-sum-representation-p
    (field group module left-submodule right-submodule value)
  (exists
   (left-value right-value)
   (and
    (q656198-submodule-member-p
     field group module left-submodule left-value)
    (q656198-submodule-member-p
     field group module right-submodule right-value)
    (equal
     (q656198-module-add
      field group module left-value right-value)
     value))))

(defun-sk q656198-complement-laws-p
    (field group module submodule complement)
  (forall
   (x)
   (and
    (implies
     (and
      (q656198-submodule-member-p
       field group module submodule x)
      (q656198-submodule-member-p
       field group module complement x))
     (equal x (q656198-module-zero field group module)))
    (implies
     (q656198-module-element-p field group module x)
     (q656198-sum-representation-p
      field group module submodule complement x)))))

(defun q656198-is-complement-p
    (field group group-elements module submodule complement)
  (and
   (q656198-submodule-p
    field group group-elements module complement)
   (q656198-complement-laws-p
    field group module submodule complement)))

(defun-sk q656198-complement-exists-p
    (field group group-elements module submodule)
  (exists
   (complement)
   (q656198-is-complement-p
    field group group-elements module submodule complement)))

(defun-sk thousand-theorems-q656198-maschke-s-theorem-statement ()
  (forall
   (field group group-elements module submodule)
   (implies
    (and
     (q656198-field-p field)
     (q656198-finite-group-p group group-elements)
     (q656198-cardinality-nonzero-p field group-elements)
     (q656198-module-p field group group-elements module)
     (q656198-submodule-p
      field group group-elements module submodule))
    (q656198-complement-exists-p
     field group group-elements module submodule))))

(value-triple :itpeval-statement-checked)
:q
