;; Statement-only formalization of thousand-theorems corpus artifact Q203565,
;; "Solutions of a general cubic equation": Cardano's characterization of the
;; roots of a cubic over an arbitrary field with invertible 2 and 3 and a
;; primitive cube root of unity. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative function symbols present an arbitrary, potentially infinite
;; field indexed by FIELD. The declarations supply no laws; every field axiom
;; used by the source statement is explicit in Q203565-FIELD-P.

(defstub q203565-element-p (field value) t)
(defstub q203565-zero (field) t)
(defstub q203565-one (field) t)
(defstub q203565-add (field left right) t)
(defstub q203565-multiply (field left right) t)
(defstub q203565-negate (field value) t)
(defstub q203565-inverse (field value) t)

(defun-sk q203565-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (q203565-element-p field x)
      (q203565-element-p field y)
      (q203565-element-p field z))
     (let* ((zero (q203565-zero field))
            (one (q203565-one field))
            (x-plus-y (q203565-add field x y))
            (y-plus-z (q203565-add field y z))
            (x-times-y (q203565-multiply field x y))
            (y-times-z (q203565-multiply field y z))
            (negative-x (q203565-negate field x))
            (inverse-x (q203565-inverse field x)))
       (and
        (q203565-element-p field x-plus-y)
        (q203565-element-p field x-times-y)
        (q203565-element-p field negative-x)
        (q203565-element-p field inverse-x)
        (equal
         (q203565-add field x-plus-y z)
         (q203565-add field x y-plus-z))
        (equal x-plus-y (q203565-add field y x))
        (equal (q203565-add field x zero) x)
        (equal (q203565-add field x negative-x) zero)
        (equal
         (q203565-multiply field x-times-y z)
         (q203565-multiply field x y-times-z))
        (equal x-times-y (q203565-multiply field y x))
        (equal (q203565-multiply field x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q203565-multiply field x inverse-x)
          one))
        (equal
         (q203565-multiply field x y-plus-z)
         (q203565-add
          field
          (q203565-multiply field x y)
          (q203565-multiply field x z))))))))

(defun q203565-field-p (field)
  (and
   (q203565-element-p field (q203565-zero field))
   (q203565-element-p field (q203565-one field))
   (not
    (equal
     (q203565-zero field)
     (q203565-one field)))
   (q203565-field-laws-p field)))

(defun q203565-subtract (field left right)
  (q203565-add
   field
   left
   (q203565-negate field right)))

(defun q203565-divide (field numerator denominator)
  (q203565-multiply
   field
   numerator
   (q203565-inverse field denominator)))

(defun q203565-nat (field number)
  (declare (xargs :measure (nfix number)))
  (if (zp number)
      (q203565-zero field)
    (q203565-add
     field
     (q203565-one field)
     (q203565-nat field (- number 1)))))

(defun q203565-power (field base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q203565-one field)
    (q203565-multiply
     field
     base
     (q203565-power field base (- exponent 1)))))

(defun q203565-primitive-cube-root-p (field omega)
  (and
   (equal
    (q203565-power field omega 3)
    (q203565-one field))
   (not
    (equal
     omega
     (q203565-one field)))
   (not
    (equal
     (q203565-power field omega 2)
     (q203565-one field)))))

(defun q203565-p-value (field a b c)
  (let* ((three (q203565-nat field 3))
         (nine (q203565-nat field 9))
         (three-a-c
          (q203565-multiply
           field
           (q203565-multiply field three a)
           c))
         (b-squared (q203565-power field b 2))
         (numerator
          (q203565-subtract field three-a-c b-squared))
         (denominator
          (q203565-multiply
           field
           nine
           (q203565-power field a 2))))
    (q203565-divide field numerator denominator)))

(defun q203565-q-value (field a b c d)
  (let* ((two (q203565-nat field 2))
         (nine (q203565-nat field 9))
         (twenty-seven (q203565-nat field 27))
         (fifty-four (q203565-nat field 54))
         (term-one
          (q203565-multiply
           field
           (q203565-multiply
            field
            (q203565-multiply field nine a)
            b)
           c))
         (term-two
          (q203565-multiply
           field
           two
           (q203565-power field b 3)))
         (term-three
          (q203565-multiply
           field
           (q203565-multiply
            field
            twenty-seven
            (q203565-power field a 2))
           d))
         (numerator
          (q203565-subtract
           field
           (q203565-subtract field term-one term-two)
           term-three))
         (denominator
          (q203565-multiply
           field
           fifty-four
           (q203565-power field a 3))))
    (q203565-divide field numerator denominator)))

(defun q203565-cubic-value (field a b c d x)
  (q203565-add
   field
   (q203565-add
    field
    (q203565-add
     field
     (q203565-multiply
      field a (q203565-power field x 3))
     (q203565-multiply
      field b (q203565-power field x 2)))
    (q203565-multiply field c x))
   d))

(defun q203565-root-shift (field a b)
  (q203565-divide
   field
   b
   (q203565-multiply
    field
    (q203565-nat field 3)
    a)))

(defun q203565-first-root (field a b s tm)
  (q203565-subtract
   field
   (q203565-subtract field s tm)
   (q203565-root-shift field a b)))

(defun q203565-second-root (field a b omega s tm)
  (q203565-subtract
   field
   (q203565-subtract
    field
    (q203565-multiply field s omega)
    (q203565-multiply
     field
     tm
     (q203565-power field omega 2)))
   (q203565-root-shift field a b)))

(defun q203565-third-root (field a b omega s tm)
  (q203565-subtract
   field
   (q203565-subtract
    field
    (q203565-multiply
     field
     s
     (q203565-power field omega 2))
    (q203565-multiply field tm omega))
   (q203565-root-shift field a b)))

(defun-sk
    thousand-theorems-q203565-solutions-of-a-general-cubic-equation-statement
    ()
  (forall (field a b c d omega p q r s tm x)
    (implies
     (and
      (q203565-field-p field)
      (q203565-element-p field a)
      (q203565-element-p field b)
      (q203565-element-p field c)
      (q203565-element-p field d)
      (q203565-element-p field omega)
      (q203565-element-p field p)
      (q203565-element-p field q)
      (q203565-element-p field r)
      (q203565-element-p field s)
      (q203565-element-p field tm)
      (q203565-element-p field x)
      (not
       (equal
        (q203565-nat field 2)
        (q203565-zero field)))
      (not
       (equal
        (q203565-nat field 3)
        (q203565-zero field)))
      (not
       (equal
        a
        (q203565-zero field)))
      (q203565-primitive-cube-root-p field omega)
      (equal p (q203565-p-value field a b c))
      (not
       (equal
        p
        (q203565-zero field)))
      (equal q (q203565-q-value field a b c d))
      (equal
       (q203565-power field r 2)
       (q203565-add
        field
        (q203565-power field q 2)
        (q203565-power field p 3)))
      (equal
       (q203565-power field s 3)
       (q203565-add field q r))
      (equal
       (q203565-multiply field tm s)
       p))
     (iff
      (equal
       (q203565-cubic-value field a b c d x)
       (q203565-zero field))
      (or
       (equal
        x
        (q203565-first-root field a b s tm))
       (equal
        x
        (q203565-second-root field a b omega s tm))
       (equal
        x
        (q203565-third-root field a b omega s tm)))))))

(value-triple :itpeval-statement-checked)
:q
