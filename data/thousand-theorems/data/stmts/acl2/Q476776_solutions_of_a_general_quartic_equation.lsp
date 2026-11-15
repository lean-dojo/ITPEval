;; Statement-only formalization of thousand-theorems corpus artifact Q476776,
;; "Solutions of a general quartic equation": Ferrari's characterization of
;; the four roots of a quartic over an arbitrary field with invertible 2,
;; using a nonzero depressed linear coefficient and a cubic-resolvent root.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative function symbols present an arbitrary, potentially infinite
;; field indexed by FIELD. The declarations supply no laws; every field axiom
;; used by the source statement is explicit in Q476776-FIELD-P.

(defstub q476776-element-p (field value) t)
(defstub q476776-zero (field) t)
(defstub q476776-one (field) t)
(defstub q476776-add (field left right) t)
(defstub q476776-multiply (field left right) t)
(defstub q476776-negate (field value) t)
(defstub q476776-inverse (field value) t)

(defun-sk q476776-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (q476776-element-p field x)
      (q476776-element-p field y)
      (q476776-element-p field z))
     (let* ((zero (q476776-zero field))
            (one (q476776-one field))
            (x-plus-y (q476776-add field x y))
            (y-plus-z (q476776-add field y z))
            (x-times-y (q476776-multiply field x y))
            (y-times-z (q476776-multiply field y z))
            (negative-x (q476776-negate field x))
            (inverse-x (q476776-inverse field x)))
       (and
        (q476776-element-p field x-plus-y)
        (q476776-element-p field x-times-y)
        (q476776-element-p field negative-x)
        (q476776-element-p field inverse-x)
        (equal
         (q476776-add field x-plus-y z)
         (q476776-add field x y-plus-z))
        (equal x-plus-y (q476776-add field y x))
        (equal (q476776-add field x zero) x)
        (equal (q476776-add field x negative-x) zero)
        (equal
         (q476776-multiply field x-times-y z)
         (q476776-multiply field x y-times-z))
        (equal x-times-y (q476776-multiply field y x))
        (equal (q476776-multiply field x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q476776-multiply field x inverse-x)
          one))
        (equal
         (q476776-multiply field x y-plus-z)
         (q476776-add
          field
          (q476776-multiply field x y)
          (q476776-multiply field x z))))))))

(defun q476776-field-p (field)
  (and
   (q476776-element-p field (q476776-zero field))
   (q476776-element-p field (q476776-one field))
   (not
    (equal
     (q476776-zero field)
     (q476776-one field)))
   (q476776-field-laws-p field)))

(defun q476776-subtract (field left right)
  (q476776-add
   field
   left
   (q476776-negate field right)))

(defun q476776-divide (field numerator denominator)
  (q476776-multiply
   field
   numerator
   (q476776-inverse field denominator)))

(defun q476776-nat (field number)
  (declare (xargs :measure (nfix number)))
  (if (zp number)
      (q476776-zero field)
    (q476776-add
     field
     (q476776-one field)
     (q476776-nat field (- number 1)))))

(defun q476776-power (field base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q476776-one field)
    (q476776-multiply
     field
     base
     (q476776-power field base (- exponent 1)))))

(defun q476776-p-value (field a b c)
  (let* ((three (q476776-nat field 3))
         (eight (q476776-nat field 8))
         (a-squared (q476776-power field a 2))
         (b-squared (q476776-power field b 2))
         (eight-a-c
          (q476776-multiply
           field
           (q476776-multiply field eight a)
           c))
         (three-b-squared
          (q476776-multiply field three b-squared))
         (numerator
          (q476776-subtract
           field eight-a-c three-b-squared))
         (denominator
          (q476776-multiply field eight a-squared)))
    (q476776-divide field numerator denominator)))

(defun q476776-q-value (field a b c d)
  (let* ((four (q476776-nat field 4))
         (eight (q476776-nat field 8))
         (a-squared (q476776-power field a 2))
         (a-cubed (q476776-power field a 3))
         (b-cubed (q476776-power field b 3))
         (four-a-b-c
          (q476776-multiply
           field
           (q476776-multiply
            field
            (q476776-multiply field four a)
            b)
           c))
         (eight-a-squared-d
          (q476776-multiply
           field
           (q476776-multiply field eight a-squared)
           d))
         (numerator
          (q476776-add
           field
           (q476776-subtract
            field b-cubed four-a-b-c)
           eight-a-squared-d))
         (denominator
          (q476776-multiply field eight a-cubed)))
    (q476776-divide field numerator denominator)))

(defun q476776-r-value (field a b c d e)
  (let* ((three (q476776-nat field 3))
         (sixteen (q476776-nat field 16))
         (sixty-four (q476776-nat field 64))
         (two-hundred-fifty-six (q476776-nat field 256))
         (a-squared (q476776-power field a 2))
         (a-cubed (q476776-power field a 3))
         (a-fourth (q476776-power field a 4))
         (b-squared (q476776-power field b 2))
         (b-fourth (q476776-power field b 4))
         (sixteen-a-b-squared-c
          (q476776-multiply
           field
           (q476776-multiply
            field
            (q476776-multiply field sixteen a)
            b-squared)
           c))
         (two-hundred-fifty-six-a-cubed-e
          (q476776-multiply
           field
           (q476776-multiply
            field two-hundred-fifty-six a-cubed)
           e))
         (three-b-fourth
          (q476776-multiply field three b-fourth))
         (sixty-four-a-squared-b-d
          (q476776-multiply
           field
           (q476776-multiply
            field
            (q476776-multiply field sixty-four a-squared)
            b)
           d))
         (numerator
          (q476776-subtract
           field
           (q476776-subtract
            field
            (q476776-add
             field
             sixteen-a-b-squared-c
             two-hundred-fifty-six-a-cubed-e)
            three-b-fourth)
           sixty-four-a-squared-b-d))
         (denominator
          (q476776-multiply
           field two-hundred-fifty-six a-fourth)))
    (q476776-divide field numerator denominator)))

(defun q476776-resolvent-value (field p q r u)
  (let* ((four (q476776-nat field 4))
         (u-squared (q476776-power field u 2))
         (u-cubed (q476776-power field u 3))
         (q-squared (q476776-power field q 2))
         (p-u-squared
          (q476776-multiply field p u-squared))
         (four-r-u
          (q476776-multiply
           field
           (q476776-multiply field four r)
           u))
         (four-p-r
          (q476776-multiply
           field
           (q476776-multiply field four p)
           r)))
    (q476776-subtract
     field
     (q476776-add
      field
      (q476776-subtract
       field
       (q476776-subtract field u-cubed p-u-squared)
       four-r-u)
      four-p-r)
     q-squared)))

(defun q476776-quartic-value (field a b c d e x)
  (q476776-add
   field
   (q476776-add
    field
    (q476776-add
     field
     (q476776-add
      field
      (q476776-multiply
       field a (q476776-power field x 4))
      (q476776-multiply
       field b (q476776-power field x 3)))
     (q476776-multiply
      field c (q476776-power field x 2)))
    (q476776-multiply field d x))
   e))

(defun q476776-shift (field a b)
  (q476776-divide
   field
   b
   (q476776-multiply
    field
    (q476776-nat field 4)
    a)))

(defun q476776-first-root (field a b s v)
  (let* ((two (q476776-nat field 2))
         (four (q476776-nat field 4))
         (negative-two-s
          (q476776-negate
           field
           (q476776-multiply field two s)))
         (numerator
          (q476776-subtract field negative-two-s v)))
    (q476776-subtract
     field
     (q476776-divide field numerator four)
     (q476776-shift field a b))))

(defun q476776-second-root (field a b s v)
  (let* ((two (q476776-nat field 2))
         (four (q476776-nat field 4))
         (negative-two-s
          (q476776-negate
           field
           (q476776-multiply field two s)))
         (numerator
          (q476776-add field negative-two-s v)))
    (q476776-subtract
     field
     (q476776-divide field numerator four)
     (q476776-shift field a b))))

(defun q476776-third-root (field a b s w)
  (let* ((two (q476776-nat field 2))
         (four (q476776-nat field 4))
         (two-s (q476776-multiply field two s))
         (numerator (q476776-subtract field two-s w)))
    (q476776-subtract
     field
     (q476776-divide field numerator four)
     (q476776-shift field a b))))

(defun q476776-fourth-root (field a b s w)
  (let* ((two (q476776-nat field 2))
         (four (q476776-nat field 4))
         (two-s (q476776-multiply field two s))
         (numerator (q476776-add field two-s w)))
    (q476776-subtract
     field
     (q476776-divide field numerator four)
     (q476776-shift field a b))))

(defun-sk
    thousand-theorems-q476776-solutions-of-a-general-quartic-equation-statement
    ()
  (forall (field a b c d e p q r u s v w x)
    (let* ((zero (q476776-zero field))
           (two (q476776-nat field 2))
           (four (q476776-nat field 4))
           (eight (q476776-nat field 8))
           (s-squared (q476776-power field s 2))
           (q-over-s (q476776-divide field q s)))
      (implies
       (and
        (q476776-field-p field)
        (q476776-element-p field a)
        (q476776-element-p field b)
        (q476776-element-p field c)
        (q476776-element-p field d)
        (q476776-element-p field e)
        (q476776-element-p field p)
        (q476776-element-p field q)
        (q476776-element-p field r)
        (q476776-element-p field u)
        (q476776-element-p field s)
        (q476776-element-p field v)
        (q476776-element-p field w)
        (q476776-element-p field x)
        (not (equal two zero))
        (not (equal a zero))
        (equal p (q476776-p-value field a b c))
        (equal q (q476776-q-value field a b c d))
        (not (equal q zero))
        (equal r (q476776-r-value field a b c d e))
        (equal
         (q476776-resolvent-value field p q r u)
         zero)
        (equal
         s-squared
         (q476776-subtract field u p))
        (equal
         (q476776-power field v 2)
         (q476776-subtract
          field
          (q476776-multiply field four s-squared)
          (q476776-multiply
           field
           eight
           (q476776-subtract field u q-over-s))))
        (equal
         (q476776-power field w 2)
         (q476776-subtract
          field
          (q476776-multiply field four s-squared)
          (q476776-multiply
           field
           eight
           (q476776-add field u q-over-s)))))
       (iff
        (equal
         (q476776-quartic-value field a b c d e x)
         zero)
        (or
         (equal
          x
          (q476776-first-root field a b s v))
         (equal
          x
          (q476776-second-root field a b s v))
         (equal
          x
          (q476776-third-root field a b s w))
         (equal
          x
          (q476776-fourth-root field a b s w))))))))

(value-triple :itpeval-statement-checked)
:q
