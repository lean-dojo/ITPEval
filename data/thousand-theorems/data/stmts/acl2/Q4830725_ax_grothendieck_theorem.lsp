;; Statement-only formalization of thousand-theorems corpus artifact Q4830725,
;; "Ax–Grothendieck theorem": over an algebraically closed field, an injective
;; polynomial self-map of an affine algebraic zero locus is surjective on that
;; zero locus. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; FIELD is an arbitrary field tag.  INDICES is a duplicate-free list
;; presenting an arbitrary finite index type.  Sparse canonical polynomials
;; and coordinate lists then present MvPolynomial INDICES FIELD and
;; INDICES -> FIELD without bounding either the field carrier or its values.

(defstub q4830725-field-member-p (field value) t)
(defstub q4830725-zero (field) t)
(defstub q4830725-one (field) t)
(defstub q4830725-add (field left right) t)
(defstub q4830725-multiply (field left right) t)
(defstub q4830725-negate (field value) t)
(defstub q4830725-inverse (field value) t)

(defun-sk q4830725-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (q4830725-field-member-p field x)
      (q4830725-field-member-p field y)
      (q4830725-field-member-p field z))
     (let* ((zero (q4830725-zero field))
            (one (q4830725-one field))
            (xy-add (q4830725-add field x y))
            (yz-add (q4830725-add field y z))
            (xy-mul (q4830725-multiply field x y))
            (yz-mul (q4830725-multiply field y z))
            (neg-x (q4830725-negate field x))
            (inv-x (q4830725-inverse field x)))
       (and
        (q4830725-field-member-p field xy-add)
        (q4830725-field-member-p field xy-mul)
        (q4830725-field-member-p field neg-x)
        (q4830725-field-member-p field inv-x)
        (equal
         (q4830725-add field xy-add z)
         (q4830725-add field x yz-add))
        (equal xy-add (q4830725-add field y x))
        (equal (q4830725-add field x zero) x)
        (equal (q4830725-add field x neg-x) zero)
        (equal
         (q4830725-multiply field xy-mul z)
         (q4830725-multiply field x yz-mul))
        (equal xy-mul (q4830725-multiply field y x))
        (equal (q4830725-multiply field x one) x)
        (equal
         (q4830725-multiply
          field x (q4830725-add field y z))
         (q4830725-add
          field
          (q4830725-multiply field x y)
          (q4830725-multiply field x z)))
        (equal (q4830725-inverse field zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q4830725-multiply field x inv-x)
          one)))))))

(defun q4830725-field-p (field)
  (and
   (q4830725-field-member-p field (q4830725-zero field))
   (q4830725-field-member-p field (q4830725-one field))
   (not (equal (q4830725-zero field)
               (q4830725-one field)))
   (q4830725-field-laws-p field)))

;; Algebraic closedness is the usual assertion that every nonconstant
;; univariate polynomial over the field has a root.

(defun q4830725-field-list-p (field values)
  (if (consp values)
      (and
       (q4830725-field-member-p field (car values))
       (q4830725-field-list-p field (cdr values)))
    (equal values nil)))

(defun q4830725-univariate-polynomial-p (field coefficients)
  (and
   (true-listp coefficients)
   (consp (cdr coefficients))
   (q4830725-field-list-p field coefficients)
   (not
    (equal
     (car (last coefficients))
     (q4830725-zero field)))))

(defun q4830725-univariate-eval (field coefficients x)
  (if (consp coefficients)
      (q4830725-add
       field
       (car coefficients)
       (q4830725-multiply
        field
        x
        (q4830725-univariate-eval
         field (cdr coefficients) x)))
    (q4830725-zero field)))

(defun-sk q4830725-root-exists-p (field coefficients)
  (exists (root)
    (and
     (q4830725-field-member-p field root)
     (equal
      (q4830725-univariate-eval
       field coefficients root)
      (q4830725-zero field)))))

(defun-sk q4830725-algebraically-closed-p (field)
  (forall (coefficients)
    (implies
     (q4830725-univariate-polynomial-p
      field coefficients)
     (q4830725-root-exists-p
      field coefficients))))

(defun q4830725-algebraically-closed-field-p (field)
  (and
   (q4830725-field-p field)
   (q4830725-algebraically-closed-p field)))

;; Canonical sparse multivariate polynomials.  A term is
;; (EXPONENT-VECTOR COEFFICIENT), terms are lexicographically ordered, and
;; zero coefficients are omitted.

(defun q4830725-nat-vector-p (vector length)
  (and
   (true-listp vector)
   (equal (len vector) length)
   (if (consp vector)
       (and
        (natp (car vector))
        (q4830725-nat-vector-p
         (cdr vector) (- length 1)))
     (equal length 0))))

(defun q4830725-exp-less-p (left right)
  (if (consp left)
      (if (< (car left) (car right))
          t
        (and
         (equal (car left) (car right))
         (q4830725-exp-less-p
          (cdr left) (cdr right))))
    nil))

(defun q4830725-polynomial-tail-p
    (field polynomial dimension previous have-previous)
  (if (consp polynomial)
      (let ((term (car polynomial)))
        (and
         (true-listp term)
         (equal (len term) 2)
         (q4830725-nat-vector-p
          (car term) dimension)
         (q4830725-field-member-p field (cadr term))
         (not
          (equal (cadr term) (q4830725-zero field)))
         (or
          (not have-previous)
          (q4830725-exp-less-p
           previous (car term)))
         (q4830725-polynomial-tail-p
          field (cdr polynomial) dimension
          (car term) t)))
    (equal polynomial nil)))

(defun q4830725-polynomial-p
    (field indices polynomial)
  (and
   (true-listp polynomial)
   (q4830725-polynomial-tail-p
    field polynomial (len indices) nil nil)))

(defun q4830725-poly-add (field left right)
  (declare
   (xargs
    :measure
    (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((equal (caar left) (caar right))
    (let ((coefficient
           (q4830725-add
            field (cadar left) (cadar right))))
      (if (equal coefficient (q4830725-zero field))
          (q4830725-poly-add
           field (cdr left) (cdr right))
        (cons
         (list (caar left) coefficient)
         (q4830725-poly-add
          field (cdr left) (cdr right))))))
   ((q4830725-exp-less-p
     (caar left) (caar right))
    (cons
     (car left)
     (q4830725-poly-add
      field (cdr left) right)))
   (t
    (cons
     (car right)
     (q4830725-poly-add
      field left (cdr right))))))

(defun q4830725-poly-negate (field polynomial)
  (if (consp polynomial)
      (let ((coefficient
             (q4830725-negate
              field (cadar polynomial))))
        (if (equal coefficient (q4830725-zero field))
            (q4830725-poly-negate
             field (cdr polynomial))
          (cons
           (list (caar polynomial) coefficient)
           (q4830725-poly-negate
            field (cdr polynomial)))))
    nil))

(defun q4830725-exp-add (left right)
  (if (consp left)
      (cons
       (+ (car left) (car right))
       (q4830725-exp-add
        (cdr left) (cdr right)))
    nil))

(defun q4830725-poly-insert-term
    (field term polynomial)
  (cond
   ((equal (cadr term) (q4830725-zero field))
    polynomial)
   ((endp polynomial)
    (list term))
   ((equal (car term) (caar polynomial))
    (let ((coefficient
           (q4830725-add
            field
            (cadr term)
            (cadar polynomial))))
      (if (equal coefficient (q4830725-zero field))
          (cdr polynomial)
        (cons
         (list (car term) coefficient)
         (cdr polynomial)))))
   ((q4830725-exp-less-p
     (car term) (caar polynomial))
    (cons term polynomial))
   (t
    (cons
     (car polynomial)
     (q4830725-poly-insert-term
      field term (cdr polynomial))))))

(defun q4830725-poly-mul-row
    (field term polynomial accumulator)
  (if (consp polynomial)
      (q4830725-poly-mul-row
       field
       term
       (cdr polynomial)
       (q4830725-poly-insert-term
        field
        (list
         (q4830725-exp-add
          (car term) (caar polynomial))
         (q4830725-multiply
          field
          (cadr term)
          (cadar polynomial)))
        accumulator))
    accumulator))

(defun q4830725-poly-multiply-acc
    (field left right accumulator)
  (if (consp left)
      (q4830725-poly-multiply-acc
       field
       (cdr left)
       right
       (q4830725-poly-mul-row
        field (car left) right accumulator))
    accumulator))

(defun q4830725-poly-multiply
    (field left right)
  (q4830725-poly-multiply-acc
   field left right nil))

(defun q4830725-field-power
    (field base exponent)
  (if (zp exponent)
      (q4830725-one field)
    (q4830725-multiply
     field
     base
     (q4830725-field-power
      field base (- exponent 1)))))

(defun q4830725-monomial-eval
    (field exponents point)
  (if (consp exponents)
      (q4830725-multiply
       field
       (q4830725-field-power
        field (car point) (car exponents))
       (q4830725-monomial-eval
        field (cdr exponents) (cdr point)))
    (q4830725-one field)))

(defun q4830725-polynomial-eval
    (field polynomial point)
  (if (consp polynomial)
      (q4830725-add
       field
       (q4830725-multiply
        field
        (cadar polynomial)
        (q4830725-monomial-eval
         field (caar polynomial) point))
       (q4830725-polynomial-eval
        field (cdr polynomial) point))
    (q4830725-zero field)))

(defun q4830725-point-p (field indices point)
  (and
   (true-listp point)
   (equal (len point) (len indices))
   (q4830725-field-list-p field point)))

(defun q4830725-polynomial-map-tail-p
    (field indices remaining polynomials)
  (if (consp remaining)
      (and
       (consp polynomials)
       (q4830725-polynomial-p
        field indices (car polynomials))
       (q4830725-polynomial-map-tail-p
        field indices (cdr remaining) (cdr polynomials)))
    (equal polynomials nil)))

(defun q4830725-polynomial-map-p
    (field indices polynomials)
  (q4830725-polynomial-map-tail-p
   field indices indices polynomials))

(defun q4830725-evaluate-map
    (field polynomials point)
  (if (consp polynomials)
      (cons
       (q4830725-polynomial-eval
        field (car polynomials) point)
       (q4830725-evaluate-map
        field (cdr polynomials) point))
    nil))

;; An arbitrary ideal is retained as an arbitrary membership predicate on
;; canonical polynomials; it is not replaced by a chosen finite generating
;; family.

(defstub q4830725-ideal-member-p
  (field indices ideal polynomial)
  t)

(defun-sk q4830725-ideal-closure-p
    (field indices ideal)
  (forall (left right multiplier)
    (and
     (implies
      (and
       (q4830725-polynomial-p
        field indices left)
       (q4830725-polynomial-p
        field indices right)
       (q4830725-ideal-member-p
        field indices ideal left)
       (q4830725-ideal-member-p
        field indices ideal right))
      (q4830725-ideal-member-p
       field indices ideal
       (q4830725-poly-add field left right)))
     (implies
      (and
       (q4830725-polynomial-p
        field indices left)
       (q4830725-ideal-member-p
        field indices ideal left))
      (q4830725-ideal-member-p
       field indices ideal
       (q4830725-poly-negate field left)))
     (implies
      (and
       (q4830725-polynomial-p
        field indices left)
       (q4830725-polynomial-p
        field indices multiplier)
       (q4830725-ideal-member-p
        field indices ideal left))
      (q4830725-ideal-member-p
       field indices ideal
       (q4830725-poly-multiply
        field multiplier left))))))

(defun q4830725-ideal-p (field indices ideal)
  (and
   (q4830725-ideal-member-p
    field indices ideal nil)
   (q4830725-ideal-closure-p
    field indices ideal)))

(defun-sk q4830725-common-zero-p
    (field indices ideal point)
  (forall (polynomial)
    (implies
     (and
      (q4830725-polynomial-p
       field indices polynomial)
      (q4830725-ideal-member-p
       field indices ideal polynomial))
     (equal
      (q4830725-polynomial-eval
       field polynomial point)
      (q4830725-zero field)))))

(defun q4830725-zero-locus-p
    (field indices ideal point)
  (and
   (q4830725-point-p field indices point)
   (q4830725-common-zero-p
    field indices ideal point)))

(defun-sk q4830725-maps-to-p
    (field indices ideal polynomials)
  (forall (point)
    (implies
     (q4830725-zero-locus-p
      field indices ideal point)
     (q4830725-zero-locus-p
      field indices ideal
      (q4830725-evaluate-map
       field polynomials point)))))

(defun-sk q4830725-injective-on-p
    (field indices ideal polynomials)
  (forall (left right)
    (implies
     (and
      (q4830725-zero-locus-p
       field indices ideal left)
      (q4830725-zero-locus-p
       field indices ideal right)
      (equal
       (q4830725-evaluate-map
        field polynomials left)
       (q4830725-evaluate-map
        field polynomials right)))
     (equal left right))))

(defun-sk q4830725-preimage-exists-p
    (field indices ideal polynomials target)
  (exists (source)
    (and
     (q4830725-zero-locus-p
      field indices ideal source)
     (equal
      (q4830725-evaluate-map
       field polynomials source)
      target))))

(defun-sk q4830725-surjective-on-p
    (field indices ideal polynomials)
  (forall (target)
    (implies
     (q4830725-zero-locus-p
      field indices ideal target)
     (q4830725-preimage-exists-p
      field indices ideal polynomials target))))

(defun-sk
  thousand-theorems-q4830725-ax-grothendieck-statement
  ()
  (forall (field indices ideal polynomials)
    (implies
     (and
      (true-listp indices)
      (no-duplicatesp-equal indices)
      (q4830725-algebraically-closed-field-p field)
      (q4830725-ideal-p field indices ideal)
      (q4830725-polynomial-map-p
       field indices polynomials))
     (implies
      (q4830725-maps-to-p
       field indices ideal polynomials)
      (implies
       (q4830725-injective-on-p
        field indices ideal polynomials)
       (q4830725-surjective-on-p
        field indices ideal polynomials))))))

(value-triple :itpeval-statement-checked)
:q
