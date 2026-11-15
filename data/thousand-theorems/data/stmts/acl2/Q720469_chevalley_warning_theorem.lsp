;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q720469, "Chevalley–Warning theorem": over a
;; finite field of characteristic p, if the sum of the total degrees of a
;; finite family of multivariate polynomials is smaller than the number of
;; variables, then p divides the number of their common zeros. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Duplicate-free lists present the finite field, variable type, and finite
;; polynomial index set. Operation tables are required to satisfy all field
;; laws on the carrier. A polynomial is a canonical sparse list of
;; (exponent-vector coefficient) terms. The polynomial list is aligned with
;; the index-set list, which is exactly the restriction of the source family
;; to the finite set occurring in the theorem.

(defun q720469-set-list-p (objects)
  (if (consp objects)
      (and (not (member-equal (car objects) (cdr objects)))
           (q720469-set-list-p (cdr objects)))
    (equal objects nil)))

(defun q720469-lookup-unary (x table)
  (cdr (assoc-equal x table)))

(defun q720469-lookup-binary (x y table)
  (cdr (assoc-equal (list x y) table)))

(defun q720469-field-z-laws-p
    (zs x y add-table multiply-table)
  (if (consp zs)
      (let ((z (car zs)))
        (and
         (equal
          (q720469-lookup-binary
           (q720469-lookup-binary x y add-table)
           z add-table)
          (q720469-lookup-binary
           x
           (q720469-lookup-binary y z add-table)
           add-table))
         (equal
          (q720469-lookup-binary
           (q720469-lookup-binary x y multiply-table)
           z multiply-table)
          (q720469-lookup-binary
           x
           (q720469-lookup-binary y z multiply-table)
           multiply-table))
         (equal
          (q720469-lookup-binary
           x
           (q720469-lookup-binary y z add-table)
           multiply-table)
          (q720469-lookup-binary
           (q720469-lookup-binary x y multiply-table)
           (q720469-lookup-binary x z multiply-table)
           add-table))
         (q720469-field-z-laws-p
          (cdr zs) x y add-table multiply-table)))
    (equal zs nil)))

(defun q720469-field-y-laws-p
    (ys carrier x add-table multiply-table)
  (if (consp ys)
      (let* ((y (car ys))
             (sum (q720469-lookup-binary x y add-table))
             (product
              (q720469-lookup-binary x y multiply-table)))
        (and
         (assoc-equal (list x y) add-table)
         (member-equal sum carrier)
         (assoc-equal (list x y) multiply-table)
         (member-equal product carrier)
         (equal sum
                (q720469-lookup-binary y x add-table))
         (equal product
                (q720469-lookup-binary y x multiply-table))
         (q720469-field-z-laws-p
          carrier x y add-table multiply-table)
         (q720469-field-y-laws-p
          (cdr ys) carrier x add-table multiply-table)))
    (equal ys nil)))

(defun q720469-field-x-laws-p
    (xs carrier zero one add-table multiply-table
        negate-table inverse-table)
  (if (consp xs)
      (let* ((x (car xs))
             (negative (q720469-lookup-unary x negate-table))
             (inverse (q720469-lookup-unary x inverse-table)))
        (and
         (assoc-equal x negate-table)
         (member-equal negative carrier)
         (assoc-equal x inverse-table)
         (member-equal inverse carrier)
         (equal
          (q720469-lookup-binary x zero add-table)
          x)
         (equal
          (q720469-lookup-binary x negative add-table)
          zero)
         (equal
          (q720469-lookup-binary x one multiply-table)
          x)
         (implies
          (not (equal x zero))
          (equal
           (q720469-lookup-binary x inverse multiply-table)
           one))
         (q720469-field-y-laws-p
          carrier carrier x add-table multiply-table)
         (q720469-field-x-laws-p
          (cdr xs) carrier zero one add-table multiply-table
          negate-table inverse-table)))
    (equal xs nil)))

(defun q720469-finite-field-p
    (carrier zero one add-table multiply-table
        negate-table inverse-table)
  (and
   (q720469-set-list-p carrier)
   (consp carrier)
   (member-equal zero carrier)
   (member-equal one carrier)
   (not (equal zero one))
   (q720469-field-x-laws-p
    carrier carrier zero one add-table multiply-table
    negate-table inverse-table)))

;; For a finite field, CharP K p is equivalently that p is the least positive
;; natural number whose multiple of one is zero.

(defun q720469-natural-multiple
    (count value zero add-table)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (q720469-lookup-binary
     value
     (q720469-natural-multiple
      (- count 1) value zero add-table)
     add-table)))

(defun q720469-smaller-multiples-nonzero-p
    (count one zero add-table)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (not
      (equal
       (q720469-natural-multiple count one zero add-table)
       zero))
     (q720469-smaller-multiples-nonzero-p
      (- count 1) one zero add-table))))

(defun q720469-characteristic-p
    (p one zero add-table)
  (and
   (posp p)
   (equal
    (q720469-natural-multiple p one zero add-table)
    zero)
   (q720469-smaller-multiples-nonzero-p
    (- p 1) one zero add-table)))

;; Canonical sparse multivariate polynomials.

(defun q720469-all-members-p (objects carrier)
  (if (consp objects)
      (and (member-equal (car objects) carrier)
           (q720469-all-members-p (cdr objects) carrier))
    (equal objects nil)))

(defun q720469-natural-vector-p (vector length)
  (if (consp vector)
      (and
       (posp length)
       (natp (car vector))
       (q720469-natural-vector-p
        (cdr vector) (- length 1)))
    (and (equal vector nil)
         (equal length 0))))

(defun q720469-exponent-less-p (left right)
  (if (consp left)
      (if (< (car left) (car right))
          t
        (and
         (equal (car left) (car right))
         (q720469-exponent-less-p
          (cdr left) (cdr right))))
    nil))

(defun q720469-polynomial-tail-p
    (polynomial variable-count carrier zero
                previous have-previous)
  (if (consp polynomial)
      (let ((term (car polynomial)))
        (and
         (true-listp term)
         (equal (len term) 2)
         (q720469-natural-vector-p
          (car term) variable-count)
         (member-equal (cadr term) carrier)
         (not (equal (cadr term) zero))
         (or
          (not have-previous)
          (q720469-exponent-less-p previous (car term)))
         (q720469-polynomial-tail-p
          (cdr polynomial) variable-count carrier zero
          (car term) t)))
    (equal polynomial nil)))

(defun q720469-polynomial-p
    (polynomial variable-count carrier zero)
  (and
   (natp variable-count)
   (true-listp polynomial)
   (q720469-polynomial-tail-p
    polynomial variable-count carrier zero nil nil)))

(defun q720469-polynomial-family-p
    (polynomials variable-count carrier zero)
  (if (consp polynomials)
      (and
       (q720469-polynomial-p
        (car polynomials) variable-count carrier zero)
       (q720469-polynomial-family-p
        (cdr polynomials) variable-count carrier zero))
    (equal polynomials nil)))

(defun q720469-exponent-sum (exponents)
  (if (consp exponents)
      (+ (car exponents)
         (q720469-exponent-sum (cdr exponents)))
    0))

(defun q720469-polynomial-total-degree (polynomial)
  (if (consp polynomial)
      (max
       (q720469-exponent-sum (caar polynomial))
       (q720469-polynomial-total-degree (cdr polynomial)))
    0))

(defun q720469-family-degree-sum (polynomials)
  (if (consp polynomials)
      (+
       (q720469-polynomial-total-degree (car polynomials))
       (q720469-family-degree-sum (cdr polynomials)))
    0))

;; Evaluation and exact enumeration of the function space sigma -> K.

(defun q720469-field-power
    (value exponent one multiply-table)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q720469-lookup-binary
     value
     (q720469-field-power
      value (- exponent 1) one multiply-table)
     multiply-table)))

(defun q720469-monomial-eval
    (exponents point one multiply-table)
  (if (consp exponents)
      (q720469-lookup-binary
       (q720469-field-power
        (car point) (car exponents) one multiply-table)
       (q720469-monomial-eval
        (cdr exponents) (cdr point) one multiply-table)
       multiply-table)
    one))

(defun q720469-polynomial-eval
    (polynomial point zero one add-table multiply-table)
  (if (consp polynomial)
      (q720469-lookup-binary
       (q720469-lookup-binary
        (cadar polynomial)
        (q720469-monomial-eval
         (caar polynomial) point one multiply-table)
        multiply-table)
       (q720469-polynomial-eval
        (cdr polynomial) point zero one
        add-table multiply-table)
       add-table)
    zero))

(defun q720469-prepend-to-points (value points)
  (if (consp points)
      (cons
       (cons value (car points))
       (q720469-prepend-to-points value (cdr points)))
    nil))

(defun q720469-extend-points (values points)
  (if (consp values)
      (append
       (q720469-prepend-to-points (car values) points)
       (q720469-extend-points (cdr values) points))
    nil))

(defun q720469-all-points (variable-count carrier)
  (declare (xargs :measure (nfix variable-count)))
  (if (zp variable-count)
      (list nil)
    (q720469-extend-points
     carrier
     (q720469-all-points (- variable-count 1) carrier))))

(defun q720469-common-zero-p
    (polynomials point zero one add-table multiply-table)
  (if (consp polynomials)
      (and
       (equal
        (q720469-polynomial-eval
         (car polynomials) point zero one
         add-table multiply-table)
        zero)
       (q720469-common-zero-p
        (cdr polynomials) point zero one
        add-table multiply-table))
    (equal polynomials nil)))

(defun q720469-count-common-zeros
    (points polynomials zero one add-table multiply-table)
  (if (consp points)
      (+
       (if
        (q720469-common-zero-p
         polynomials (car points) zero one
         add-table multiply-table)
        1
        0)
       (q720469-count-common-zeros
        (cdr points) polynomials zero one
        add-table multiply-table))
    0))

(defun thousand-theorems-q720469-chevalley-warning-theorem-statement
    (variables indices polynomials
               carrier zero one add-table multiply-table
               negate-table inverse-table p)
  (implies
   (and
    (q720469-set-list-p variables)
    (q720469-set-list-p indices)
    (equal (len polynomials) (len indices))
    (q720469-finite-field-p
     carrier zero one add-table multiply-table
     negate-table inverse-table)
    (q720469-characteristic-p p one zero add-table)
    (q720469-polynomial-family-p
     polynomials (len variables) carrier zero))
   (implies
    (< (q720469-family-degree-sum polynomials)
       (len variables))
    (equal
     (mod
      (q720469-count-common-zeros
       (q720469-all-points (len variables) carrier)
       polynomials zero one add-table multiply-table)
      p)
     0))))

(value-triple :itpeval-statement-checked)
:q
