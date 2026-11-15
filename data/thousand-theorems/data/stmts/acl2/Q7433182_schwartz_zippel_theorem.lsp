;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q7433182, "Schwartz–Zippel theorem": for a
;; nonzero multivariate polynomial over an arbitrary commutative integral
;; domain, the fraction of zeros on a finite dependent product is bounded by
;; the support supremum of the sums of coordinate degrees divided by the
;; corresponding set cardinalities. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The integral-domain carrier and operations are arbitrary tame APPLY$
;; function objects. FN-EQUAL supplies universal quantification over the full
;; carrier. The polynomial and each member of the dependent family of finite
;; sets have their source-exact finite representations: a canonical sparse
;; exponent/coefficient list and a duplicate-free list, respectively.

(defun q7433182-quoted (object)
  (list 'quote object))

(defun q7433182-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q7433182-term-list (cdr terms)))
    (q7433182-quoted nil)))

(defun q7433182-static-apply-term (function arguments)
  (list 'apply$
        (q7433182-quoted function)
        (q7433182-term-list arguments)))

(defun q7433182-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q7433182-and-terms (cdr terms))
            (q7433182-quoted nil))
    (q7433182-quoted t)))

(defun q7433182-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q7433182-quoted t)
            (q7433182-or-terms (cdr terms)))
    (q7433182-quoted nil)))

(defun q7433182-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q7433182-quoted t)))

(defun q7433182-true-function (formals)
  (list 'lambda formals (q7433182-quoted t)))

(defun q7433182-universal-p (function formals)
  (let ((always-true (q7433182-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q7433182-member-p (carrier object)
  (if (apply$ carrier (list object)) t nil))

(defun q7433182-binary-value (function left right)
  (apply$ function (list left right)))

;; Arbitrary nontrivial commutative rings with no zero divisors.

(defun q7433182-ring-laws-function
    (carrier zero one add multiply negate)
  (let* ((add-xy (q7433182-static-apply-term add '(x y)))
         (add-yz (q7433182-static-apply-term add '(y z)))
         (mul-xy (q7433182-static-apply-term multiply '(x y)))
         (mul-yz (q7433182-static-apply-term multiply '(y z)))
         (neg-x (q7433182-static-apply-term negate '(x)))
         (domain
          (q7433182-and-terms
           (list
            (q7433182-static-apply-term carrier '(x))
            (q7433182-static-apply-term carrier '(y))
            (q7433182-static-apply-term carrier '(z))))))
    (list
     'lambda '(x y z)
     (q7433182-implies-term
      domain
      (q7433182-and-terms
       (list
        (q7433182-static-apply-term carrier (list add-xy))
        (q7433182-static-apply-term carrier (list mul-xy))
        (q7433182-static-apply-term carrier (list neg-x))
        (list 'equal
              (q7433182-static-apply-term add (list add-xy 'z))
              (q7433182-static-apply-term add (list 'x add-yz)))
        (list 'equal
              add-xy
              (q7433182-static-apply-term add '(y x)))
        (list 'equal
              (q7433182-static-apply-term
               add (list 'x (q7433182-quoted zero)))
              'x)
        (list 'equal
              (q7433182-static-apply-term add (list 'x neg-x))
              (q7433182-quoted zero))
        (list 'equal
              (q7433182-static-apply-term multiply (list mul-xy 'z))
              (q7433182-static-apply-term multiply (list 'x mul-yz)))
        (list 'equal
              mul-xy
              (q7433182-static-apply-term multiply '(y x)))
        (list 'equal
              (q7433182-static-apply-term
               multiply (list 'x (q7433182-quoted one)))
              'x)
        (list 'equal
              (q7433182-static-apply-term multiply (list 'x add-yz))
              (q7433182-static-apply-term
               add
               (list
                (q7433182-static-apply-term multiply '(x y))
                (q7433182-static-apply-term multiply '(x z)))))))))))

(defun q7433182-no-zero-divisors-function
    (carrier zero multiply)
  (list
   'lambda '(x y)
   (q7433182-implies-term
    (q7433182-and-terms
     (list
      (q7433182-static-apply-term carrier '(x))
      (q7433182-static-apply-term carrier '(y))
      (list 'equal
            (q7433182-static-apply-term multiply '(x y))
            (q7433182-quoted zero))))
    (q7433182-or-terms
     (list
      (list 'equal 'x (q7433182-quoted zero))
      (list 'equal 'y (q7433182-quoted zero)))))))

(defun q7433182-integral-domain-p
    (carrier zero one add multiply negate)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (q7433182-member-p carrier zero)
   (q7433182-member-p carrier one)
   (not (equal zero one))
   (q7433182-universal-p
    (q7433182-ring-laws-function
     carrier zero one add multiply negate)
    '(x y z))
   (q7433182-universal-p
    (q7433182-no-zero-divisors-function
     carrier zero multiply)
    '(x y))))

;; Canonical finite-support multivariate polynomials. Exponent vectors have
;; one natural coordinate for each variable. Terms are strictly ordered, so
;; every exponent occurs once, and zero coefficients are omitted.

(defun q7433182-natural-vector-p (vector length)
  (if (consp vector)
      (and
       (posp length)
       (natp (car vector))
       (q7433182-natural-vector-p
        (cdr vector) (- length 1)))
    (and
     (equal vector nil)
     (equal length 0))))

(defun q7433182-exponent-less-p (left right)
  (if (consp left)
      (if (< (car left) (car right))
          t
        (and
         (equal (car left) (car right))
         (q7433182-exponent-less-p
          (cdr left) (cdr right))))
    nil))

(defun q7433182-polynomial-tail-p
    (polynomial variable-count carrier zero
                previous have-previous)
  (if (consp polynomial)
      (let ((term (car polynomial)))
        (and
         (true-listp term)
         (equal (len term) 2)
         (q7433182-natural-vector-p
          (car term) variable-count)
         (q7433182-member-p carrier (cadr term))
         (not (equal (cadr term) zero))
         (or
          (not have-previous)
          (q7433182-exponent-less-p
           previous (car term)))
         (q7433182-polynomial-tail-p
          (cdr polynomial) variable-count carrier zero
          (car term) t)))
    (equal polynomial nil)))

(defun q7433182-polynomial-p
    (polynomial variable-count carrier zero)
  (and
   (natp variable-count)
   (true-listp polynomial)
   (q7433182-polynomial-tail-p
    polynomial variable-count carrier zero nil nil)))

;; A list of duplicate-free lists presents S : Fin n -> Finset R exactly.

(defun q7433182-set-elements-p (elements carrier)
  (if (consp elements)
      (and
       (q7433182-member-p carrier (car elements))
       (q7433182-set-elements-p (cdr elements) carrier))
    (equal elements nil)))

(defun q7433182-finset-p (elements carrier)
  (and
   (true-listp elements)
   (no-duplicatesp-equal elements)
   (q7433182-set-elements-p elements carrier)))

(defun q7433182-dependent-finsets-p
    (sets variable-count carrier)
  (if (consp sets)
      (and
       (posp variable-count)
       (q7433182-finset-p (car sets) carrier)
       (q7433182-dependent-finsets-p
        (cdr sets) (- variable-count 1) carrier))
    (and
     (equal sets nil)
     (equal variable-count 0))))

;; Exact evaluation in the represented integral domain.

(defun q7433182-domain-power
    (value exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q7433182-binary-value
     multiply
     value
     (q7433182-domain-power
      value (- exponent 1) one multiply))))

(defun q7433182-monomial-eval
    (exponents point one multiply)
  (if (consp exponents)
      (q7433182-binary-value
       multiply
       (q7433182-domain-power
        (car point) (car exponents) one multiply)
       (q7433182-monomial-eval
        (cdr exponents) (cdr point) one multiply))
    one))

(defun q7433182-polynomial-eval
    (polynomial point zero one add multiply)
  (if (consp polynomial)
      (q7433182-binary-value
       add
       (q7433182-binary-value
        multiply
        (cadar polynomial)
        (q7433182-monomial-eval
         (caar polynomial) point one multiply))
       (q7433182-polynomial-eval
        (cdr polynomial) point zero one add multiply))
    zero))

;; Exact enumeration of the dependent Cartesian product.

(defun q7433182-prepend-to-points (value points)
  (if (consp points)
      (cons
       (cons value (car points))
       (q7433182-prepend-to-points value (cdr points)))
    nil))

(defun q7433182-extend-points (values points)
  (if (consp values)
      (append
       (q7433182-prepend-to-points
        (car values) points)
       (q7433182-extend-points
        (cdr values) points))
    nil))

(defun q7433182-all-points (sets)
  (if (consp sets)
      (q7433182-extend-points
       (car sets)
       (q7433182-all-points (cdr sets)))
    (list nil)))

(defun q7433182-count-zeros
    (points polynomial zero one add multiply)
  (if (consp points)
      (+
       (if
        (equal
         (q7433182-polynomial-eval
          polynomial (car points) zero one add multiply)
         zero)
        1
        0)
       (q7433182-count-zeros
        (cdr points) polynomial zero one add multiply))
    0))

(defun q7433182-cardinality-product (sets)
  (if (consp sets)
      (*
       (len (car sets))
       (q7433182-cardinality-product (cdr sets)))
    1))

;; Division by zero is explicitly totalized to zero, matching division on the
;; nonnegative rationals used by the source.

(defun q7433182-nonnegative-ratio
    (numerator denominator)
  (if (zp denominator)
      0
    (/ numerator denominator)))

(defun q7433182-support-sum (exponents sets)
  (if (consp exponents)
      (+
       (q7433182-nonnegative-ratio
        (car exponents) (len (car sets)))
       (q7433182-support-sum
        (cdr exponents) (cdr sets)))
    0))

(defun q7433182-support-supremum (polynomial sets)
  (if (consp polynomial)
      (max
       (q7433182-support-sum
        (caar polynomial) sets)
       (q7433182-support-supremum
        (cdr polynomial) sets))
    0))

(defun thousand-theorems-q7433182-schwartz-zippel-theorem-statement
    (variable-count polynomial sets
                    carrier zero one add multiply negate)
  (implies
   (and
    (q7433182-integral-domain-p
     carrier zero one add multiply negate)
    (q7433182-polynomial-p
     polynomial variable-count carrier zero)
    (consp polynomial)
   (q7433182-dependent-finsets-p
     sets variable-count carrier))
   (<=
    (q7433182-nonnegative-ratio
     (q7433182-count-zeros
      (q7433182-all-points sets)
      polynomial zero one add multiply)
     (q7433182-cardinality-product sets))
    (q7433182-support-supremum
     polynomial sets))))

;; Admission-time tameness audit for every reified lambda used above.

(defun q7433182-all-reified-functions-tame-p ()
  (let ((unary '(lambda (x) (quote t)))
        (binary '(lambda (x y) x)))
    (and
     (tamep-functionp
      (q7433182-true-function '(x)))
     (tamep-functionp
      (q7433182-ring-laws-function
       unary 0 1 binary binary unary))
     (tamep-functionp
      (q7433182-no-zero-divisors-function
       unary 0 binary)))))

(value-triple
 (if (q7433182-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q7433182-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
