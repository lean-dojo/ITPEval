;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_b2:
;; a complex polynomial satisfying P = Q P'' with quadratic Q has as many
;; distinct roots as its degree whenever it has two distinct roots. This file
;; contains no proof.

(in-package "ACL2")

;; Complex coefficients are represented through an arbitrary algebraically
;; closed field of characteristic zero.  Algebraic closure is presented by a
;; root-selection function for nonconstant polynomials, and characteristic
;; zero by the canonical embedding of the natural numbers.  These choices add
;; operations but no mathematical assumptions: choice supplies the selector,
;; and the natural embedding is unique.
;;
;; Canonical nonempty coefficient lists use ascending degree order.  The
;; evaluation laws make pointwise equality below exactly the source identity.
;; Algebraically closed fields of characteristic zero are elementarily
;; equivalent to the complex numbers, so this field-generic finite-polynomial
;; formulation is bidirectionally equivalent to the source statement.
;;
;; FN-EQUAL against a constant-T function expresses universal quantification
;; over the represented field.  Negated FN-EQUAL with a failure predicate
;; expresses the source's internal existential quantifiers for the two roots
;; and for the list of degree-many distinct roots.  Every generated traversal
;; lambda specializes its function positions to quoted tame function objects.

(defun putnam-1999-b2-quoted (object)
  (list 'quote object))

(defun putnam-1999-b2-apply1-term (function argument)
  (list
   'apply$
   (putnam-1999-b2-quoted function)
   (list 'cons argument nil)))

(defun putnam-1999-b2-apply2-term (function left right)
  (list
   'apply$
   (putnam-1999-b2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-1999-b2-and-term (terms)
  (if (endp terms)
      (putnam-1999-b2-quoted t)
    (list
     'if
     (car terms)
     (putnam-1999-b2-and-term (cdr terms))
     (putnam-1999-b2-quoted nil))))

(defun putnam-1999-b2-or-term (terms)
  (if (endp terms)
      (putnam-1999-b2-quoted nil)
    (list
     'if
     (car terms)
     (putnam-1999-b2-quoted t)
     (putnam-1999-b2-or-term (cdr terms)))))

(defun putnam-1999-b2-not-term (term)
  (list
   'if
   term
   (putnam-1999-b2-quoted nil)
   (putnam-1999-b2-quoted t)))

(defun putnam-1999-b2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-1999-b2-quoted t)))

(defun putnam-1999-b2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-1999-b2-quoted t)))

(defun putnam-1999-b2-carrier-term (carrier element)
  (putnam-1999-b2-apply1-term carrier element))

(defun putnam-1999-b2-operation-term (operation left right)
  (putnam-1999-b2-apply2-term operation left right))

(defun putnam-1999-b2-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-1999-b2-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-1999-b2-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-1999-b2-quoted
    (putnam-1999-b2-all-coefficients-function
     carrier))
   (putnam-1999-b2-quoted nil)
   coefficients))

(defun putnam-1999-b2-polynomial-term
    (carrier zero coefficients)
  (putnam-1999-b2-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-1999-b2-all-coefficients-term
     carrier coefficients)
    (putnam-1999-b2-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-1999-b2-quoted 1))
      (putnam-1999-b2-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-1999-b2-quoted zero))))))))

(defun putnam-1999-b2-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-1999-b2-quoted zero))
         (qone (putnam-1999-b2-quoted one))
         (add-xy
          (putnam-1999-b2-operation-term add x y))
         (add-yz
          (putnam-1999-b2-operation-term add y z))
         (mul-xy
          (putnam-1999-b2-operation-term mul x y))
         (mul-yz
          (putnam-1999-b2-operation-term mul y z))
         (neg-x
          (putnam-1999-b2-apply1-term neg x))
         (inv-x
          (putnam-1999-b2-apply1-term inv x))
         (domain
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-carrier-term carrier x)
            (putnam-1999-b2-carrier-term carrier y)
            (putnam-1999-b2-carrier-term carrier z))))
         (laws
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-carrier-term carrier add-xy)
            (putnam-1999-b2-carrier-term carrier mul-xy)
            (putnam-1999-b2-carrier-term carrier neg-x)
            (putnam-1999-b2-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-1999-b2-operation-term add add-xy z)
             (putnam-1999-b2-operation-term add x add-yz))
            (list
             'equal
             (putnam-1999-b2-operation-term mul mul-xy z)
             (putnam-1999-b2-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-1999-b2-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-1999-b2-operation-term mul y x))
            (list
             'equal
             (putnam-1999-b2-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-1999-b2-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-1999-b2-operation-term mul x qone)
             x)
            (putnam-1999-b2-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-1999-b2-implies-term
             (putnam-1999-b2-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-1999-b2-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-1999-b2-operation-term mul x add-yz)
             (putnam-1999-b2-operation-term
              add
              (putnam-1999-b2-operation-term mul x y)
              (putnam-1999-b2-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-1999-b2-implies-term domain laws))))

(defun putnam-1999-b2-natural-embedding-laws-function
    (carrier zero one add natural-embedding)
  (let* ((n 'n)
         (qzero (putnam-1999-b2-quoted zero))
         (qone (putnam-1999-b2-quoted one))
         (embedded-n
          (putnam-1999-b2-apply1-term natural-embedding n))
         (embedded-next
          (putnam-1999-b2-apply1-term
           natural-embedding
           (list 'binary-+ n (putnam-1999-b2-quoted 1))))
         (successor-law
          (list
           'equal
           embedded-next
           (putnam-1999-b2-operation-term
            add embedded-n qone)))
         (positive-n
          (list '< (putnam-1999-b2-quoted 0) n))
         (laws
          (putnam-1999-b2-and-term
           (list
            (list
             'equal
             (putnam-1999-b2-apply1-term
              natural-embedding
              (putnam-1999-b2-quoted 0))
             qzero)
            (putnam-1999-b2-implies-term
             (list 'natp n)
             (putnam-1999-b2-and-term
              (list
               (putnam-1999-b2-carrier-term
                carrier embedded-n)
               successor-law
               (putnam-1999-b2-implies-term
                positive-n
                (putnam-1999-b2-not-term
                 (list 'equal embedded-n qzero))))))))))
    (list 'lambda '(n) laws)))

(defun putnam-1999-b2-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-1999-b2-quoted zero))
         (domain
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-1999-b2-all-coefficients-term
             carrier rest)
            (putnam-1999-b2-carrier-term carrier x))))
         (empty-law
          (putnam-1999-b2-implies-term
           (putnam-1999-b2-carrier-term carrier x)
           (list
            'equal
            (putnam-1999-b2-operation-term
             evaluate
             (putnam-1999-b2-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-1999-b2-operation-term
           add
           coefficient
           (putnam-1999-b2-operation-term
            mul
            x
            (putnam-1999-b2-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-1999-b2-implies-term
           domain
           (putnam-1999-b2-and-term
            (list
             (putnam-1999-b2-carrier-term
              carrier
              (putnam-1999-b2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-1999-b2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-1999-b2-and-term
      (list empty-law recursive-law)))))

(defun putnam-1999-b2-root-selection-laws-function
    (carrier zero evaluate root-selector)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-1999-b2-apply1-term
           root-selector coefficients))
         (domain
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-polynomial-term
             carrier zero coefficients)
            (list
             '<
             (putnam-1999-b2-quoted 1)
             (list 'len coefficients)))))
         (laws
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-carrier-term carrier root)
            (list
             'equal
             (putnam-1999-b2-operation-term
              evaluate coefficients root)
             (putnam-1999-b2-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-1999-b2-implies-term domain laws))))

(defun putnam-1999-b2-algebraically-closed-field-p
    (carrier zero one add mul neg inv natural-embedding
             evaluate root-selector)
  (let* ((field-laws
          (putnam-1999-b2-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-1999-b2-true-function '(x y z)))
         (natural-embedding-laws
          (putnam-1999-b2-natural-embedding-laws-function
           carrier zero one add natural-embedding))
         (natural-embedding-laws-true
          (putnam-1999-b2-true-function '(n)))
         (evaluation-laws
          (putnam-1999-b2-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-1999-b2-true-function
           '(coefficient rest x)))
         (root-selection-laws
          (putnam-1999-b2-root-selection-laws-function
           carrier zero evaluate root-selector))
         (root-selection-laws-true
          (putnam-1999-b2-true-function
           '(coefficients))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp mul)
     (tamep-functionp neg)
     (tamep-functionp inv)
     (tamep-functionp natural-embedding)
     (tamep-functionp evaluate)
     (tamep-functionp root-selector)
     (tamep-functionp field-laws)
     (tamep-functionp field-laws-true)
     (tamep-functionp natural-embedding-laws)
     (tamep-functionp natural-embedding-laws-true)
     (tamep-functionp evaluation-laws)
     (tamep-functionp evaluation-laws-true)
     (tamep-functionp root-selection-laws)
     (tamep-functionp root-selection-laws-true)
     (apply$ carrier (list zero))
     (apply$ carrier (list one))
     (not (equal zero one))
     (fn-equal field-laws field-laws-true)
     (fn-equal
      natural-embedding-laws
      natural-embedding-laws-true)
     (fn-equal evaluation-laws evaluation-laws-true)
     (fn-equal
      root-selection-laws
      root-selection-laws-true))))

(defun putnam-1999-b2-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-1999-b2-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-1999-b2-polynomial-p
    (polynomial carrier zero)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-1999-b2-coefficient-list-p
    polynomial carrier)
   (or
    (equal (len polynomial) 1)
    (not (equal (car (last polynomial)) zero)))))

(defun putnam-1999-b2-natural-scale
    (add zero coefficient n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      zero
    (apply$
     add
     (list
      coefficient
      (putnam-1999-b2-natural-scale
       add zero coefficient (- n 1))))))

(defun putnam-1999-b2-derivative-aux
    (coefficients degree add zero)
  (if (endp coefficients)
      nil
    (cons
     (putnam-1999-b2-natural-scale
      add zero (car coefficients) degree)
     (putnam-1999-b2-derivative-aux
      (cdr coefficients) (+ degree 1) add zero))))

(defun putnam-1999-b2-derivative
    (polynomial add zero)
  (if (or (endp polynomial)
          (endp (cdr polynomial)))
      (list zero)
    (putnam-1999-b2-derivative-aux
     (cdr polynomial) 1 add zero)))

(defun putnam-1999-b2-second-derivative
    (polynomial add zero)
  (putnam-1999-b2-derivative
   (putnam-1999-b2-derivative
    polynomial add zero)
   add zero))

(defun putnam-1999-b2-identity-function
    (carrier mul evaluate polynomial quadratic second-derivative)
  (let* ((x 'x)
         (domain
          (putnam-1999-b2-carrier-term carrier x))
         (left
          (putnam-1999-b2-operation-term
           evaluate
           (putnam-1999-b2-quoted polynomial)
           x))
         (right
          (putnam-1999-b2-operation-term
           mul
           (putnam-1999-b2-operation-term
            evaluate
            (putnam-1999-b2-quoted quadratic)
            x)
           (putnam-1999-b2-operation-term
            evaluate
            (putnam-1999-b2-quoted second-derivative)
            x))))
    (list
     'lambda
     '(x)
     (putnam-1999-b2-implies-term
      domain
      (list 'equal left right)))))

(defun putnam-1999-b2-polynomial-identity-p
    (carrier zero add mul evaluate polynomial quadratic)
  (let* ((second-derivative
          (putnam-1999-b2-second-derivative
           polynomial add zero))
         (identity-function
          (putnam-1999-b2-identity-function
           carrier mul evaluate polynomial quadratic
           second-derivative))
         (true-function
          (putnam-1999-b2-true-function '(x))))
    (and
     (tamep-functionp identity-function)
     (tamep-functionp true-function)
     (fn-equal identity-function true-function))))

(defun putnam-1999-b2-two-roots-failure-function
    (carrier zero evaluate polynomial)
  (let* ((x1 'x1)
         (x2 'x2)
         (qualification
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-carrier-term carrier x1)
            (putnam-1999-b2-carrier-term carrier x2)
            (putnam-1999-b2-not-term
             (list 'equal x1 x2))
            (list
             'equal
             (putnam-1999-b2-operation-term
              evaluate
              (putnam-1999-b2-quoted polynomial)
              x1)
             (putnam-1999-b2-quoted zero))
            (list
             'equal
             (putnam-1999-b2-operation-term
              evaluate
              (putnam-1999-b2-quoted polynomial)
              x2)
             (putnam-1999-b2-quoted zero))))))
    (list
     'lambda
     '(x1 x2)
     (list
      'if
      qualification
      (putnam-1999-b2-quoted nil)
      (putnam-1999-b2-quoted t)))))

(defun putnam-1999-b2-two-roots-exist-p
    (carrier zero evaluate polynomial)
  (let ((failure-function
         (putnam-1999-b2-two-roots-failure-function
          carrier zero evaluate polynomial))
        (true-function
         (putnam-1999-b2-true-function '(x1 x2))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnam-1999-b2-all-roots-function
    (carrier zero evaluate polynomial)
  (let* ((root 'loop$-ivars)
         (qualification
          (putnam-1999-b2-and-term
           (list
            (putnam-1999-b2-carrier-term carrier root)
            (list
             'equal
             (putnam-1999-b2-operation-term
              evaluate
              (putnam-1999-b2-quoted polynomial)
              root)
             (putnam-1999-b2-quoted zero))))))
    (list
     'lambda
     '(loop$-gvars loop$-ivars)
     qualification)))

(defun putnam-1999-b2-all-roots-term
    (carrier zero evaluate polynomial roots)
  (list
   'always$+
   (putnam-1999-b2-quoted
    (putnam-1999-b2-all-roots-function
     carrier zero evaluate polynomial))
   (putnam-1999-b2-quoted nil)
   roots))

(defun putnam-1999-b2-root-list-failure-function
    (carrier zero evaluate polynomial degree)
  (let* ((roots 'roots)
         (qualification
          (putnam-1999-b2-and-term
           (list
            (list 'true-listp roots)
            (list
             'equal
             (list 'len roots)
             (putnam-1999-b2-quoted degree))
            (list 'no-duplicatesp-equal roots)
            (putnam-1999-b2-all-roots-term
             carrier zero evaluate polynomial roots)))))
    (list
     'lambda
     '(roots)
     (list
      'if
      qualification
      (putnam-1999-b2-quoted nil)
      (putnam-1999-b2-quoted t)))))

(defun putnam-1999-b2-degree-roots-exist-p
    (carrier zero evaluate polynomial degree)
  (let ((failure-function
         (putnam-1999-b2-root-list-failure-function
          carrier zero evaluate polynomial degree))
        (true-function
         (putnam-1999-b2-true-function '(roots))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-1999-b2-statement
    (carrier zero one add mul neg inv natural-embedding
             evaluate root-selector polynomial quadratic)
  (implies
   (and
    (putnam-1999-b2-algebraically-closed-field-p
     carrier zero one add mul neg inv natural-embedding
     evaluate root-selector)
    (putnam-1999-b2-polynomial-p
     polynomial carrier zero)
    (putnam-1999-b2-polynomial-p
     quadratic carrier zero)
    (equal (len quadratic) 3)
    (putnam-1999-b2-polynomial-identity-p
     carrier zero add mul evaluate polynomial quadratic))
   (implies
    (putnam-1999-b2-two-roots-exist-p
     carrier zero evaluate polynomial)
    (putnam-1999-b2-degree-roots-exist-p
     carrier zero evaluate polynomial
     (- (len polynomial) 1)))))

(value-triple :itpeval-statement-checked)
:q
