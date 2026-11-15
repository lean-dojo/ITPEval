;; Statement-only formalization of thousand-theorems corpus artifact Q1068976,
;; "Hilbert's Nullstellensatz": over a field embedded in an algebraically
;; closed field and finitely many variables, the vanishing ideal of an ideal's
;; zero locus equals its radical. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Variables are a duplicate-free finite list. Polynomials are canonical
;; sorted finite-support lists whose entries are (exponent-vector coefficient).
;; Field carriers, ideals, point sets, and polynomial families remain arbitrary
;; tame predicates and are not enumerated.
;;
;; ALGEBRAIC-PACKAGE, POLYNOMIAL-PACKAGE, and LOCUS-PACKAGE bundle operations
;; and classical choice components with both directions of their defining
;; laws. Forgetting the components gives exactly the source fields, polynomial
;; ring, ideal, zero locus, vanishing ideal, and radical; conversely classical
;; choice supplies every bundled component. Thus roots, counterexamples, and
;; radical powers remain internal witnesses rather than theorem parameters.
;;
;; Every function object supplied to FN-EQUAL contains only ACL2 primitives,
;; loop scions, and APPLY$ calls on quoted tame functions. The final diagnostic
;; checks every directly or transitively reified lambda.

(defun q1068976-quoted (object)
  (list 'quote object))

(defun q1068976-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q1068976-term-list (cdr terms)))
    (q1068976-quoted nil)))

(defun q1068976-static-apply-term (function arguments)
  (list 'apply$
        (q1068976-quoted function)
        (q1068976-term-list arguments)))

(defun q1068976-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q1068976-and-terms (cdr terms))
            (q1068976-quoted nil))
    (q1068976-quoted t)))

(defun q1068976-not-term (term)
  (list 'if term
        (q1068976-quoted nil)
        (q1068976-quoted t)))

(defun q1068976-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q1068976-quoted t)))

(defun q1068976-iff-term (left right)
  (list 'if left
        (list 'if right
              (q1068976-quoted t)
              (q1068976-quoted nil))
        (list 'if right
              (q1068976-quoted nil)
              (q1068976-quoted t))))

(defun q1068976-true-function (formals)
  (list 'lambda formals (q1068976-quoted t)))

(defun q1068976-universal-p (function formals)
  (let ((always-true (q1068976-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun q1068976-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q1068976-index-range-term (last)
  (list 'from-to-by
        (q1068976-quoted 0)
        last
        (q1068976-quoted 1)))

(defun q1068976-zero-vector (variables)
  (if (consp variables)
      (cons 0 (q1068976-zero-vector (cdr variables)))
    nil))

;; Fields and the embedding k -> K.

(defun q1068976-field-laws-function
    (carrier add multiply negate inverse zero one)
  (let* ((add-xy (q1068976-static-apply-term add '(x y)))
         (add-yz (q1068976-static-apply-term add '(y z)))
         (mul-xy (q1068976-static-apply-term multiply '(x y)))
         (mul-yz (q1068976-static-apply-term multiply '(y z)))
         (neg-x (q1068976-static-apply-term negate '(x)))
         (inv-x (q1068976-static-apply-term inverse '(x)))
         (domain
          (q1068976-and-terms
           (list (q1068976-static-apply-term carrier '(x))
                 (q1068976-static-apply-term carrier '(y))
                 (q1068976-static-apply-term carrier '(z))))))
    (list
     'lambda '(x y z)
     (q1068976-implies-term
      domain
      (q1068976-and-terms
       (list
        (q1068976-static-apply-term carrier (list add-xy))
        (q1068976-static-apply-term carrier (list mul-xy))
        (q1068976-static-apply-term carrier (list neg-x))
        (q1068976-implies-term
         (q1068976-not-term
          (list 'equal 'x (q1068976-quoted zero)))
         (q1068976-static-apply-term carrier (list inv-x)))
        (list 'equal
              (q1068976-static-apply-term add (list add-xy 'z))
              (q1068976-static-apply-term add (list 'x add-yz)))
        (list 'equal add-xy
              (q1068976-static-apply-term add '(y x)))
        (list 'equal
              (q1068976-static-apply-term
               add (list 'x (q1068976-quoted zero)))
              'x)
        (list 'equal
              (q1068976-static-apply-term add (list 'x neg-x))
              (q1068976-quoted zero))
        (list 'equal
              (q1068976-static-apply-term multiply (list mul-xy 'z))
              (q1068976-static-apply-term multiply (list 'x mul-yz)))
        (list 'equal mul-xy
              (q1068976-static-apply-term multiply '(y x)))
        (list 'equal
              (q1068976-static-apply-term
               multiply (list 'x (q1068976-quoted one)))
              'x)
        (q1068976-implies-term
         (q1068976-not-term
          (list 'equal 'x (q1068976-quoted zero)))
         (list 'equal
               (q1068976-static-apply-term multiply (list 'x inv-x))
               (q1068976-quoted one)))
        (list 'equal
              (q1068976-static-apply-term multiply (list 'x add-yz))
              (q1068976-static-apply-term
               add
               (list
                (q1068976-static-apply-term multiply '(x y))
                (q1068976-static-apply-term multiply '(x z)))))))))))

(defun q1068976-field-p
    (carrier add multiply negate inverse zero one)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (q1068976-member-p carrier zero)
   (q1068976-member-p carrier one)
   (not (equal zero one))
   (q1068976-universal-p
    (q1068976-field-laws-function
     carrier add multiply negate inverse zero one)
    '(x y z))))

(defun q1068976-embedding-laws-function
    (small-carrier large-carrier
     small-add small-multiply small-zero small-one
     large-add large-multiply large-zero large-one embedding)
  (let* ((map-x (q1068976-static-apply-term embedding '(x)))
         (map-y (q1068976-static-apply-term embedding '(y)))
         (domain
          (q1068976-and-terms
           (list
            (q1068976-static-apply-term small-carrier '(x))
            (q1068976-static-apply-term small-carrier '(y))))))
    (list
     'lambda '(x y)
     (q1068976-implies-term
      domain
      (q1068976-and-terms
       (list
        (q1068976-static-apply-term large-carrier (list map-x))
        (list 'equal
              (q1068976-static-apply-term
               embedding
               (list
                (q1068976-static-apply-term small-add '(x y))))
              (q1068976-static-apply-term
               large-add (list map-x map-y)))
        (list 'equal
              (q1068976-static-apply-term
               embedding
               (list
                (q1068976-static-apply-term small-multiply '(x y))))
              (q1068976-static-apply-term
               large-multiply (list map-x map-y)))
        (q1068976-implies-term
         (list 'equal map-x map-y)
         (list 'equal 'x 'y))
        (list 'equal
              (q1068976-static-apply-term
               embedding (list (q1068976-quoted small-zero)))
              (q1068976-quoted large-zero))
        (list 'equal
              (q1068976-static-apply-term
               embedding (list (q1068976-quoted small-one)))
              (q1068976-quoted large-one))))))))

(defun q1068976-field-embedding-p
    (small-carrier large-carrier
     small-add small-multiply small-zero small-one
     large-add large-multiply large-zero large-one embedding)
  (and
   (tamep-functionp embedding)
   (q1068976-universal-p
    (q1068976-embedding-laws-function
     small-carrier large-carrier
     small-add small-multiply small-zero small-one
     large-add large-multiply large-zero large-one embedding)
    '(x y))))

;; Canonical polynomial and point terms.

(defun q1068976-natural-function ()
  '(lambda (value) (natp value)))

(defun q1068976-exponent-valid-term (exponent variables)
  (q1068976-and-terms
   (list
    (list 'true-listp exponent)
    (list 'equal (list 'len exponent)
          (q1068976-quoted (len variables)))
    (list 'always$
          (q1068976-quoted (q1068976-natural-function))
          exponent))))

(defun q1068976-polynomial-entry-function
    (variables carrier zero)
  (let ((exponent (list 'car 'entry))
        (coefficient (list 'car (list 'cdr 'entry))))
    (list
     'lambda '(entry)
     (q1068976-and-terms
      (list
       (list 'true-listp 'entry)
       (list 'equal (list 'len 'entry) (q1068976-quoted 2))
       (q1068976-exponent-valid-term exponent variables)
       (q1068976-static-apply-term carrier (list coefficient))
       (q1068976-not-term
        (list 'equal coefficient (q1068976-quoted zero))))))))

(defun q1068976-polynomial-order-function ()
  (let* ((polynomial (list 'car 'loop$-gvars))
         (left
          (list 'car
                (list 'nth 'loop$-ivars polynomial)))
         (right
          (list 'car
                (list 'nth
                      (list 'binary-+ 'loop$-ivars
                            (q1068976-quoted 1))
                      polynomial))))
    (list
     'lambda '(loop$-gvars loop$-ivars)
     (q1068976-and-terms
      (list
       (list 'lexorder left right)
       (q1068976-not-term
        (list 'equal left right)))))))

(defun q1068976-polynomial-valid-term
    (polynomial variables carrier zero)
  (q1068976-and-terms
   (list
    (list 'true-listp polynomial)
    (list 'always$
          (q1068976-quoted
           (q1068976-polynomial-entry-function
            variables carrier zero))
          polynomial)
    (list
     'always$+
     (q1068976-quoted
      (q1068976-polynomial-order-function))
     (q1068976-term-list (list polynomial))
     (q1068976-index-range-term
      (list 'binary-+
            (list 'len polynomial)
            (q1068976-quoted -2)))))))

(defun q1068976-polynomial-valid-function
    (variables carrier zero)
  (list 'lambda '(polynomial)
        (q1068976-polynomial-valid-term
         'polynomial variables carrier zero)))

(defun q1068976-point-valid-term (point variables carrier)
  (q1068976-and-terms
   (list
    (list 'true-listp point)
    (list 'equal (list 'len point)
          (q1068976-quoted (len variables)))
    (list 'always$ (q1068976-quoted carrier) point))))

(defun q1068976-coefficient-term
    (polynomial exponent zero)
  (let ((entry (list 'assoc-equal exponent polynomial)))
    (list 'if entry
          (list 'car (list 'cdr entry))
          (q1068976-quoted zero))))

(defun q1068976-coordinate-le-function ()
  (let* ((shift (list 'car 'loop$-gvars))
         (target (list 'car (list 'cdr 'loop$-gvars)))
         (shift-coordinate
          (list 'nth 'loop$-ivars shift))
         (target-coordinate
          (list 'nth 'loop$-ivars target)))
    (list
     'lambda '(loop$-gvars loop$-ivars)
     (q1068976-not-term
      (list '< target-coordinate shift-coordinate)))))

(defun q1068976-coordinatewise-le-term (shift target)
  (list
   'always$+
   (q1068976-quoted
    (q1068976-coordinate-le-function))
   (q1068976-term-list (list shift target))
   (q1068976-index-range-term
    (list 'binary-+
          (list 'len target)
          (q1068976-quoted -1)))))

(defun q1068976-coordinate-difference-function ()
  (let* ((target (list 'car 'loop$-gvars))
         (shift (list 'car (list 'cdr 'loop$-gvars))))
    (list
     'lambda '(loop$-gvars loop$-ivars)
     (list 'binary-+
           (list 'nth 'loop$-ivars target)
           (list 'unary--
                 (list 'nth 'loop$-ivars shift))))))

(defun q1068976-coordinate-difference-term (target shift)
  (list
   'collect$+
   (q1068976-quoted
    (q1068976-coordinate-difference-function))
   (q1068976-term-list (list target shift))
   (q1068976-index-range-term
    (list 'binary-+
          (list 'len target)
          (q1068976-quoted -1)))))

(defun q1068976-unit-coordinate-function ()
  (let ((target-index (list 'car 'loop$-gvars)))
    (list
     'lambda '(loop$-gvars loop$-ivars)
     (list 'if
           (list 'equal 'loop$-ivars target-index)
           (q1068976-quoted 1)
           (q1068976-quoted 0)))))

(defun q1068976-variable-polynomial-term
    (index variables one)
  (let ((exponent
         (list
          'collect$+
          (q1068976-quoted
           (q1068976-unit-coordinate-function))
          (q1068976-term-list (list index))
          (q1068976-index-range-term
           (q1068976-quoted
            (- (len variables) 1))))))
    (list 'cons
          (q1068976-term-list
           (list exponent (q1068976-quoted one)))
          (q1068976-quoted nil))))

(defun q1068976-constant-polynomial-term
    (coefficient variables zero)
  (list
   'if
   (list 'equal coefficient (q1068976-quoted zero))
   (q1068976-quoted nil)
   (list
    'cons
    (q1068976-term-list
     (list
      (q1068976-quoted
       (q1068976-zero-vector variables))
      coefficient))
    (q1068976-quoted nil))))

;; Algebraic closedness, using a package-internal selected root and a Horner
;; trace. The trace is a finite certificate for evaluation at that root.

(defun q1068976-root-trace-step-function
    (add multiply)
  (let* ((coefficients (list 'car 'loop$-gvars))
         (root (list 'car (list 'cdr 'loop$-gvars)))
         (trace
          (list 'car
                (list 'cdr
                      (list 'cdr 'loop$-gvars))))
         (coefficient-index
          (list
           'binary-+
           (list 'binary-+
                 (list 'len coefficients)
                 (q1068976-quoted -1))
           (list 'unary-- 'loop$-ivars))))
    (list
     'lambda '(loop$-gvars loop$-ivars)
     (list
      'equal
      (list 'nth
            (list 'binary-+ 'loop$-ivars
                  (q1068976-quoted 1))
            trace)
      (q1068976-static-apply-term
       add
       (list
        (list 'nth coefficient-index coefficients)
        (q1068976-static-apply-term
         multiply
         (list root
               (list 'nth 'loop$-ivars trace)))))))))

(defun q1068976-algebraic-closure-function
    (carrier add multiply zero root-selector)
  (let* ((witness
          (q1068976-static-apply-term
           root-selector '(coefficients)))
         (root (list 'car witness))
         (trace (list 'car (list 'cdr witness)))
         (positive-degree
          (q1068976-and-terms
           (list
            (list 'true-listp 'coefficients)
            (q1068976-not-term
             (list '< (list 'len 'coefficients)
                   (q1068976-quoted 2)))
            (list 'always$
                  (q1068976-quoted carrier)
                  'coefficients)
            (q1068976-not-term
             (list
              'equal
              (list 'nth
                    (list 'binary-+
                          (list 'len 'coefficients)
                          (q1068976-quoted -1))
                    'coefficients)
              (q1068976-quoted zero))))))
         (trace-law
          (list
           'always$+
           (q1068976-quoted
            (q1068976-root-trace-step-function
             add multiply))
           (q1068976-term-list
            (list 'coefficients root trace))
           (q1068976-index-range-term
            (list 'binary-+
                  (list 'len 'coefficients)
                  (q1068976-quoted -1))))))
    (list
     'lambda '(coefficients)
     (q1068976-implies-term
      positive-degree
      (q1068976-and-terms
       (list
        (list 'true-listp witness)
        (list 'equal (list 'len witness)
              (q1068976-quoted 2))
        (q1068976-static-apply-term carrier (list root))
        (list 'true-listp trace)
        (list 'equal
              (list 'len trace)
              (list 'binary-+
                    (list 'len 'coefficients)
                    (q1068976-quoted 1)))
        (list 'equal
              (list 'nth (q1068976-quoted 0) trace)
              (q1068976-quoted zero))
        trace-law
        (list 'equal
              (list 'nth
                    (list 'len 'coefficients)
                    trace)
              (q1068976-quoted zero))))))))

(defun q1068976-algebraically-closed-p
    (carrier add multiply zero algebraic-package)
  (let ((root-selector (nth 0 algebraic-package)))
    (and
     (true-listp algebraic-package)
     (equal (len algebraic-package) 1)
     (tamep-functionp root-selector)
     (q1068976-universal-p
      (q1068976-algebraic-closure-function
       carrier add multiply zero root-selector)
      '(coefficients)))))

;; POLYNOMIAL-PACKAGE fields and exact operation laws.

(defun q1068976-polynomial-add (package) (nth 0 package))
(defun q1068976-polynomial-negate (package) (nth 1 package))
(defun q1068976-polynomial-scale (package) (nth 2 package))
(defun q1068976-polynomial-multiply (package) (nth 3 package))
(defun q1068976-polynomial-evaluate (package) (nth 4 package))

(defun q1068976-polynomial-add-law-function
    (variables carrier add zero polynomial-add)
  (let* ((sum
          (q1068976-static-apply-term
           polynomial-add '(p q)))
         (domain
          (q1068976-and-terms
           (list
            (q1068976-polynomial-valid-term
             'p variables carrier zero)
            (q1068976-polynomial-valid-term
             'q variables carrier zero)
            (q1068976-exponent-valid-term
             'exponent variables)))))
    (list
     'lambda '(p q exponent)
     (q1068976-implies-term
      domain
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         sum variables carrier zero)
        (list
         'equal
         (q1068976-coefficient-term
          sum 'exponent zero)
         (q1068976-static-apply-term
          add
          (list
           (q1068976-coefficient-term
            'p 'exponent zero)
           (q1068976-coefficient-term
            'q 'exponent zero))))))))))

(defun q1068976-polynomial-negate-law-function
    (variables carrier negate zero polynomial-negate)
  (let ((negative
         (q1068976-static-apply-term
          polynomial-negate '(p))))
    (list
     'lambda '(p exponent)
     (q1068976-implies-term
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         'p variables carrier zero)
        (q1068976-exponent-valid-term
         'exponent variables)))
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         negative variables carrier zero)
        (list
         'equal
         (q1068976-coefficient-term
          negative 'exponent zero)
         (q1068976-static-apply-term
          negate
          (list
           (q1068976-coefficient-term
            'p 'exponent zero))))))))))

(defun q1068976-polynomial-scale-law-function
    (variables carrier multiply zero polynomial-scale)
  (let* ((term-exponent (list 'car 'term))
         (term-coefficient
          (list 'car (list 'cdr 'term)))
         (scaled
          (q1068976-static-apply-term
           polynomial-scale '(term p)))
         (source-exponent
          (q1068976-coordinate-difference-term
           'exponent term-exponent))
         (expected
          (list
           'if
           (q1068976-coordinatewise-le-term
            term-exponent 'exponent)
           (q1068976-static-apply-term
            multiply
            (list
             term-coefficient
             (q1068976-coefficient-term
              'p source-exponent zero)))
           (q1068976-quoted zero))))
    (list
     'lambda '(term p exponent)
     (q1068976-implies-term
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         (list 'cons 'term (q1068976-quoted nil))
         variables carrier zero)
        (q1068976-polynomial-valid-term
         'p variables carrier zero)
        (q1068976-exponent-valid-term
         'exponent variables)))
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         scaled variables carrier zero)
        (list
         'equal
         (q1068976-coefficient-term
          scaled 'exponent zero)
         expected)))))))

(defun q1068976-polynomial-multiply-law-function
    (variables carrier zero
     polynomial-add polynomial-scale polynomial-multiply)
  (let ((product
         (q1068976-static-apply-term
          polynomial-multiply '(p q)))
        (recursive-product
         (list
          'if
          (list 'consp 'p)
          (q1068976-static-apply-term
           polynomial-add
           (list
            (q1068976-static-apply-term
             polynomial-scale
             (list (list 'car 'p) 'q))
            (q1068976-static-apply-term
             polynomial-multiply
             (list (list 'cdr 'p) 'q))))
          (q1068976-quoted nil))))
    (list
     'lambda '(p q)
     (q1068976-implies-term
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         'p variables carrier zero)
        (q1068976-polynomial-valid-term
         'q variables carrier zero)))
      (q1068976-and-terms
       (list
        (q1068976-polynomial-valid-term
         product variables carrier zero)
        (list 'equal product recursive-product)))))))

(defun q1068976-polynomial-evaluate-law-function
    (variables
     small-carrier small-zero small-one
     large-carrier embedding large-add large-multiply
     polynomial-add polynomial-multiply polynomial-evaluate)
  (let* ((eval-p
          (q1068976-static-apply-term
           polynomial-evaluate '(p point)))
         (eval-q
          (q1068976-static-apply-term
           polynomial-evaluate '(q point)))
         (valid-point
          (q1068976-point-valid-term
           'point variables large-carrier))
         (valid-p
          (q1068976-polynomial-valid-term
           'p variables small-carrier small-zero))
         (valid-q
          (q1068976-polynomial-valid-term
           'q variables small-carrier small-zero))
         (constant
          (q1068976-constant-polynomial-term
           'coefficient variables small-zero))
         (variable
          (q1068976-variable-polynomial-term
           'index variables small-one)))
    (list
     'lambda '(p q point coefficient index)
     (q1068976-and-terms
      (list
       (q1068976-implies-term
        (q1068976-and-terms (list valid-p valid-point))
        (q1068976-static-apply-term
         large-carrier (list eval-p)))
       (q1068976-implies-term
        (q1068976-and-terms
         (list valid-p valid-q valid-point))
        (q1068976-and-terms
         (list
          (list
           'equal
           (q1068976-static-apply-term
            polynomial-evaluate
            (list
             (q1068976-static-apply-term
              polynomial-add '(p q))
             'point))
           (q1068976-static-apply-term
            large-add (list eval-p eval-q)))
          (list
           'equal
           (q1068976-static-apply-term
            polynomial-evaluate
            (list
             (q1068976-static-apply-term
              polynomial-multiply '(p q))
             'point))
           (q1068976-static-apply-term
            large-multiply (list eval-p eval-q))))))
       (q1068976-implies-term
        (q1068976-and-terms
         (list
          (q1068976-static-apply-term
           small-carrier '(coefficient))
          valid-point))
        (list
         'equal
         (q1068976-static-apply-term
          polynomial-evaluate
          (list constant 'point))
         (q1068976-static-apply-term
          embedding '(coefficient))))
       (q1068976-implies-term
        (q1068976-and-terms
         (list
          (list 'natp 'index)
          (list '< 'index
                (q1068976-quoted (len variables)))
          valid-point))
        (list
         'equal
         (q1068976-static-apply-term
          polynomial-evaluate
          (list variable 'point))
         (list 'nth 'index 'point))))))))

(defun q1068976-polynomial-package-p
    (variables
     small-carrier small-add small-multiply small-negate
     small-zero small-one
     large-carrier embedding large-add large-multiply
     polynomial-package)
  (let* ((polynomial-add
          (q1068976-polynomial-add polynomial-package))
         (polynomial-negate
          (q1068976-polynomial-negate polynomial-package))
         (polynomial-scale
          (q1068976-polynomial-scale polynomial-package))
         (polynomial-multiply
          (q1068976-polynomial-multiply polynomial-package))
         (polynomial-evaluate
          (q1068976-polynomial-evaluate polynomial-package)))
    (and
     (true-listp polynomial-package)
     (equal (len polynomial-package) 5)
     (tamep-functionp polynomial-add)
     (tamep-functionp polynomial-negate)
     (tamep-functionp polynomial-scale)
     (tamep-functionp polynomial-multiply)
     (tamep-functionp polynomial-evaluate)
     (q1068976-universal-p
      (q1068976-polynomial-add-law-function
       variables small-carrier small-add small-zero
       polynomial-add)
      '(p q exponent))
     (q1068976-universal-p
      (q1068976-polynomial-negate-law-function
       variables small-carrier small-negate small-zero
       polynomial-negate)
      '(p exponent))
     (q1068976-universal-p
      (q1068976-polynomial-scale-law-function
       variables small-carrier small-multiply small-zero
       polynomial-scale)
      '(term p exponent))
     (q1068976-universal-p
      (q1068976-polynomial-multiply-law-function
       variables small-carrier small-zero
       polynomial-add polynomial-scale polynomial-multiply)
      '(p q))
     (q1068976-universal-p
      (q1068976-polynomial-evaluate-law-function
       variables
       small-carrier small-zero small-one
       large-carrier embedding large-add large-multiply
       polynomial-add polynomial-multiply polynomial-evaluate)
      '(p q point coefficient index)))))

;; Ideals of the canonical polynomial ring.

(defun q1068976-ideal-law-function
    (variables carrier zero ideal
     polynomial-add polynomial-negate polynomial-multiply)
  (let ((p-in (q1068976-static-apply-term ideal '(p)))
        (q-in (q1068976-static-apply-term ideal '(q)))
        (p-valid
         (q1068976-polynomial-valid-term
          'p variables carrier zero)))
    (list
     'lambda '(p q)
     (q1068976-and-terms
      (list
       (q1068976-implies-term p-in p-valid)
       (q1068976-implies-term
        (q1068976-and-terms (list p-in q-in))
        (q1068976-static-apply-term
         ideal
         (list
          (q1068976-static-apply-term
           polynomial-add '(p q)))))
       (q1068976-implies-term
        p-in
        (q1068976-static-apply-term
         ideal
         (list
          (q1068976-static-apply-term
           polynomial-negate '(p)))))
       (q1068976-implies-term
        (q1068976-and-terms (list p-valid q-in))
        (q1068976-static-apply-term
         ideal
         (list
          (q1068976-static-apply-term
           polynomial-multiply '(p q))))))))))

(defun q1068976-ideal-p
    (variables carrier zero ideal polynomial-package)
  (and
   (tamep-functionp ideal)
   (q1068976-member-p ideal nil)
   (q1068976-universal-p
    (q1068976-ideal-law-function
     variables carrier zero ideal
     (q1068976-polynomial-add polynomial-package)
     (q1068976-polynomial-negate polynomial-package)
     (q1068976-polynomial-multiply polynomial-package))
    '(p q))))

;; LOCUS-PACKAGE fields and exact definitions of zero locus, vanishing ideal,
;; and radical.

(defun q1068976-zero-locus (package) (nth 0 package))
(defun q1068976-zero-counterexample (package) (nth 1 package))
(defun q1068976-vanishing (package) (nth 2 package))
(defun q1068976-vanishing-counterexample (package) (nth 3 package))
(defun q1068976-radical (package) (nth 4 package))
(defun q1068976-radical-witness (package) (nth 5 package))

(defun q1068976-zero-locus-law-function
    (variables large-carrier large-zero ideal polynomial-evaluate
     zero-locus zero-counterexample)
  (let ((point-valid
         (q1068976-point-valid-term
          'point variables large-carrier))
        (point-zero
         (q1068976-static-apply-term
          zero-locus '(point)))
        (counterexample
         (q1068976-static-apply-term
          zero-counterexample '(point))))
    (list
     'lambda '(point polynomial)
     (q1068976-and-terms
      (list
       (q1068976-implies-term point-zero point-valid)
       (q1068976-implies-term
        (q1068976-and-terms
         (list
          point-valid
          point-zero
          (q1068976-static-apply-term
           ideal '(polynomial))))
        (list
         'equal
         (q1068976-static-apply-term
          polynomial-evaluate '(polynomial point))
         (q1068976-quoted large-zero)))
       (q1068976-implies-term
        (q1068976-and-terms
         (list point-valid
               (q1068976-not-term point-zero)))
        (q1068976-and-terms
         (list
          (q1068976-static-apply-term
           ideal (list counterexample))
          (q1068976-not-term
           (list
            'equal
            (q1068976-static-apply-term
             polynomial-evaluate
             (list counterexample 'point))
            (q1068976-quoted large-zero)))))))))))

(defun q1068976-vanishing-law-function
    (variables small-carrier small-zero
     large-carrier large-zero polynomial-evaluate
     zero-locus vanishing vanishing-counterexample)
  (let ((polynomial-valid
         (q1068976-polynomial-valid-term
          'polynomial variables small-carrier small-zero))
        (polynomial-vanishes
         (q1068976-static-apply-term
          vanishing '(polynomial)))
        (counterexample
         (q1068976-static-apply-term
          vanishing-counterexample '(polynomial))))
    (list
     'lambda '(polynomial point)
     (q1068976-and-terms
      (list
       (q1068976-implies-term
        polynomial-vanishes polynomial-valid)
       (q1068976-implies-term
        (q1068976-and-terms
         (list
          polynomial-valid
          polynomial-vanishes
          (q1068976-point-valid-term
           'point variables large-carrier)
          (q1068976-static-apply-term
           zero-locus '(point))))
        (list
         'equal
         (q1068976-static-apply-term
          polynomial-evaluate '(polynomial point))
         (q1068976-quoted large-zero)))
       (q1068976-implies-term
        (q1068976-and-terms
         (list
          polynomial-valid
          (q1068976-not-term polynomial-vanishes)))
        (q1068976-and-terms
         (list
          (q1068976-point-valid-term
           counterexample variables large-carrier)
          (q1068976-static-apply-term
           zero-locus (list counterexample))
          (q1068976-not-term
           (list
            'equal
            (q1068976-static-apply-term
             polynomial-evaluate
             (list 'polynomial counterexample))
            (q1068976-quoted large-zero)))))))))))

(defun q1068976-power-chain-step-function
    (polynomial-multiply)
  (let* ((polynomial (list 'car 'loop$-gvars))
         (chain (list 'car (list 'cdr 'loop$-gvars))))
    (list
     'lambda '(loop$-gvars loop$-ivars)
     (list
      'equal
      (list 'nth
            (list 'binary-+ 'loop$-ivars
                  (q1068976-quoted 1))
            chain)
      (q1068976-static-apply-term
       polynomial-multiply
       (list polynomial
             (list 'nth 'loop$-ivars chain)))))))

(defun q1068976-power-certificate-term
    (polynomial exponent chain
     variables carrier zero one
     ideal polynomial-multiply)
  (q1068976-and-terms
   (list
    (list 'natp exponent)
    (list 'true-listp chain)
    (list 'equal
          (list 'len chain)
          (list 'binary-+ exponent
                (q1068976-quoted 1)))
    (list 'always$
          (q1068976-quoted
           (q1068976-polynomial-valid-function
            variables carrier zero))
          chain)
    (list 'equal
          (list 'nth (q1068976-quoted 0) chain)
          (q1068976-quoted
           (list
            (list
             (q1068976-zero-vector variables)
             one))))
    (list
     'always$+
     (q1068976-quoted
      (q1068976-power-chain-step-function
       polynomial-multiply))
     (q1068976-term-list
      (list polynomial chain))
     (q1068976-index-range-term
      (list 'binary-+ exponent
            (q1068976-quoted -1))))
    (q1068976-static-apply-term
     ideal (list (list 'nth exponent chain))))))

(defun q1068976-radical-law-function
    (variables carrier zero one ideal polynomial-multiply
     radical radical-witness)
  (let* ((valid
          (q1068976-polynomial-valid-term
           'polynomial variables carrier zero))
         (in-radical
          (q1068976-static-apply-term
           radical '(polynomial)))
         (witness
          (q1068976-static-apply-term
           radical-witness '(polynomial)))
         (selected-exponent (list 'car witness))
         (selected-chain
          (list 'car (list 'cdr witness))))
    (list
     'lambda '(polynomial exponent chain)
     (q1068976-and-terms
      (list
       (q1068976-implies-term in-radical valid)
       (q1068976-implies-term
        (q1068976-and-terms (list valid in-radical))
        (q1068976-and-terms
         (list
          (list 'true-listp witness)
          (list 'equal (list 'len witness)
                (q1068976-quoted 2))
          (q1068976-power-certificate-term
           'polynomial selected-exponent selected-chain
           variables carrier zero one
           ideal polynomial-multiply))))
       (q1068976-implies-term
        (q1068976-and-terms
         (list
          valid
          (q1068976-power-certificate-term
           'polynomial 'exponent 'chain
           variables carrier zero one
           ideal polynomial-multiply)))
        in-radical))))))

(defun q1068976-locus-package-p
    (variables
     small-carrier small-zero small-one
     large-carrier large-zero
     ideal polynomial-package locus-package)
  (let* ((polynomial-evaluate
          (q1068976-polynomial-evaluate polynomial-package))
         (polynomial-multiply
          (q1068976-polynomial-multiply polynomial-package))
         (zero-locus
          (q1068976-zero-locus locus-package))
         (zero-counterexample
          (q1068976-zero-counterexample locus-package))
         (vanishing
          (q1068976-vanishing locus-package))
         (vanishing-counterexample
          (q1068976-vanishing-counterexample locus-package))
         (radical
          (q1068976-radical locus-package))
         (radical-witness
          (q1068976-radical-witness locus-package)))
    (and
     (true-listp locus-package)
     (equal (len locus-package) 6)
     (tamep-functionp zero-locus)
     (tamep-functionp zero-counterexample)
     (tamep-functionp vanishing)
     (tamep-functionp vanishing-counterexample)
     (tamep-functionp radical)
     (tamep-functionp radical-witness)
     (q1068976-universal-p
      (q1068976-zero-locus-law-function
       variables large-carrier large-zero
       ideal polynomial-evaluate
       zero-locus zero-counterexample)
      '(point polynomial))
     (q1068976-universal-p
      (q1068976-vanishing-law-function
       variables small-carrier small-zero
       large-carrier large-zero polynomial-evaluate
       zero-locus vanishing vanishing-counterexample)
      '(polynomial point))
     (q1068976-universal-p
      (q1068976-radical-law-function
       variables small-carrier small-zero small-one
       ideal polynomial-multiply radical radical-witness)
      '(polynomial exponent chain)))))

(defun q1068976-nullstellensatz-function
    (variables carrier zero vanishing radical)
  (list
   'lambda '(polynomial)
   (q1068976-implies-term
    (q1068976-polynomial-valid-term
     'polynomial variables carrier zero)
    (q1068976-iff-term
     (q1068976-static-apply-term
      vanishing '(polynomial))
     (q1068976-static-apply-term
      radical '(polynomial))))))

(defun thousand-theorems-q1068976-hilbert-nullstellensatz-statement
    (variables
     small-carrier small-add small-multiply small-negate small-inverse
     small-zero small-one
     large-carrier large-add large-multiply large-negate large-inverse
     large-zero large-one
     embedding algebraic-package polynomial-package ideal locus-package)
  (implies
   (and
    (true-listp variables)
    (no-duplicatesp-equal variables)
    (q1068976-field-p
     small-carrier small-add small-multiply
     small-negate small-inverse small-zero small-one)
    (q1068976-field-p
     large-carrier large-add large-multiply
     large-negate large-inverse large-zero large-one)
    (q1068976-field-embedding-p
     small-carrier large-carrier
     small-add small-multiply small-zero small-one
     large-add large-multiply large-zero large-one embedding)
    (q1068976-algebraically-closed-p
     large-carrier large-add large-multiply large-zero
     algebraic-package)
    (q1068976-polynomial-package-p
     variables
     small-carrier small-add small-multiply small-negate
     small-zero small-one
     large-carrier embedding large-add large-multiply
     polynomial-package)
    (q1068976-ideal-p
     variables small-carrier small-zero ideal polynomial-package)
    (q1068976-locus-package-p
     variables
     small-carrier small-zero small-one
     large-carrier large-zero
     ideal polynomial-package locus-package))
   (q1068976-universal-p
    (q1068976-nullstellensatz-function
     variables small-carrier small-zero
     (q1068976-vanishing locus-package)
     (q1068976-radical locus-package))
    '(polynomial))))

;; Admission-time tameness audit. Failure aborts before the statement sentinel.

(defun q1068976-all-reified-functions-tame-p ()
  (let* ((unary '(lambda (x) (quote t)))
         (binary '(lambda (x y) x))
         (variables '(v0 v1))
         (polynomial-package
          (list binary unary binary binary binary))
         (locus-package
          (list unary unary unary unary unary unary)))
    (and
     (tamep-functionp
      (q1068976-true-function '(x)))
     (tamep-functionp
      (q1068976-field-laws-function
       unary binary binary unary unary 0 1))
     (tamep-functionp
      (q1068976-embedding-laws-function
       unary unary binary binary 0 1
       binary binary 0 1 unary))
     (tamep-functionp
      (q1068976-natural-function))
     (tamep-functionp
      (q1068976-polynomial-entry-function
       variables unary 0))
     (tamep-functionp
      (q1068976-polynomial-order-function))
     (tamep-functionp
      (q1068976-polynomial-valid-function
       variables unary 0))
     (tamep-functionp
      (q1068976-coordinate-le-function))
     (tamep-functionp
      (q1068976-coordinate-difference-function))
     (tamep-functionp
      (q1068976-unit-coordinate-function))
     (tamep-functionp
      (q1068976-root-trace-step-function
       binary binary))
     (tamep-functionp
      (q1068976-algebraic-closure-function
       unary binary binary 0 unary))
     (tamep-functionp
      (q1068976-polynomial-add-law-function
       variables unary binary 0 binary))
     (tamep-functionp
      (q1068976-polynomial-negate-law-function
       variables unary unary 0 unary))
     (tamep-functionp
      (q1068976-polynomial-scale-law-function
       variables unary binary 0 binary))
     (tamep-functionp
      (q1068976-polynomial-multiply-law-function
       variables unary 0 binary binary binary))
     (tamep-functionp
      (q1068976-polynomial-evaluate-law-function
       variables unary 0 1 unary unary binary binary
       binary binary binary))
     (tamep-functionp
      (q1068976-ideal-law-function
       variables unary 0 unary binary unary binary))
     (tamep-functionp
      (q1068976-zero-locus-law-function
       variables unary 0 unary binary unary unary))
     (tamep-functionp
      (q1068976-vanishing-law-function
       variables unary 0 unary 0 binary unary unary unary))
     (tamep-functionp
      (q1068976-power-chain-step-function binary))
     (tamep-functionp
      (q1068976-radical-law-function
       variables unary 0 1 unary binary unary unary))
     (tamep-functionp
      (q1068976-nullstellensatz-function
       variables unary 0
       (q1068976-vanishing locus-package)
       (q1068976-radical locus-package)))
     (equal (len polynomial-package) 5))))

(value-triple
 (if (q1068976-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q1068976-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
