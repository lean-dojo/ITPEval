;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_b4:
;; pairs of real polynomials whose shifted determinant is identically one are
;; exactly the affine pairs with coefficient determinant one. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real coefficient domain is presented as a real closed ordered field.
;; The square-root and odd-degree-root laws are the standard algebraic
;; characterization of real closedness.  Polynomials are canonical nonempty
;; coefficient lists in ascending degree order.
;;
;; This is bidirectionally equivalent to the source statement: the reals form
;; such a field, while completeness of real closed fields transfers this
;; first-order polynomial assertion between any real closed field and the
;; reals. Canonical coefficient-list equality is polynomial equality because
;; every ordered field is infinite.
;;
;; ACL2 function objects supply the field operations and polynomial
;; evaluation. FN-EQUAL against a constant-T function expresses the source's
;; universal quantification over every real input without turning that input
;; into an external statement parameter. The solution predicate reads the
;; constant and linear coefficients of the canonical lists, so degree at most
;; one and the determinant equation are represented directly.

(defun putnam-2010-b4-quoted (object)
  (list 'quote object))

(defun putnam-2010-b4-apply1-term (function argument)
  (list
   'apply$
   (putnam-2010-b4-quoted function)
   (list 'cons argument nil)))

(defun putnam-2010-b4-apply2-term (function left right)
  (list
   'apply$
   (putnam-2010-b4-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2010-b4-and-term (terms)
  (if (endp terms)
      (putnam-2010-b4-quoted t)
    (list
     'if
     (car terms)
     (putnam-2010-b4-and-term (cdr terms))
     (putnam-2010-b4-quoted nil))))

(defun putnam-2010-b4-or-term (terms)
  (if (endp terms)
      (putnam-2010-b4-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2010-b4-quoted t)
     (putnam-2010-b4-or-term (cdr terms)))))

(defun putnam-2010-b4-not-term (term)
  (list
   'if
   term
   (putnam-2010-b4-quoted nil)
   (putnam-2010-b4-quoted t)))

(defun putnam-2010-b4-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2010-b4-quoted t)))

(defun putnam-2010-b4-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2010-b4-quoted t)))

(defun putnam-2010-b4-carrier-term (carrier element)
  (putnam-2010-b4-apply1-term carrier element))

(defun putnam-2010-b4-operation-term (operation left right)
  (putnam-2010-b4-apply2-term operation left right))

(defun putnam-2010-b4-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2010-b4-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2010-b4-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2010-b4-quoted
    (putnam-2010-b4-all-coefficients-function
     carrier))
   (putnam-2010-b4-quoted nil)
   coefficients))

(defun putnam-2010-b4-polynomial-term
    (carrier zero coefficients)
  (putnam-2010-b4-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2010-b4-all-coefficients-term
     carrier coefficients)
    (putnam-2010-b4-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2010-b4-quoted 1))
      (putnam-2010-b4-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2010-b4-quoted zero))))))))

(defun putnam-2010-b4-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2010-b4-quoted zero))
         (qone (putnam-2010-b4-quoted one))
         (add-xy
          (putnam-2010-b4-operation-term add x y))
         (add-yz
          (putnam-2010-b4-operation-term add y z))
         (mul-xy
          (putnam-2010-b4-operation-term mul x y))
         (mul-yz
          (putnam-2010-b4-operation-term mul y z))
         (neg-x
          (putnam-2010-b4-apply1-term neg x))
         (inv-x
          (putnam-2010-b4-apply1-term inv x))
         (domain
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term carrier x)
            (putnam-2010-b4-carrier-term carrier y)
            (putnam-2010-b4-carrier-term carrier z))))
         (laws
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term carrier add-xy)
            (putnam-2010-b4-carrier-term carrier mul-xy)
            (putnam-2010-b4-carrier-term carrier neg-x)
            (putnam-2010-b4-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2010-b4-operation-term add add-xy z)
             (putnam-2010-b4-operation-term add x add-yz))
            (list
             'equal
             (putnam-2010-b4-operation-term mul mul-xy z)
             (putnam-2010-b4-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2010-b4-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2010-b4-operation-term mul y x))
            (list
             'equal
             (putnam-2010-b4-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2010-b4-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2010-b4-operation-term mul x qone)
             x)
            (putnam-2010-b4-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2010-b4-implies-term
             (putnam-2010-b4-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2010-b4-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2010-b4-operation-term mul x add-yz)
             (putnam-2010-b4-operation-term
              add
              (putnam-2010-b4-operation-term mul x y)
              (putnam-2010-b4-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2010-b4-implies-term domain laws))))

(defun putnam-2010-b4-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2010-b4-quoted zero))
         (lt-xy
          (putnam-2010-b4-operation-term lt x y))
         (lt-yx
          (putnam-2010-b4-operation-term lt y x))
         (lt-yz
          (putnam-2010-b4-operation-term lt y z))
         (lt-xz
          (putnam-2010-b4-operation-term lt x z))
         (domain
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term carrier x)
            (putnam-2010-b4-carrier-term carrier y)
            (putnam-2010-b4-carrier-term carrier z))))
         (laws
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-not-term
             (putnam-2010-b4-operation-term lt x x))
            (putnam-2010-b4-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2010-b4-implies-term
             (putnam-2010-b4-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2010-b4-implies-term
             lt-xy
             (putnam-2010-b4-operation-term
              lt
              (putnam-2010-b4-operation-term add x z)
              (putnam-2010-b4-operation-term add y z)))
            (putnam-2010-b4-implies-term
             (putnam-2010-b4-and-term
              (list
               (putnam-2010-b4-operation-term lt qzero x)
               (putnam-2010-b4-operation-term lt qzero y)))
             (putnam-2010-b4-operation-term
              lt
              qzero
              (putnam-2010-b4-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2010-b4-implies-term domain laws))))

(defun putnam-2010-b4-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2010-b4-quoted zero))
         (root
          (putnam-2010-b4-apply1-term square-root x))
         (domain
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term carrier x)
            (putnam-2010-b4-not-term
             (putnam-2010-b4-operation-term lt x qzero)))))
         (laws
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term carrier root)
            (list
             'equal
             (putnam-2010-b4-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2010-b4-implies-term domain laws))))

(defun putnam-2010-b4-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2010-b4-quoted zero))
         (domain
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2010-b4-all-coefficients-term
             carrier rest)
            (putnam-2010-b4-carrier-term carrier x))))
         (empty-law
          (putnam-2010-b4-implies-term
           (putnam-2010-b4-carrier-term carrier x)
           (list
            'equal
            (putnam-2010-b4-operation-term
             evaluate
             (putnam-2010-b4-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2010-b4-operation-term
           add
           coefficient
           (putnam-2010-b4-operation-term
            mul
            x
            (putnam-2010-b4-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2010-b4-implies-term
           domain
           (putnam-2010-b4-and-term
            (list
             (putnam-2010-b4-carrier-term
              carrier
              (putnam-2010-b4-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2010-b4-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2010-b4-and-term
      (list empty-law recursive-law)))))

(defun putnam-2010-b4-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2010-b4-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2010-b4-and-term
           (list
            (putnam-2010-b4-carrier-term carrier root)
            (list
             'equal
             (putnam-2010-b4-operation-term
              evaluate coefficients root)
             (putnam-2010-b4-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2010-b4-implies-term domain laws))))

(defun putnam-2010-b4-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate)
  (let* ((field-laws
          (putnam-2010-b4-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2010-b4-true-function '(x y z)))
         (order-laws
          (putnam-2010-b4-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2010-b4-true-function '(x y z)))
         (square-root-laws
          (putnam-2010-b4-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2010-b4-true-function '(x)))
         (evaluation-laws
          (putnam-2010-b4-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2010-b4-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2010-b4-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2010-b4-true-function
           '(coefficients))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp mul)
     (tamep-functionp neg)
     (tamep-functionp inv)
     (tamep-functionp lt)
     (tamep-functionp square-root)
     (tamep-functionp odd-root)
     (tamep-functionp evaluate)
     (tamep-functionp field-laws)
     (tamep-functionp field-laws-true)
     (tamep-functionp order-laws)
     (tamep-functionp order-laws-true)
     (tamep-functionp square-root-laws)
     (tamep-functionp square-root-laws-true)
     (tamep-functionp evaluation-laws)
     (tamep-functionp evaluation-laws-true)
     (tamep-functionp odd-root-laws)
     (tamep-functionp odd-root-laws-true)
     (apply$ carrier (list zero))
     (apply$ carrier (list one))
     (not (equal zero one))
     (fn-equal field-laws field-laws-true)
     (fn-equal order-laws order-laws-true)
     (fn-equal square-root-laws square-root-laws-true)
     (fn-equal evaluation-laws evaluation-laws-true)
     (fn-equal odd-root-laws odd-root-laws-true))))

(defun putnam-2010-b4-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-2010-b4-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2010-b4-polynomial-p
    (polynomial carrier zero)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-2010-b4-coefficient-list-p
    polynomial carrier)
   (or
    (equal (len polynomial) 1)
    (not (equal (car (last polynomial)) zero)))))

(defun putnam-2010-b4-shifted-identity-function
    (carrier one add mul neg evaluate p q)
  (let* ((x 'x)
         (x-plus-one
          (putnam-2010-b4-operation-term
           add x (putnam-2010-b4-quoted one)))
         (p-x
          (putnam-2010-b4-operation-term
           evaluate (putnam-2010-b4-quoted p) x))
         (q-x
          (putnam-2010-b4-operation-term
           evaluate (putnam-2010-b4-quoted q) x))
         (p-shift
          (putnam-2010-b4-operation-term
           evaluate (putnam-2010-b4-quoted p) x-plus-one))
         (q-shift
          (putnam-2010-b4-operation-term
           evaluate (putnam-2010-b4-quoted q) x-plus-one))
         (determinant
          (putnam-2010-b4-operation-term
           add
           (putnam-2010-b4-operation-term mul p-x q-shift)
           (putnam-2010-b4-apply1-term
            neg
            (putnam-2010-b4-operation-term
             mul p-shift q-x)))))
    (list
     'lambda
     '(x)
     (putnam-2010-b4-implies-term
      (putnam-2010-b4-carrier-term carrier x)
      (list
       'equal
       determinant
       (putnam-2010-b4-quoted one))))))

(defun putnam-2010-b4-shifted-identity-p
    (carrier one add mul neg evaluate p q)
  (let ((identity
         (putnam-2010-b4-shifted-identity-function
          carrier one add mul neg evaluate p q))
        (true-function
         (putnam-2010-b4-true-function '(x))))
    (and
     (tamep-functionp identity)
     (tamep-functionp true-function)
     (fn-equal identity true-function))))

(defun putnam-2010-b4-coefficient
    (polynomial index zero)
  (if (< (nfix index) (len polynomial))
      (nth (nfix index) polynomial)
    zero))

(defun putnam-2010-b4-solution-p
    (zero one add mul neg p q)
  (and
   (<= (len p) 2)
   (<= (len q) 2)
   (equal
    (apply$
     add
     (list
      (apply$
       mul
       (list
        (putnam-2010-b4-coefficient p 0 zero)
        (putnam-2010-b4-coefficient q 1 zero)))
      (apply$
       neg
       (list
        (apply$
         mul
         (list
          (putnam-2010-b4-coefficient p 1 zero)
          (putnam-2010-b4-coefficient q 0 zero)))))))
    one)))

(defun putnambench-putnam-2010-b4-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate p q)
  (implies
   (and
    (putnam-2010-b4-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root
     evaluate)
    (putnam-2010-b4-polynomial-p
     p carrier zero)
    (putnam-2010-b4-polynomial-p
     q carrier zero))
   (iff
    (putnam-2010-b4-shifted-identity-p
     carrier one add mul neg evaluate p q)
    (putnam-2010-b4-solution-p
     zero one add mul neg p q))))

;; This evaluation checks every generated lambda family with concrete tame
;; function objects. It asserts no theorem and admits no proof or axiom.
(value-triple
 (if
  (and
   (tamep-functionp
    (putnam-2010-b4-all-coefficients-function
     '(lambda (x) (rationalp x))))
   (tamep-functionp
    (putnam-2010-b4-true-function '(x)))
   (tamep-functionp
    (putnam-2010-b4-true-function '(x y z)))
   (tamep-functionp
    (putnam-2010-b4-field-laws-function
     '(lambda (x) (rationalp x))
     0
     1
     'binary-+
     'binary-*
     'unary--
     'unary-/))
   (tamep-functionp
    (putnam-2010-b4-order-laws-function
     '(lambda (x) (rationalp x))
     0
     'binary-+
     'binary-*
     '<))
   (tamep-functionp
    (putnam-2010-b4-square-root-laws-function
     '(lambda (x) (rationalp x))
     0
     'binary-*
     '<
     '(lambda (x) '0)))
   (tamep-functionp
    (putnam-2010-b4-evaluation-laws-function
     '(lambda (x) (rationalp x))
     0
     'binary-+
     'binary-*
     '(lambda (coefficients x) '0)))
   (tamep-functionp
    (putnam-2010-b4-odd-root-laws-function
     '(lambda (x) (rationalp x))
     0
     '(lambda (coefficients x) '0)
     '(lambda (coefficients) '0)))
   (tamep-functionp
    (putnam-2010-b4-shifted-identity-function
     '(lambda (x) (rationalp x))
     1
     'binary-+
     'binary-*
     'unary--
     '(lambda (coefficients x) '0)
     '(0)
     '(0))))
  :itpeval-tame-functions-checked
  :itpeval-tame-functions-failed))

(value-triple :itpeval-statement-checked)
:q
