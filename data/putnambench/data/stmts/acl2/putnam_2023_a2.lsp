;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_a2:
;; a monic real polynomial of degree 2n taking the value k^2 at 1/k for
;; 1 <= |k| <= n has exactly the two additional reciprocal roots
;; +/-1/(n!). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are represented in an arbitrary real-closed ordered field. Real
;; closed fields are elementarily equivalent, and the statement is
;; first-order in ordered-field operations. FN-EQUAL supplies the universal
;; quantifiers in the field laws and in the final pointwise set equality.

(defun putnam-2023-a2-quoted (object)
  (list 'quote object))

(defun putnam-2023-a2-apply1-term (function argument)
  (list
   'apply$
   (putnam-2023-a2-quoted function)
   (list 'cons argument nil)))

(defun putnam-2023-a2-apply2-term (function left right)
  (list
   'apply$
   (putnam-2023-a2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2023-a2-and-term (terms)
  (if (endp terms)
      (putnam-2023-a2-quoted t)
    (list
     'if
     (car terms)
     (putnam-2023-a2-and-term (cdr terms))
     (putnam-2023-a2-quoted nil))))

(defun putnam-2023-a2-or-term (terms)
  (if (endp terms)
      (putnam-2023-a2-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2023-a2-quoted t)
     (putnam-2023-a2-or-term (cdr terms)))))

(defun putnam-2023-a2-not-term (term)
  (list
   'if
   term
   (putnam-2023-a2-quoted nil)
   (putnam-2023-a2-quoted t)))

(defun putnam-2023-a2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2023-a2-quoted t)))

(defun putnam-2023-a2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2023-a2-quoted t)))

(defun putnam-2023-a2-carrier-term (carrier element)
  (putnam-2023-a2-apply1-term carrier element))

(defun putnam-2023-a2-operation-term (operation left right)
  (putnam-2023-a2-apply2-term operation left right))

(defun putnam-2023-a2-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2023-a2-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2023-a2-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2023-a2-quoted
    (putnam-2023-a2-all-coefficients-function
     carrier))
   (putnam-2023-a2-quoted nil)
   coefficients))

(defun putnam-2023-a2-polynomial-term
    (carrier zero coefficients)
  (putnam-2023-a2-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2023-a2-all-coefficients-term
     carrier coefficients)
    (putnam-2023-a2-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2023-a2-quoted 1))
      (putnam-2023-a2-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2023-a2-quoted zero))))))))

(defun putnam-2023-a2-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2023-a2-quoted zero))
         (qone (putnam-2023-a2-quoted one))
         (add-xy
          (putnam-2023-a2-operation-term add x y))
         (add-yz
          (putnam-2023-a2-operation-term add y z))
         (mul-xy
          (putnam-2023-a2-operation-term mul x y))
         (mul-yz
          (putnam-2023-a2-operation-term mul y z))
         (neg-x
          (putnam-2023-a2-apply1-term neg x))
         (inv-x
          (putnam-2023-a2-apply1-term inv x))
         (domain
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term carrier x)
            (putnam-2023-a2-carrier-term carrier y)
            (putnam-2023-a2-carrier-term carrier z))))
         (laws
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term carrier add-xy)
            (putnam-2023-a2-carrier-term carrier mul-xy)
            (putnam-2023-a2-carrier-term carrier neg-x)
            (putnam-2023-a2-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2023-a2-operation-term add add-xy z)
             (putnam-2023-a2-operation-term add x add-yz))
            (list
             'equal
             (putnam-2023-a2-operation-term mul mul-xy z)
             (putnam-2023-a2-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2023-a2-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2023-a2-operation-term mul y x))
            (list
             'equal
             (putnam-2023-a2-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2023-a2-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2023-a2-operation-term mul x qone)
             x)
            (putnam-2023-a2-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2023-a2-implies-term
             (putnam-2023-a2-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2023-a2-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2023-a2-operation-term mul x add-yz)
             (putnam-2023-a2-operation-term
              add
              (putnam-2023-a2-operation-term mul x y)
              (putnam-2023-a2-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2023-a2-implies-term domain laws))))

(defun putnam-2023-a2-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2023-a2-quoted zero))
         (lt-xy
          (putnam-2023-a2-operation-term lt x y))
         (lt-yx
          (putnam-2023-a2-operation-term lt y x))
         (lt-yz
          (putnam-2023-a2-operation-term lt y z))
         (lt-xz
          (putnam-2023-a2-operation-term lt x z))
         (domain
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term carrier x)
            (putnam-2023-a2-carrier-term carrier y)
            (putnam-2023-a2-carrier-term carrier z))))
         (laws
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-not-term
             (putnam-2023-a2-operation-term lt x x))
            (putnam-2023-a2-or-term
             (list
              lt-xy
              lt-yx
              (list 'equal x y)))
            (putnam-2023-a2-implies-term
             (putnam-2023-a2-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2023-a2-implies-term
             lt-xy
             (putnam-2023-a2-operation-term
              lt
              (putnam-2023-a2-operation-term add x z)
              (putnam-2023-a2-operation-term add y z)))
            (putnam-2023-a2-implies-term
             (putnam-2023-a2-and-term
              (list
               (putnam-2023-a2-operation-term lt qzero x)
               (putnam-2023-a2-operation-term lt qzero y)))
             (putnam-2023-a2-operation-term
              lt
              qzero
              (putnam-2023-a2-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2023-a2-implies-term domain laws))))

(defun putnam-2023-a2-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2023-a2-quoted zero))
         (root
          (putnam-2023-a2-apply1-term square-root x))
         (domain
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term carrier x)
            (putnam-2023-a2-not-term
             (putnam-2023-a2-operation-term lt x qzero)))))
         (laws
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term carrier root)
            (putnam-2023-a2-not-term
             (putnam-2023-a2-operation-term lt root qzero))
            (list
             'equal
             (putnam-2023-a2-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2023-a2-implies-term domain laws))))

(defun putnam-2023-a2-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2023-a2-quoted zero))
         (domain
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2023-a2-all-coefficients-term
             carrier rest)
            (putnam-2023-a2-carrier-term carrier x))))
         (empty-law
          (putnam-2023-a2-implies-term
           (putnam-2023-a2-carrier-term carrier x)
           (list
            'equal
            (putnam-2023-a2-operation-term
             evaluate
             (putnam-2023-a2-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2023-a2-operation-term
           add
           coefficient
           (putnam-2023-a2-operation-term
            mul
            x
            (putnam-2023-a2-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2023-a2-implies-term
           domain
           (putnam-2023-a2-and-term
            (list
             (putnam-2023-a2-carrier-term
              carrier
              (putnam-2023-a2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2023-a2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2023-a2-and-term
      (list empty-law recursive-law)))))

(defun putnam-2023-a2-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2023-a2-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2023-a2-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2023-a2-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2023-a2-field-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2023-a2-add
     add
     one
     (putnam-2023-a2-field-natural
      (- n 1) zero one add))))

(defun putnam-2023-a2-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-2023-a2-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2023-a2-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2023-a2-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-carrier-term carrier root)
            (list
             'equal
             (putnam-2023-a2-operation-term
              evaluate coefficients root)
             (putnam-2023-a2-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2023-a2-implies-term domain laws))))

(defun putnam-2023-a2-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2023-a2-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2023-a2-true-function '(x y z)))
         (order-laws
          (putnam-2023-a2-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2023-a2-true-function '(x y z)))
         (square-root-laws
          (putnam-2023-a2-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2023-a2-true-function '(x)))
         (evaluation-laws
          (putnam-2023-a2-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2023-a2-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2023-a2-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2023-a2-true-function '(coefficients)))
         (all-coefficients-loop
          (putnam-2023-a2-all-coefficients-function
           carrier)))
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
     (tamep-functionp all-coefficients-loop)
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

(defun putnam-2023-a2-monic-degree-p
    (coefficients n carrier one)
  (and
   (true-listp coefficients)
   (equal (len coefficients) (+ (* 2 n) 1))
   (putnam-2023-a2-coefficient-list-p
    coefficients carrier)
   (equal (car (last coefficients)) one)))

(defun putnam-2023-a2-interpolation-p
    (count coefficients zero one add mul neg inv evaluate)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let* ((positive
            (putnam-2023-a2-field-natural
             count zero one add))
           (negative
            (putnam-2023-a2-neg neg positive))
           (positive-square
            (putnam-2023-a2-mul mul positive positive))
           (negative-square
            (putnam-2023-a2-mul mul negative negative)))
      (and
       (equal
        (apply$
         evaluate
         (list
          coefficients
          (putnam-2023-a2-inv inv positive)))
        positive-square)
       (equal
        (apply$
         evaluate
         (list
          coefficients
          (putnam-2023-a2-inv inv negative)))
        negative-square)
       (putnam-2023-a2-interpolation-p
        (- count 1)
        coefficients zero one add mul neg inv evaluate)))))

(defun putnam-2023-a2-source-set-term
    (x count zero one add neg)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-2023-a2-quoted nil)
    (let* ((positive
            (putnam-2023-a2-field-natural
             count zero one add))
           (negative
            (putnam-2023-a2-neg neg positive)))
      (putnam-2023-a2-or-term
       (list
        (list
         'equal x
         (putnam-2023-a2-quoted positive))
        (list
         'equal x
         (putnam-2023-a2-quoted negative))
        (putnam-2023-a2-source-set-term
         x (- count 1) zero one add neg))))))

(defun putnam-2023-a2-field-factorial
    (n zero one add mul)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (putnam-2023-a2-mul
     mul
     (putnam-2023-a2-field-natural
      n zero one add)
     (putnam-2023-a2-field-factorial
      (- n 1) zero one add mul))))

(defun putnam-2023-a2-root-function
    (n coefficients carrier zero one add mul neg inv evaluate)
  (let* ((x 'x)
         (qzero
          (putnam-2023-a2-quoted zero))
         (reciprocal
          (putnam-2023-a2-apply1-term inv x))
         (polynomial-value
          (putnam-2023-a2-operation-term
           evaluate
           (putnam-2023-a2-quoted coefficients)
           reciprocal))
         (square
          (putnam-2023-a2-operation-term mul x x))
         (root-condition
          (putnam-2023-a2-and-term
           (list
            (putnam-2023-a2-not-term
             (list 'equal x qzero))
            (list 'equal polynomial-value square)
            (putnam-2023-a2-not-term
             (putnam-2023-a2-source-set-term
              x n zero one add neg)))))
         (factorial
          (putnam-2023-a2-field-factorial
           n zero one add mul))
         (positive-solution
          (putnam-2023-a2-inv inv factorial))
         (negative-solution
          (putnam-2023-a2-neg neg positive-solution))
         (solution-condition
          (putnam-2023-a2-or-term
           (list
            (list
             'equal x
             (putnam-2023-a2-quoted positive-solution))
            (list
             'equal x
             (putnam-2023-a2-quoted negative-solution)))))
         (equivalence
          (list 'equal root-condition solution-condition)))
    (list
     'lambda
     '(x)
     (putnam-2023-a2-implies-term
      (putnam-2023-a2-carrier-term carrier x)
      equivalence))))

(defun putnam-2023-a2-root-characterization-p
    (n coefficients carrier zero one add mul neg inv evaluate)
  (let ((condition
         (putnam-2023-a2-root-function
          n coefficients carrier zero one add mul neg inv evaluate))
        (always-true
         (putnam-2023-a2-true-function '(x))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnambench-putnam-2023-a2-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate n coefficients)
  (implies
   (and
    (putnam-2023-a2-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate)
    (natp n)
    (< 0 n)
    (evenp n)
    (putnam-2023-a2-monic-degree-p
     coefficients n carrier one)
    (putnam-2023-a2-interpolation-p
     n coefficients zero one add mul neg inv evaluate))
   (putnam-2023-a2-root-characterization-p
    n coefficients carrier zero one add mul neg inv evaluate)))

(value-triple :itpeval-statement-checked)
:q
