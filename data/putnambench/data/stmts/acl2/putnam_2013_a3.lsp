;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_a3:
;; a vanishing weighted sum of real coefficients at a point in the open unit
;; interval guarantees a root there for the corresponding polynomial. This
;; file contains no proof.

(in-package "ACL2")

;; The parameters below present an arbitrary real closed ordered field rather
;; than replacing the source real numbers by ACL2 rationals. Completeness of
;; real closed fields transfers this first-order assertion bidirectionally
;; between that presentation and the real numbers. FN-EQUAL supplies the
;; unbounded universal quantification used by the field laws.
;;
;; The coefficient list is exactly the restriction of the source family to
;; indices 0 through n; restriction and arbitrary extension outside this
;; range give the two directions of equivalence. Negated FN-EQUAL keeps the
;; required root y existentially quantified inside the statement predicate.

(defun putnam-2013-a3-quoted (object)
  (list 'quote object))

(defun putnam-2013-a3-apply1-term (function argument)
  (list
   'apply$
   (putnam-2013-a3-quoted function)
   (list 'cons argument nil)))

(defun putnam-2013-a3-apply2-term (function left right)
  (list
   'apply$
   (putnam-2013-a3-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2013-a3-and-term (terms)
  (if (endp terms)
      (putnam-2013-a3-quoted t)
    (list
     'if
     (car terms)
     (putnam-2013-a3-and-term (cdr terms))
     (putnam-2013-a3-quoted nil))))

(defun putnam-2013-a3-or-term (terms)
  (if (endp terms)
      (putnam-2013-a3-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2013-a3-quoted t)
     (putnam-2013-a3-or-term (cdr terms)))))

(defun putnam-2013-a3-not-term (term)
  (list
   'if
   term
   (putnam-2013-a3-quoted nil)
   (putnam-2013-a3-quoted t)))

(defun putnam-2013-a3-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2013-a3-quoted t)))

(defun putnam-2013-a3-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2013-a3-quoted t)))

(defun putnam-2013-a3-carrier-term (carrier element)
  (putnam-2013-a3-apply1-term carrier element))

(defun putnam-2013-a3-operation-term (operation left right)
  (putnam-2013-a3-apply2-term operation left right))

(defun putnam-2013-a3-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2013-a3-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2013-a3-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2013-a3-quoted
    (putnam-2013-a3-all-coefficients-function
     carrier))
   (putnam-2013-a3-quoted nil)
   coefficients))

(defun putnam-2013-a3-polynomial-term
    (carrier zero coefficients)
  (putnam-2013-a3-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2013-a3-all-coefficients-term
     carrier coefficients)
    (putnam-2013-a3-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2013-a3-quoted 1))
      (putnam-2013-a3-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2013-a3-quoted zero))))))))

(defun putnam-2013-a3-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2013-a3-quoted zero))
         (qone (putnam-2013-a3-quoted one))
         (add-xy
          (putnam-2013-a3-operation-term add x y))
         (add-yz
          (putnam-2013-a3-operation-term add y z))
         (mul-xy
          (putnam-2013-a3-operation-term mul x y))
         (mul-yz
          (putnam-2013-a3-operation-term mul y z))
         (neg-x
          (putnam-2013-a3-apply1-term neg x))
         (inv-x
          (putnam-2013-a3-apply1-term inv x))
         (domain
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier x)
            (putnam-2013-a3-carrier-term carrier y)
            (putnam-2013-a3-carrier-term carrier z))))
         (laws
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier add-xy)
            (putnam-2013-a3-carrier-term carrier mul-xy)
            (putnam-2013-a3-carrier-term carrier neg-x)
            (putnam-2013-a3-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2013-a3-operation-term add add-xy z)
             (putnam-2013-a3-operation-term add x add-yz))
            (list
             'equal
             (putnam-2013-a3-operation-term mul mul-xy z)
             (putnam-2013-a3-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2013-a3-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2013-a3-operation-term mul y x))
            (list
             'equal
             (putnam-2013-a3-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2013-a3-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2013-a3-operation-term mul x qone)
             x)
            (putnam-2013-a3-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2013-a3-implies-term
             (putnam-2013-a3-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2013-a3-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2013-a3-operation-term mul x add-yz)
             (putnam-2013-a3-operation-term
              add
              (putnam-2013-a3-operation-term mul x y)
              (putnam-2013-a3-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2013-a3-implies-term domain laws))))

(defun putnam-2013-a3-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2013-a3-quoted zero))
         (lt-xy
          (putnam-2013-a3-operation-term lt x y))
         (lt-yx
          (putnam-2013-a3-operation-term lt y x))
         (lt-yz
          (putnam-2013-a3-operation-term lt y z))
         (lt-xz
          (putnam-2013-a3-operation-term lt x z))
         (domain
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier x)
            (putnam-2013-a3-carrier-term carrier y)
            (putnam-2013-a3-carrier-term carrier z))))
         (laws
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-not-term
             (putnam-2013-a3-operation-term lt x x))
            (putnam-2013-a3-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2013-a3-implies-term
             (putnam-2013-a3-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2013-a3-implies-term
             lt-xy
             (putnam-2013-a3-operation-term
              lt
              (putnam-2013-a3-operation-term add x z)
              (putnam-2013-a3-operation-term add y z)))
            (putnam-2013-a3-implies-term
             (putnam-2013-a3-and-term
              (list
               (putnam-2013-a3-operation-term lt qzero x)
               (putnam-2013-a3-operation-term lt qzero y)))
             (putnam-2013-a3-operation-term
              lt
              qzero
              (putnam-2013-a3-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2013-a3-implies-term domain laws))))

(defun putnam-2013-a3-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2013-a3-quoted zero))
         (root
          (putnam-2013-a3-apply1-term square-root x))
         (domain
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier x)
            (putnam-2013-a3-not-term
             (putnam-2013-a3-operation-term lt x qzero)))))
         (laws
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier root)
            (list
             'equal
             (putnam-2013-a3-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2013-a3-implies-term domain laws))))

(defun putnam-2013-a3-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2013-a3-quoted zero))
         (domain
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2013-a3-all-coefficients-term
             carrier rest)
            (putnam-2013-a3-carrier-term carrier x))))
         (empty-law
          (putnam-2013-a3-implies-term
           (putnam-2013-a3-carrier-term carrier x)
           (list
            'equal
            (putnam-2013-a3-operation-term
             evaluate
             (putnam-2013-a3-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2013-a3-operation-term
           add
           coefficient
           (putnam-2013-a3-operation-term
            mul
            x
            (putnam-2013-a3-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2013-a3-implies-term
           domain
           (putnam-2013-a3-and-term
            (list
             (putnam-2013-a3-carrier-term
              carrier
              (putnam-2013-a3-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2013-a3-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2013-a3-and-term
      (list empty-law recursive-law)))))

(defun putnam-2013-a3-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2013-a3-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier root)
            (list
             'equal
             (putnam-2013-a3-operation-term
              evaluate coefficients root)
             (putnam-2013-a3-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2013-a3-implies-term domain laws))))

(defun putnam-2013-a3-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2013-a3-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2013-a3-true-function '(x y z)))
         (order-laws
          (putnam-2013-a3-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2013-a3-true-function '(x y z)))
         (square-root-laws
          (putnam-2013-a3-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2013-a3-true-function '(x)))
         (evaluation-laws
          (putnam-2013-a3-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2013-a3-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2013-a3-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2013-a3-true-function
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

(defun putnam-2013-a3-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2013-a3-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2013-a3-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2013-a3-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2013-a3-sub (add neg left right)
  (putnam-2013-a3-add
   add left (putnam-2013-a3-neg neg right)))

(defun putnam-2013-a3-power (mul one value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2013-a3-mul
     mul
     value
     (putnam-2013-a3-power
      mul one value (- exponent 1)))))

(defun putnam-2013-a3-less-p (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2013-a3-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-2013-a3-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2013-a3-weighted-sum
    (coefficients index zero one add mul neg inv x)
  (if (endp coefficients)
      zero
    (let* ((power
            (putnam-2013-a3-power
             mul one x (+ index 1)))
           (denominator
            (putnam-2013-a3-sub
             add neg one power))
           (term
            (putnam-2013-a3-mul
             mul
             (car coefficients)
             (putnam-2013-a3-inv
              inv denominator))))
      (putnam-2013-a3-add
       add
       term
       (putnam-2013-a3-weighted-sum
        (cdr coefficients)
        (+ index 1)
        zero one add mul neg inv x)))))

;; Build a tame term for a_0 + y*(a_1 + y*(... + y*a_n)).
(defun putnam-2013-a3-polynomial-value-term
    (coefficients zero add mul y)
  (if (endp coefficients)
      (putnam-2013-a3-quoted zero)
    (putnam-2013-a3-operation-term
     add
     (putnam-2013-a3-quoted (car coefficients))
     (putnam-2013-a3-operation-term
      mul
      y
      (putnam-2013-a3-polynomial-value-term
       (cdr coefficients) zero add mul y)))))

(defun putnam-2013-a3-root-failure-function
    (carrier zero one add mul lt coefficients)
  (let* ((y 'y)
         (qzero (putnam-2013-a3-quoted zero))
         (qone (putnam-2013-a3-quoted one))
         (value
          (putnam-2013-a3-polynomial-value-term
           coefficients zero add mul y))
         (qualification
          (putnam-2013-a3-and-term
           (list
            (putnam-2013-a3-carrier-term carrier y)
            (putnam-2013-a3-operation-term lt qzero y)
            (putnam-2013-a3-operation-term lt y qone)
            (list 'equal value qzero)))))
    (list
     'lambda
     '(y)
     (list
      'if
      qualification
      (putnam-2013-a3-quoted nil)
      (putnam-2013-a3-quoted t)))))

(defun putnam-2013-a3-root-exists-p
    (carrier zero one add mul lt coefficients)
  (let ((failure
         (putnam-2013-a3-root-failure-function
          carrier zero one add mul lt coefficients))
        (always-true
         (putnam-2013-a3-true-function '(y))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnambench-putnam-2013-a3-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate n coefficients x)
  (implies
   (and
    (putnam-2013-a3-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root evaluate)
    (natp n)
    (true-listp coefficients)
    (equal (len coefficients) (+ n 1))
    (putnam-2013-a3-coefficient-list-p
     coefficients carrier)
    (apply$ carrier (list x))
    (putnam-2013-a3-less-p lt zero x)
    (putnam-2013-a3-less-p lt x one)
    (equal
     (putnam-2013-a3-weighted-sum
      coefficients 0 zero one add mul neg inv x)
     zero))
   (putnam-2013-a3-root-exists-p
    carrier zero one add mul lt coefficients)))

(value-triple :itpeval-statement-checked)
:q
