;; Statement-only formalization of PutnamBench corpus artifact putnam_1999_a2:
;; every real polynomial that is nonnegative on the real line is a finite sum
;; of squares of real polynomials. This file contains no proof.

(in-package "ACL2")

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
;; ACL2 function objects supply the field operations and the canonical
;; polynomial operations.  FN-EQUAL against a constant-T function expresses
;; universal quantification over the whole represented field.  The concluding
;; NOT/FN-EQUAL is an internal existential quantifier over a nonempty finite
;; list of polynomial coefficient lists; no decomposition is a parameter of
;; the statement predicate. Such lists are equivalent to finite indexed
;; families; an empty sum for the zero polynomial is replaced by the one-term
;; family containing the zero polynomial.

(defun putnam-1999-a2-quoted (object)
  (list 'quote object))

(defun putnam-1999-a2-apply1-term (function argument)
  (list
   'apply$
   (putnam-1999-a2-quoted function)
   (list 'cons argument nil)))

(defun putnam-1999-a2-apply2-term (function left right)
  (list
   'apply$
   (putnam-1999-a2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-1999-a2-and-term (terms)
  (if (endp terms)
      (putnam-1999-a2-quoted t)
    (list
     'if
     (car terms)
     (putnam-1999-a2-and-term (cdr terms))
     (putnam-1999-a2-quoted nil))))

(defun putnam-1999-a2-or-term (terms)
  (if (endp terms)
      (putnam-1999-a2-quoted nil)
    (list
     'if
     (car terms)
     (putnam-1999-a2-quoted t)
     (putnam-1999-a2-or-term (cdr terms)))))

(defun putnam-1999-a2-not-term (term)
  (list
   'if
   term
   (putnam-1999-a2-quoted nil)
   (putnam-1999-a2-quoted t)))

(defun putnam-1999-a2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-1999-a2-quoted t)))

(defun putnam-1999-a2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-1999-a2-quoted t)))

(defun putnam-1999-a2-carrier-term (carrier element)
  (putnam-1999-a2-apply1-term carrier element))

(defun putnam-1999-a2-operation-term (operation left right)
  (putnam-1999-a2-apply2-term operation left right))

(defun putnam-1999-a2-all-coefficients-function ()
  '(lambda (loop$-gvars loop$-ivars)
     (apply$ (car loop$-gvars)
             (cons loop$-ivars 'nil))))

(defun putnam-1999-a2-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-1999-a2-quoted
    (putnam-1999-a2-all-coefficients-function))
   (list 'cons
         (putnam-1999-a2-quoted carrier)
         nil)
   coefficients))

(defun putnam-1999-a2-polynomial-term
    (carrier zero coefficients)
  (putnam-1999-a2-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-1999-a2-all-coefficients-term
     carrier coefficients)
    (putnam-1999-a2-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-1999-a2-quoted 1))
      (putnam-1999-a2-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-1999-a2-quoted zero))))))))

(defun putnam-1999-a2-all-polynomials-function
    (carrier zero)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-1999-a2-polynomial-term
    carrier zero 'loop$-ivars)))

(defun putnam-1999-a2-all-polynomials-term
    (carrier zero polynomials)
  (list
   'always$+
   (putnam-1999-a2-quoted
    (putnam-1999-a2-all-polynomials-function
     carrier zero))
   (putnam-1999-a2-quoted nil)
   polynomials))

(defun putnam-1999-a2-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-1999-a2-quoted zero))
         (qone (putnam-1999-a2-quoted one))
         (add-xy
          (putnam-1999-a2-operation-term add x y))
         (add-yz
          (putnam-1999-a2-operation-term add y z))
         (mul-xy
          (putnam-1999-a2-operation-term mul x y))
         (mul-yz
          (putnam-1999-a2-operation-term mul y z))
         (neg-x
          (putnam-1999-a2-apply1-term neg x))
         (inv-x
          (putnam-1999-a2-apply1-term inv x))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term carrier x)
            (putnam-1999-a2-carrier-term carrier y)
            (putnam-1999-a2-carrier-term carrier z))))
         (laws
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term carrier add-xy)
            (putnam-1999-a2-carrier-term carrier mul-xy)
            (putnam-1999-a2-carrier-term carrier neg-x)
            (putnam-1999-a2-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-1999-a2-operation-term add add-xy z)
             (putnam-1999-a2-operation-term add x add-yz))
            (list
             'equal
             (putnam-1999-a2-operation-term mul mul-xy z)
             (putnam-1999-a2-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-1999-a2-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-1999-a2-operation-term mul y x))
            (list
             'equal
             (putnam-1999-a2-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-1999-a2-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-1999-a2-operation-term mul x qone)
             x)
            (putnam-1999-a2-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-1999-a2-implies-term
             (putnam-1999-a2-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-1999-a2-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-1999-a2-operation-term mul x add-yz)
             (putnam-1999-a2-operation-term
              add
              (putnam-1999-a2-operation-term mul x y)
              (putnam-1999-a2-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-1999-a2-implies-term domain laws))))

(defun putnam-1999-a2-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-1999-a2-quoted zero))
         (lt-xy
          (putnam-1999-a2-operation-term lt x y))
         (lt-yx
          (putnam-1999-a2-operation-term lt y x))
         (lt-yz
          (putnam-1999-a2-operation-term lt y z))
         (lt-xz
          (putnam-1999-a2-operation-term lt x z))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term carrier x)
            (putnam-1999-a2-carrier-term carrier y)
            (putnam-1999-a2-carrier-term carrier z))))
         (laws
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-not-term
             (putnam-1999-a2-operation-term lt x x))
            (putnam-1999-a2-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-1999-a2-implies-term
             (putnam-1999-a2-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-1999-a2-implies-term
             lt-xy
             (putnam-1999-a2-operation-term
              lt
              (putnam-1999-a2-operation-term add x z)
              (putnam-1999-a2-operation-term add y z)))
            (putnam-1999-a2-implies-term
             (putnam-1999-a2-and-term
              (list
               (putnam-1999-a2-operation-term lt qzero x)
               (putnam-1999-a2-operation-term lt qzero y)))
             (putnam-1999-a2-operation-term
              lt
              qzero
              (putnam-1999-a2-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-1999-a2-implies-term domain laws))))

(defun putnam-1999-a2-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-1999-a2-quoted zero))
         (root
          (putnam-1999-a2-apply1-term square-root x))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term carrier x)
            (putnam-1999-a2-not-term
             (putnam-1999-a2-operation-term lt x qzero)))))
         (laws
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term carrier root)
            (list
             'equal
             (putnam-1999-a2-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-1999-a2-implies-term domain laws))))

(defun putnam-1999-a2-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-1999-a2-quoted zero))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-1999-a2-all-coefficients-term
             carrier rest)
            (putnam-1999-a2-carrier-term carrier x))))
         (empty-law
          (putnam-1999-a2-implies-term
           (putnam-1999-a2-carrier-term carrier x)
           (list
            'equal
            (putnam-1999-a2-operation-term
             evaluate
             (putnam-1999-a2-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-1999-a2-operation-term
           add
           coefficient
           (putnam-1999-a2-operation-term
            mul
            x
            (putnam-1999-a2-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-1999-a2-implies-term
           domain
           (putnam-1999-a2-and-term
            (list
             (putnam-1999-a2-carrier-term
              carrier
              (putnam-1999-a2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-1999-a2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-1999-a2-and-term
      (list empty-law recursive-law)))))

(defun putnam-1999-a2-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-1999-a2-apply1-term
           odd-root coefficients))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-carrier-term carrier root)
            (list
             'equal
             (putnam-1999-a2-operation-term
              evaluate coefficients root)
             (putnam-1999-a2-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-1999-a2-implies-term domain laws))))

(defun putnam-1999-a2-polynomial-operation-laws-function
    (carrier zero add mul evaluate poly-add poly-mul)
  (let* ((left 'left)
         (right 'right)
         (x 'x)
         (sum
          (putnam-1999-a2-operation-term
           poly-add left right))
         (product
          (putnam-1999-a2-operation-term
           poly-mul left right))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-polynomial-term
             carrier zero left)
            (putnam-1999-a2-polynomial-term
             carrier zero right)
            (putnam-1999-a2-carrier-term carrier x))))
         (laws
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-polynomial-term
             carrier zero sum)
            (putnam-1999-a2-polynomial-term
             carrier zero product)
            (list
             'equal
             (putnam-1999-a2-operation-term
              evaluate sum x)
             (putnam-1999-a2-operation-term
              add
              (putnam-1999-a2-operation-term
               evaluate left x)
              (putnam-1999-a2-operation-term
               evaluate right x)))
            (list
             'equal
             (putnam-1999-a2-operation-term
              evaluate product x)
             (putnam-1999-a2-operation-term
              mul
              (putnam-1999-a2-operation-term
               evaluate left x)
              (putnam-1999-a2-operation-term
               evaluate right x)))))))
    (list
     'lambda
     '(left right x)
     (putnam-1999-a2-implies-term domain laws))))

(defun putnam-1999-a2-sum-of-squares-laws-function
    (carrier zero poly-add poly-mul sum-of-squares)
  (let* ((polynomial 'polynomial)
         (rest 'rest)
         (qzero-polynomial
          (putnam-1999-a2-quoted (list zero)))
         (rest-valid
          (putnam-1999-a2-and-term
           (list
            (list 'true-listp rest)
            (putnam-1999-a2-all-polynomials-term
             carrier zero rest))))
         (domain
          (putnam-1999-a2-and-term
           (list
            (putnam-1999-a2-polynomial-term
             carrier zero polynomial)
            rest-valid)))
         (recursive-result
          (putnam-1999-a2-operation-term
           poly-add
           (putnam-1999-a2-operation-term
            poly-mul polynomial polynomial)
           (putnam-1999-a2-apply1-term
            sum-of-squares rest)))
         (laws
          (putnam-1999-a2-and-term
           (list
            (list
             'equal
             (putnam-1999-a2-apply1-term
              sum-of-squares
              (putnam-1999-a2-quoted nil))
             qzero-polynomial)
            (putnam-1999-a2-implies-term
             domain
             (putnam-1999-a2-and-term
              (list
               (putnam-1999-a2-polynomial-term
                carrier
                zero
                (putnam-1999-a2-apply1-term
                 sum-of-squares
                 (list 'cons polynomial rest)))
               (list
                'equal
                (putnam-1999-a2-apply1-term
                 sum-of-squares
                 (list 'cons polynomial rest))
                recursive-result))))))))
    (list
     'lambda
     '(polynomial rest)
     laws)))

(defun putnam-1999-a2-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate poly-add poly-mul sum-of-squares)
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
   (tamep-functionp poly-add)
   (tamep-functionp poly-mul)
   (tamep-functionp sum-of-squares)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (fn-equal
    (putnam-1999-a2-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-1999-a2-true-function '(x y z)))
   (fn-equal
    (putnam-1999-a2-order-laws-function
     carrier zero add mul lt)
    (putnam-1999-a2-true-function '(x y z)))
   (fn-equal
    (putnam-1999-a2-square-root-laws-function
     carrier zero mul lt square-root)
    (putnam-1999-a2-true-function '(x)))
   (fn-equal
    (putnam-1999-a2-evaluation-laws-function
     carrier zero add mul evaluate)
    (putnam-1999-a2-true-function
     '(coefficient rest x)))
   (fn-equal
    (putnam-1999-a2-odd-root-laws-function
     carrier zero evaluate odd-root)
    (putnam-1999-a2-true-function
     '(coefficients)))
   (fn-equal
    (putnam-1999-a2-polynomial-operation-laws-function
     carrier zero add mul evaluate poly-add poly-mul)
    (putnam-1999-a2-true-function
     '(left right x)))
   (fn-equal
    (putnam-1999-a2-sum-of-squares-laws-function
     carrier zero poly-add poly-mul sum-of-squares)
    (putnam-1999-a2-true-function
     '(polynomial rest)))))

(defun putnam-1999-a2-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-1999-a2-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-1999-a2-polynomial-p
    (polynomial carrier zero)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-1999-a2-coefficient-list-p
    polynomial carrier)
   (or
    (equal (len polynomial) 1)
    (not (equal (car (last polynomial)) zero)))))

(defun putnam-1999-a2-nonnegative-function
    (carrier zero lt evaluate polynomial)
  (let* ((x 'x)
         (domain
          (putnam-1999-a2-carrier-term carrier x))
         (nonnegative
          (putnam-1999-a2-not-term
           (putnam-1999-a2-operation-term
            lt
            (putnam-1999-a2-operation-term
             evaluate polynomial x)
            (putnam-1999-a2-quoted zero)))))
    (list
     'lambda
     '(x)
     (putnam-1999-a2-implies-term
      domain nonnegative))))

(defun putnam-1999-a2-decomposition-failure-function
    (carrier zero sum-of-squares polynomial)
  (let* ((witness 'witness)
         (qualification
          (putnam-1999-a2-and-term
           (list
            (list 'true-listp witness)
            (list 'consp witness)
            (putnam-1999-a2-all-polynomials-term
             carrier zero witness)
            (list
             'equal
             (putnam-1999-a2-apply1-term
              sum-of-squares witness)
             (putnam-1999-a2-quoted polynomial))))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-1999-a2-quoted nil)
      (putnam-1999-a2-quoted t)))))

(defun putnam-1999-a2-decomposition-exists-p
    (carrier zero sum-of-squares polynomial)
  (let ((failure-function
         (putnam-1999-a2-decomposition-failure-function
          carrier zero sum-of-squares polynomial))
        (true-function
         (putnam-1999-a2-true-function '(witness))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-1999-a2-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate poly-add poly-mul sum-of-squares polynomial)
  (implies
   (and
    (putnam-1999-a2-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root
     evaluate poly-add poly-mul sum-of-squares)
    (putnam-1999-a2-polynomial-p
     polynomial carrier zero)
    (fn-equal
     (putnam-1999-a2-nonnegative-function
      carrier zero lt evaluate polynomial)
     (putnam-1999-a2-true-function '(x))))
   (putnam-1999-a2-decomposition-exists-p
    carrier zero sum-of-squares polynomial)))

(value-triple :itpeval-statement-checked)
:q
