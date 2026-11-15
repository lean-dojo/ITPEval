;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_a3:
;; every nonzero differentiable critical point of the quotient of a
;; positive-degree complex polynomial p by either principal z^(n/2) or
;; principal csqrt(z^n), when every zero of p is on the unit circle, is on
;; the unit circle. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Complex numbers are pairs over a represented real closed field, and a
;; polynomial is a canonical nonempty coefficient list in ascending degree
;; order. FN-EQUAL expresses universal quantification over all field pairs.
;; This is not a restriction to ACL2's rational or complex-rational numbers:
;; the assertion is first-order over real closed fields, so real-closed-field
;; completeness transfers it bidirectionally between the reals and any such
;; represented field.
;;
;; The parameter g is eliminated only through its pointwise definition. The
;; denominator-mode parameter is restricted to :COMPLEX-POWER (the Lean
;; principal z^(n/2)) or :SQRT-POWER (the Isabelle/Rocq principal
;; csqrt(z^n)). Principal square root and complex division are defined below
;; from the represented ordered real closed field.
;;
;; Crucially, the source's differentiability hypothesis is not replaced by a
;; derived polynomial equation. A tame Skolem function supplies delta for
;; each positive epsilon, and FN-EQUAL universally checks every complex
;; increment h. The squared-norm inequality
;;
;;   |g(z+h)-g(z)|^2 < epsilon^2 * |h|^2
;;
;; is exactly the epsilon-delta definition that g is complex differentiable
;; at z with derivative zero. Finally, |z|=1 is represented exactly by
;; Re(z)^2+Im(z)^2=1.

(defun putnam-2005-a3-quoted (object)
  (list 'quote object))

(defun putnam-2005-a3-apply1-term (function argument)
  (list
   'apply$
   (putnam-2005-a3-quoted function)
   (list 'cons argument nil)))

(defun putnam-2005-a3-apply2-term (function left right)
  (list
   'apply$
   (putnam-2005-a3-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2005-a3-and-term (terms)
  (if (endp terms)
      (putnam-2005-a3-quoted t)
    (list
     'if
     (car terms)
     (putnam-2005-a3-and-term (cdr terms))
     (putnam-2005-a3-quoted nil))))

(defun putnam-2005-a3-or-term (terms)
  (if (endp terms)
      (putnam-2005-a3-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2005-a3-quoted t)
     (putnam-2005-a3-or-term (cdr terms)))))

(defun putnam-2005-a3-not-term (term)
  (list
   'if
   term
   (putnam-2005-a3-quoted nil)
   (putnam-2005-a3-quoted t)))

(defun putnam-2005-a3-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2005-a3-quoted t)))

(defun putnam-2005-a3-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2005-a3-quoted t)))

(defun putnam-2005-a3-carrier-term (carrier element)
  (putnam-2005-a3-apply1-term carrier element))

(defun putnam-2005-a3-operation-term (operation left right)
  (putnam-2005-a3-apply2-term operation left right))

(defun putnam-2005-a3-all-real-coefficients-function
    (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2005-a3-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2005-a3-all-real-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2005-a3-quoted
    (putnam-2005-a3-all-real-coefficients-function
     carrier))
   (putnam-2005-a3-quoted nil)
   coefficients))

(defun putnam-2005-a3-real-polynomial-term
    (carrier zero coefficients)
  (putnam-2005-a3-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2005-a3-all-real-coefficients-term
     carrier coefficients)
    (putnam-2005-a3-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2005-a3-quoted 1))
      (putnam-2005-a3-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2005-a3-quoted zero))))))))

(defun putnam-2005-a3-second-term (value)
  (list 'car (list 'cdr value)))

(defun putnam-2005-a3-complex-pair-term (real imaginary)
  (list 'cons real (list 'cons imaginary nil)))

(defun putnam-2005-a3-complex-term-p (carrier value)
  (putnam-2005-a3-and-term
   (list
    (list 'true-listp value)
    (list 'equal
          (list 'len value)
          (putnam-2005-a3-quoted 2))
    (putnam-2005-a3-carrier-term
     carrier (list 'car value))
    (putnam-2005-a3-carrier-term
     carrier (putnam-2005-a3-second-term value)))))

(defun putnam-2005-a3-complex-add-term (add left right)
  (putnam-2005-a3-complex-pair-term
   (putnam-2005-a3-operation-term
    add (list 'car left) (list 'car right))
   (putnam-2005-a3-operation-term
    add
    (putnam-2005-a3-second-term left)
    (putnam-2005-a3-second-term right))))

(defun putnam-2005-a3-complex-mul-term
    (add mul neg left right)
  (putnam-2005-a3-complex-pair-term
   (putnam-2005-a3-operation-term
    add
    (putnam-2005-a3-operation-term
     mul (list 'car left) (list 'car right))
    (putnam-2005-a3-apply1-term
     neg
     (putnam-2005-a3-operation-term
      mul
      (putnam-2005-a3-second-term left)
      (putnam-2005-a3-second-term right))))
   (putnam-2005-a3-operation-term
    add
    (putnam-2005-a3-operation-term
     mul
     (list 'car left)
     (putnam-2005-a3-second-term right))
    (putnam-2005-a3-operation-term
     mul
     (putnam-2005-a3-second-term left)
     (list 'car right)))))

(defun putnam-2005-a3-all-complex-coefficients-function
    (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2005-a3-complex-term-p
    carrier 'loop$-ivars)))

(defun putnam-2005-a3-all-complex-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2005-a3-quoted
    (putnam-2005-a3-all-complex-coefficients-function
     carrier))
   (putnam-2005-a3-quoted nil)
   coefficients))

(defun putnam-2005-a3-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2005-a3-quoted zero))
         (qone (putnam-2005-a3-quoted one))
         (add-xy
          (putnam-2005-a3-operation-term add x y))
         (add-yz
          (putnam-2005-a3-operation-term add y z))
         (mul-xy
          (putnam-2005-a3-operation-term mul x y))
         (mul-yz
          (putnam-2005-a3-operation-term mul y z))
         (neg-x
          (putnam-2005-a3-apply1-term neg x))
         (inv-x
          (putnam-2005-a3-apply1-term inv x))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier x)
            (putnam-2005-a3-carrier-term carrier y)
            (putnam-2005-a3-carrier-term carrier z))))
         (laws
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier add-xy)
            (putnam-2005-a3-carrier-term carrier mul-xy)
            (putnam-2005-a3-carrier-term carrier neg-x)
            (putnam-2005-a3-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2005-a3-operation-term add add-xy z)
             (putnam-2005-a3-operation-term add x add-yz))
            (list
             'equal
             (putnam-2005-a3-operation-term mul mul-xy z)
             (putnam-2005-a3-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2005-a3-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2005-a3-operation-term mul y x))
            (list
             'equal
             (putnam-2005-a3-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2005-a3-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2005-a3-operation-term mul x qone)
             x)
            (putnam-2005-a3-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2005-a3-implies-term
             (putnam-2005-a3-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2005-a3-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2005-a3-operation-term mul x add-yz)
             (putnam-2005-a3-operation-term
              add
              (putnam-2005-a3-operation-term mul x y)
              (putnam-2005-a3-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2005-a3-implies-term domain laws))))

(defun putnam-2005-a3-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2005-a3-quoted zero))
         (lt-xy
          (putnam-2005-a3-operation-term lt x y))
         (lt-yx
          (putnam-2005-a3-operation-term lt y x))
         (lt-yz
          (putnam-2005-a3-operation-term lt y z))
         (lt-xz
          (putnam-2005-a3-operation-term lt x z))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier x)
            (putnam-2005-a3-carrier-term carrier y)
            (putnam-2005-a3-carrier-term carrier z))))
         (laws
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-not-term
             (putnam-2005-a3-operation-term lt x x))
            (putnam-2005-a3-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2005-a3-implies-term
             (putnam-2005-a3-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2005-a3-implies-term
             lt-xy
             (putnam-2005-a3-operation-term
              lt
              (putnam-2005-a3-operation-term add x z)
              (putnam-2005-a3-operation-term add y z)))
            (putnam-2005-a3-implies-term
             (putnam-2005-a3-and-term
              (list
               (putnam-2005-a3-operation-term lt qzero x)
               (putnam-2005-a3-operation-term lt qzero y)))
             (putnam-2005-a3-operation-term
              lt
              qzero
              (putnam-2005-a3-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2005-a3-implies-term domain laws))))

(defun putnam-2005-a3-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2005-a3-quoted zero))
         (root
          (putnam-2005-a3-apply1-term square-root x))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier x)
            (putnam-2005-a3-not-term
             (putnam-2005-a3-operation-term lt x qzero)))))
         (laws
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier root)
            (putnam-2005-a3-not-term
             (putnam-2005-a3-operation-term lt root qzero))
            (list
             'equal
             (putnam-2005-a3-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2005-a3-implies-term domain laws))))

(defun putnam-2005-a3-real-evaluation-laws-function
    (carrier zero add mul real-evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2005-a3-quoted zero))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2005-a3-all-real-coefficients-term
             carrier rest)
            (putnam-2005-a3-carrier-term carrier x))))
         (empty-law
          (putnam-2005-a3-implies-term
           (putnam-2005-a3-carrier-term carrier x)
           (list
            'equal
            (putnam-2005-a3-operation-term
             real-evaluate
             (putnam-2005-a3-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2005-a3-operation-term
           add
           coefficient
           (putnam-2005-a3-operation-term
            mul
            x
            (putnam-2005-a3-operation-term
             real-evaluate rest x))))
         (recursive-law
          (putnam-2005-a3-implies-term
           domain
           (putnam-2005-a3-and-term
            (list
             (putnam-2005-a3-carrier-term
              carrier
              (putnam-2005-a3-operation-term
               real-evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2005-a3-operation-term
               real-evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2005-a3-and-term
      (list empty-law recursive-law)))))

(defun putnam-2005-a3-odd-root-laws-function
    (carrier zero real-evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2005-a3-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-real-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier root)
            (list
             'equal
             (putnam-2005-a3-operation-term
              real-evaluate coefficients root)
             (putnam-2005-a3-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2005-a3-implies-term domain laws))))

(defun putnam-2005-a3-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root
             real-evaluate odd-root)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (tamep-functionp square-root)
   (tamep-functionp real-evaluate)
   (tamep-functionp odd-root)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (fn-equal
    (putnam-2005-a3-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-2005-a3-true-function '(x y z)))
   (fn-equal
    (putnam-2005-a3-order-laws-function
     carrier zero add mul lt)
    (putnam-2005-a3-true-function '(x y z)))
   (fn-equal
    (putnam-2005-a3-square-root-laws-function
     carrier zero mul lt square-root)
    (putnam-2005-a3-true-function '(x)))
   (fn-equal
    (putnam-2005-a3-real-evaluation-laws-function
     carrier zero add mul real-evaluate)
    (putnam-2005-a3-true-function
     '(coefficient rest x)))
   (fn-equal
    (putnam-2005-a3-odd-root-laws-function
     carrier zero real-evaluate odd-root)
    (putnam-2005-a3-true-function '(coefficients)))))

(defun putnam-2005-a3-complex-p (value carrier)
  (and
   (true-listp value)
   (equal (len value) 2)
   (apply$ carrier (list (car value)))
   (apply$ carrier (list (cadr value)))))

(defun putnam-2005-a3-complex-zero-p (value zero)
  (and
   (equal (car value) zero)
   (equal (cadr value) zero)))

(defun putnam-2005-a3-complex-add (left right add)
  (list
   (apply$ add (list (car left) (car right)))
   (apply$ add (list (cadr left) (cadr right)))))

(defun putnam-2005-a3-complex-mul
    (left right add mul neg)
  (let* ((ac (apply$ mul (list (car left) (car right))))
         (bd (apply$ mul (list (cadr left) (cadr right))))
         (ad (apply$ mul (list (car left) (cadr right))))
         (bc (apply$ mul (list (cadr left) (car right)))))
    (list
     (apply$ add (list ac (apply$ neg (list bd))))
     (apply$ add (list ad bc)))))

(defun putnam-2005-a3-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (apply$
     add
     (list
      one
      (putnam-2005-a3-field-natural
       (- n 1) zero one add)))))

(defun putnam-2005-a3-complex-scale
    (scalar value mul)
  (list
   (apply$ mul (list scalar (car value)))
   (apply$ mul (list scalar (cadr value)))))

(defun putnam-2005-a3-complex-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (putnam-2005-a3-complex-p
      (car coefficients) carrier)
     (putnam-2005-a3-complex-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2005-a3-complex-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-2005-a3-complex-coefficient-list-p
    coefficients carrier)
   (or
    (equal (len coefficients) 1)
    (not
     (putnam-2005-a3-complex-zero-p
      (car (last coefficients)) zero)))))

(defun putnam-2005-a3-complex-evaluation-laws-function
    (carrier zero add mul neg complex-evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (y 'y)
         (z
          (putnam-2005-a3-complex-pair-term x y))
         (complex-zero
          (putnam-2005-a3-complex-pair-term
           (putnam-2005-a3-quoted zero)
           (putnam-2005-a3-quoted zero)))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-complex-term-p
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2005-a3-all-complex-coefficients-term
             carrier rest)
            (putnam-2005-a3-carrier-term carrier x)
            (putnam-2005-a3-carrier-term carrier y))))
         (empty-law
          (putnam-2005-a3-implies-term
           (putnam-2005-a3-and-term
            (list
             (putnam-2005-a3-carrier-term carrier x)
             (putnam-2005-a3-carrier-term carrier y)))
           (list
            'equal
            (putnam-2005-a3-operation-term
             complex-evaluate
             (putnam-2005-a3-quoted nil)
             z)
            complex-zero)))
         (recursive-value
          (putnam-2005-a3-complex-add-term
           add
           coefficient
           (putnam-2005-a3-complex-mul-term
            add mul neg
            z
            (putnam-2005-a3-operation-term
             complex-evaluate rest z))))
         (evaluated
          (putnam-2005-a3-operation-term
           complex-evaluate
           (list 'cons coefficient rest)
           z))
         (recursive-law
          (putnam-2005-a3-implies-term
           domain
           (putnam-2005-a3-and-term
            (list
             (putnam-2005-a3-complex-term-p
              carrier evaluated)
             (list 'equal evaluated recursive-value))))))
    (list
     'lambda
     '(coefficient rest x y)
     (putnam-2005-a3-and-term
      (list empty-law recursive-law)))))

(defun putnam-2005-a3-complex-poly-derivative-aux
    (coefficients degree zero one add mul)
  (if (consp coefficients)
      (cons
       (putnam-2005-a3-complex-scale
        (putnam-2005-a3-field-natural
         degree zero one add)
        (car coefficients)
        mul)
       (putnam-2005-a3-complex-poly-derivative-aux
        (cdr coefficients)
        (+ 1 (nfix degree))
        zero one add mul))
    nil))

(defun putnam-2005-a3-complex-poly-derivative
    (coefficients zero one add mul)
  (if (consp coefficients)
      (putnam-2005-a3-complex-poly-derivative-aux
       (cdr coefficients) 1 zero one add mul)
    nil))

(defun putnam-2005-a3-norm-squared (value add mul)
  (apply$
   add
   (list
    (apply$ mul (list (car value) (car value)))
    (apply$ mul (list (cadr value) (cadr value))))))

(defun putnam-2005-a3-root-condition-function
    (carrier zero one add mul complex-evaluate coefficients)
  (let* ((x 'x)
         (y 'y)
         (qone (putnam-2005-a3-quoted one))
         (qcoefficients
          (putnam-2005-a3-quoted coefficients))
         (z
          (putnam-2005-a3-complex-pair-term x y))
         (value
          (putnam-2005-a3-operation-term
           complex-evaluate qcoefficients z))
         (domain
          (putnam-2005-a3-and-term
           (list
            (putnam-2005-a3-carrier-term carrier x)
            (putnam-2005-a3-carrier-term carrier y))))
         (is-root
          (list
           'equal
           value
           (putnam-2005-a3-complex-pair-term
            (putnam-2005-a3-quoted zero)
            (putnam-2005-a3-quoted zero))))
         (on-circle
          (list
           'equal
           (putnam-2005-a3-operation-term
            add
            (putnam-2005-a3-operation-term mul x x)
            (putnam-2005-a3-operation-term mul y y))
           qone)))
    (list
     'lambda
     '(x y)
     (putnam-2005-a3-implies-term
      domain
      (putnam-2005-a3-implies-term
       is-root on-circle)))))

(defun putnam-2005-a3-all-roots-on-unit-circle-p
    (carrier zero one add mul complex-evaluate coefficients)
  (fn-equal
   (putnam-2005-a3-root-condition-function
    carrier zero one add mul complex-evaluate coefficients)
   (putnam-2005-a3-true-function '(x y))))

(defun putnam-2005-a3-complex-evaluator-p
    (carrier zero add mul neg complex-evaluate)
  (and
   (tamep-functionp complex-evaluate)
   (fn-equal
    (putnam-2005-a3-complex-evaluation-laws-function
     carrier zero add mul neg complex-evaluate)
    (putnam-2005-a3-true-function
     '(coefficient rest x y)))))

(defun putnam-2005-a3-complex-power
    (z n zero one add mul neg)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list one zero)
    (putnam-2005-a3-complex-mul
     z
     (putnam-2005-a3-complex-power
      z (- n 1) zero one add mul neg)
     add mul neg)))

(defun putnam-2005-a3-field-sub (left right add neg)
  (apply$
   add
   (list left (apply$ neg (list right)))))

(defun putnam-2005-a3-field-half
    (value one add mul inv)
  (apply$
   mul
   (list
    value
    (apply$
     inv
     (list (apply$ add (list one one)))))))

(defun putnam-2005-a3-complex-principal-sqrt
    (z zero one add mul neg inv lt square-root)
  (let* ((real-part (car z))
         (imaginary-part (cadr z))
         (radius
          (apply$
           square-root
           (list
            (putnam-2005-a3-norm-squared z add mul))))
         (real-square
          (putnam-2005-a3-field-half
           (apply$ add (list radius real-part))
           one add mul inv))
         (imaginary-square
          (putnam-2005-a3-field-half
           (putnam-2005-a3-field-sub
            radius real-part add neg)
           one add mul inv))
         (root-real
          (apply$ square-root (list real-square)))
         (root-imaginary-magnitude
          (apply$ square-root (list imaginary-square)))
         (root-imaginary
          (if (apply$ lt (list imaginary-part zero))
              (apply$ neg (list root-imaginary-magnitude))
            root-imaginary-magnitude)))
    (list root-real root-imaginary)))

(defun putnam-2005-a3-complex-inverse
    (z add mul neg inv)
  (let ((inverse-norm
         (apply$
          inv
          (list
           (putnam-2005-a3-norm-squared z add mul)))))
    (list
     (apply$ mul (list (car z) inverse-norm))
     (apply$
      mul
      (list
       (apply$ neg (list (cadr z)))
       inverse-norm)))))

(defun putnam-2005-a3-complex-divide
    (numerator denominator add mul neg inv)
  (putnam-2005-a3-complex-mul
   numerator
   (putnam-2005-a3-complex-inverse
    denominator add mul neg inv)
   add mul neg))

(defun putnam-2005-a3-denominator
    (denominator-mode n z zero one add mul neg inv lt square-root)
  (if (equal denominator-mode :complex-power)
      (if (evenp n)
          (putnam-2005-a3-complex-power
           z (floor n 2) zero one add mul neg)
        (putnam-2005-a3-complex-mul
         (putnam-2005-a3-complex-power
          z (floor n 2) zero one add mul neg)
         (putnam-2005-a3-complex-principal-sqrt
          z zero one add mul neg inv lt square-root)
         add mul neg))
    (putnam-2005-a3-complex-principal-sqrt
     (putnam-2005-a3-complex-power
      z n zero one add mul neg)
     zero one add mul neg inv lt square-root)))

(defun putnam-2005-a3-quotient-value
    (denominator-mode coefficients n z zero one add mul neg inv lt
                      square-root complex-evaluate)
  (putnam-2005-a3-complex-divide
   (apply$ complex-evaluate (list coefficients z))
   (putnam-2005-a3-denominator
    denominator-mode n z zero one add mul neg inv lt square-root)
   add mul neg inv))

(defun putnam-2005-a3-critical-sample-p
    (carrier zero one add mul neg inv lt square-root complex-evaluate
             critical-delta denominator-mode coefficients n z
             epsilon h-real h-imaginary)
  (if (and
       (apply$ carrier (list epsilon))
       (apply$ carrier (list h-real))
       (apply$ carrier (list h-imaginary))
       (apply$ lt (list zero epsilon)))
      (let* ((delta
              (apply$ critical-delta (list epsilon)))
             (h (list h-real h-imaginary))
             (h-norm-squared
              (putnam-2005-a3-norm-squared h add mul))
             (delta-squared
              (apply$ mul (list delta delta)))
             (epsilon-squared
              (apply$ mul (list epsilon epsilon)))
             (z-plus-h
              (putnam-2005-a3-complex-add z h add))
             (value-at-z
              (putnam-2005-a3-quotient-value
               denominator-mode coefficients n z
               zero one add mul neg inv lt square-root
               complex-evaluate))
             (value-at-z-plus-h
              (putnam-2005-a3-quotient-value
               denominator-mode coefficients n z-plus-h
               zero one add mul neg inv lt square-root
               complex-evaluate))
             (difference
              (putnam-2005-a3-complex-add
               value-at-z-plus-h
               (list
                (apply$ neg (list (car value-at-z)))
                (apply$ neg (list (cadr value-at-z))))
               add))
             (difference-norm-squared
              (putnam-2005-a3-norm-squared difference add mul)))
        (and
         (apply$ carrier (list delta))
         (apply$ lt (list zero delta))
         (implies
          (and
           (apply$ lt (list zero h-norm-squared))
           (apply$ lt
                   (list h-norm-squared delta-squared)))
          (apply$
           lt
           (list
            difference-norm-squared
            (apply$
             mul
             (list epsilon-squared h-norm-squared)))))))
    t))

(defun putnam-2005-a3-critical-condition-function
    (carrier zero one add mul neg inv lt square-root complex-evaluate
             critical-delta denominator-mode coefficients n z)
  (list
   'lambda
   '(epsilon h-real h-imaginary)
   (list
    'putnam-2005-a3-critical-sample-p
    (putnam-2005-a3-quoted carrier)
    (putnam-2005-a3-quoted zero)
    (putnam-2005-a3-quoted one)
    (putnam-2005-a3-quoted add)
    (putnam-2005-a3-quoted mul)
    (putnam-2005-a3-quoted neg)
    (putnam-2005-a3-quoted inv)
    (putnam-2005-a3-quoted lt)
    (putnam-2005-a3-quoted square-root)
    (putnam-2005-a3-quoted complex-evaluate)
    (putnam-2005-a3-quoted critical-delta)
    (putnam-2005-a3-quoted denominator-mode)
    (putnam-2005-a3-quoted coefficients)
    (putnam-2005-a3-quoted n)
    (putnam-2005-a3-quoted z)
    'epsilon
    'h-real
    'h-imaginary)))

(defun putnam-2005-a3-differentiable-critical-point-p
    (carrier zero one add mul neg inv lt square-root complex-evaluate
             critical-delta denominator-mode coefficients n z)
  (and
   (tamep-functionp critical-delta)
   (fn-equal
    (putnam-2005-a3-critical-condition-function
     carrier zero one add mul neg inv lt square-root complex-evaluate
     critical-delta denominator-mode coefficients n z)
    (putnam-2005-a3-true-function
     '(epsilon h-real h-imaginary)))))

(defun putnambench-putnam-2005-a3-statement
    (carrier zero one add mul neg inv lt square-root
             real-evaluate odd-root complex-evaluate
             critical-delta denominator-mode coefficients n z)
  (implies
   (and
    (putnam-2005-a3-real-closed-field-p
     carrier zero one add mul neg inv lt square-root
     real-evaluate odd-root)
    (putnam-2005-a3-complex-evaluator-p
     carrier zero add mul neg complex-evaluate)
    (or
     (equal denominator-mode :complex-power)
     (equal denominator-mode :sqrt-power))
    (natp n)
    (< 0 n)
    (putnam-2005-a3-complex-polynomial-p
     coefficients carrier zero)
    (equal (len coefficients) (+ 1 n))
    (putnam-2005-a3-all-roots-on-unit-circle-p
     carrier zero one add mul complex-evaluate coefficients)
    (putnam-2005-a3-complex-p z carrier)
    (not (putnam-2005-a3-complex-zero-p z zero))
    (putnam-2005-a3-differentiable-critical-point-p
     carrier zero one add mul neg inv lt square-root complex-evaluate
     critical-delta denominator-mode coefficients n z))
   (equal
    (putnam-2005-a3-norm-squared z add mul)
    one)))

(value-triple :itpeval-statement-checked)
:q
