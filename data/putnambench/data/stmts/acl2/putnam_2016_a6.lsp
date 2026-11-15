;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_a6:
;; the least constant bounding the integral of the absolute value of every
;; real cubic with a root in [0,1] by its maximum absolute value is 5/6.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are interpreted in an arbitrary real closed ordered field. Real
;; closed fields are elementarily equivalent. The cubic, maximum, and
;; piecewise-antiderivative relations below are first-order, so the resulting
;; assertion is bidirectionally equivalent to the source statement over R.
;;
;; A cubic is its four coefficients in ascending degree order. A maximum is
;; characterized by attainment and a universal upper-bound condition. The
;; integral of |P| is characterized by three ordered cut points, enough to
;; separate all sign intervals of a cubic, and the exact antiderivative on
;; each interval. These witnesses remain internal: the universal witness
;; tuple formulation is equivalent because maximum and integral values are
;; uniquely characterized, while a root occurs only in an antecedent.

(defun putnam-2016-a6-quoted (object)
  (list 'quote object))

(defun putnam-2016-a6-apply1-term (function argument)
  (list
   'apply$
   (putnam-2016-a6-quoted function)
   (list 'cons argument nil)))

(defun putnam-2016-a6-apply2-term (function left right)
  (list
   'apply$
   (putnam-2016-a6-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2016-a6-and-term (terms)
  (if (endp terms)
      (putnam-2016-a6-quoted t)
    (list
     'if
     (car terms)
     (putnam-2016-a6-and-term (cdr terms))
     (putnam-2016-a6-quoted nil))))

(defun putnam-2016-a6-or-term (terms)
  (if (endp terms)
      (putnam-2016-a6-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2016-a6-quoted t)
     (putnam-2016-a6-or-term (cdr terms)))))

(defun putnam-2016-a6-not-term (term)
  (list
   'if
   term
   (putnam-2016-a6-quoted nil)
   (putnam-2016-a6-quoted t)))

(defun putnam-2016-a6-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2016-a6-quoted t)))

(defun putnam-2016-a6-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2016-a6-quoted t)))

(defun putnam-2016-a6-carrier-term (carrier element)
  (putnam-2016-a6-apply1-term carrier element))

(defun putnam-2016-a6-operation-term (operation left right)
  (putnam-2016-a6-apply2-term operation left right))

(defun putnam-2016-a6-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2016-a6-carrier-term carrier 'loop$-ivars)))

(defun putnam-2016-a6-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2016-a6-quoted
    (putnam-2016-a6-all-coefficients-function carrier))
   (putnam-2016-a6-quoted nil)
   coefficients))

(defun putnam-2016-a6-polynomial-term
    (carrier zero coefficients)
  (putnam-2016-a6-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2016-a6-all-coefficients-term
     carrier coefficients)
    (putnam-2016-a6-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2016-a6-quoted 1))
      (putnam-2016-a6-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2016-a6-quoted zero))))))))

(defun putnam-2016-a6-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2016-a6-quoted zero))
         (qone (putnam-2016-a6-quoted one))
         (add-xy
          (putnam-2016-a6-operation-term add x y))
         (add-yz
          (putnam-2016-a6-operation-term add y z))
         (mul-xy
          (putnam-2016-a6-operation-term mul x y))
         (mul-yz
          (putnam-2016-a6-operation-term mul y z))
         (neg-x
          (putnam-2016-a6-apply1-term neg x))
         (inv-x
          (putnam-2016-a6-apply1-term inv x))
         (domain
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term carrier x)
            (putnam-2016-a6-carrier-term carrier y)
            (putnam-2016-a6-carrier-term carrier z))))
         (laws
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term carrier add-xy)
            (putnam-2016-a6-carrier-term carrier mul-xy)
            (putnam-2016-a6-carrier-term carrier neg-x)
            (putnam-2016-a6-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2016-a6-operation-term add add-xy z)
             (putnam-2016-a6-operation-term add x add-yz))
            (list
             'equal
             (putnam-2016-a6-operation-term mul mul-xy z)
             (putnam-2016-a6-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2016-a6-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2016-a6-operation-term mul y x))
            (list
             'equal
             (putnam-2016-a6-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2016-a6-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2016-a6-operation-term mul x qone)
             x)
            (putnam-2016-a6-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2016-a6-implies-term
             (putnam-2016-a6-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2016-a6-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2016-a6-operation-term mul x add-yz)
             (putnam-2016-a6-operation-term
              add
              (putnam-2016-a6-operation-term mul x y)
              (putnam-2016-a6-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2016-a6-implies-term domain laws))))

(defun putnam-2016-a6-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2016-a6-quoted zero))
         (lt-xy
          (putnam-2016-a6-operation-term lt x y))
         (lt-yx
          (putnam-2016-a6-operation-term lt y x))
         (lt-yz
          (putnam-2016-a6-operation-term lt y z))
         (lt-xz
          (putnam-2016-a6-operation-term lt x z))
         (domain
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term carrier x)
            (putnam-2016-a6-carrier-term carrier y)
            (putnam-2016-a6-carrier-term carrier z))))
         (laws
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-not-term
             (putnam-2016-a6-operation-term lt x x))
            (putnam-2016-a6-or-term
             (list lt-xy (list 'equal x y) lt-yx))
            (putnam-2016-a6-implies-term
             (putnam-2016-a6-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2016-a6-implies-term
             lt-xy
             (putnam-2016-a6-operation-term
              lt
              (putnam-2016-a6-operation-term add x z)
              (putnam-2016-a6-operation-term add y z)))
            (putnam-2016-a6-implies-term
             (putnam-2016-a6-and-term
              (list
               (putnam-2016-a6-operation-term lt qzero x)
               (putnam-2016-a6-operation-term lt qzero y)))
             (putnam-2016-a6-operation-term
              lt
              qzero
              (putnam-2016-a6-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2016-a6-implies-term domain laws))))

(defun putnam-2016-a6-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2016-a6-quoted zero))
         (root
          (putnam-2016-a6-apply1-term square-root x))
         (domain
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term carrier x)
            (putnam-2016-a6-not-term
             (putnam-2016-a6-operation-term lt x qzero)))))
         (laws
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term carrier root)
            (list
             'equal
             (putnam-2016-a6-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2016-a6-implies-term domain laws))))

(defun putnam-2016-a6-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2016-a6-quoted zero))
         (domain
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2016-a6-all-coefficients-term
             carrier rest)
            (putnam-2016-a6-carrier-term carrier x))))
         (empty-law
          (putnam-2016-a6-implies-term
           (putnam-2016-a6-carrier-term carrier x)
           (list
            'equal
            (putnam-2016-a6-operation-term
             evaluate
             (putnam-2016-a6-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2016-a6-operation-term
           add
           coefficient
           (putnam-2016-a6-operation-term
            mul
            x
            (putnam-2016-a6-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2016-a6-implies-term
           domain
           (putnam-2016-a6-and-term
            (list
             (putnam-2016-a6-carrier-term
              carrier
              (putnam-2016-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2016-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2016-a6-and-term
      (list empty-law recursive-law)))))

(defun putnam-2016-a6-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2016-a6-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2016-a6-and-term
           (list
            (putnam-2016-a6-carrier-term carrier root)
            (list
             'equal
             (putnam-2016-a6-operation-term
              evaluate coefficients root)
             (putnam-2016-a6-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2016-a6-implies-term domain laws))))

(defun putnam-2016-a6-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2016-a6-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2016-a6-true-function '(x y z)))
         (order-laws
          (putnam-2016-a6-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2016-a6-true-function '(x y z)))
         (square-root-laws
          (putnam-2016-a6-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2016-a6-true-function '(x)))
         (evaluation-laws
          (putnam-2016-a6-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2016-a6-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2016-a6-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2016-a6-true-function
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

(defun putnam-2016-a6-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2016-a6-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2016-a6-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2016-a6-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2016-a6-lt (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2016-a6-le (lt left right)
  (not (putnam-2016-a6-lt lt right left)))

(defun putnam-2016-a6-sub (add neg left right)
  (putnam-2016-a6-add
   add left (putnam-2016-a6-neg neg right)))

(defun putnam-2016-a6-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2016-a6-add
     add
     one
     (putnam-2016-a6-field-natural
      (- n 1) zero one add))))

(defun putnam-2016-a6-field-rational
    (numerator denominator zero one add mul inv)
  (putnam-2016-a6-mul
   mul
   (putnam-2016-a6-field-natural
    numerator zero one add)
   (putnam-2016-a6-inv
    inv
    (putnam-2016-a6-field-natural
     denominator zero one add))))

(defun putnam-2016-a6-eval (coefficients x evaluate)
  (apply$ evaluate (list coefficients x)))

(defun putnam-2016-a6-abs
    (value zero neg lt)
  (if (putnam-2016-a6-lt lt value zero)
      (putnam-2016-a6-neg neg value)
    value))

(defun putnam-2016-a6-interval-p
    (x left right lt)
  (and
   (putnam-2016-a6-le lt left x)
   (putnam-2016-a6-le lt x right)))

(defun putnam-2016-a6-antiderivative-coefficients
    (coefficients zero one add mul inv)
  (list
   zero
   (nth 0 coefficients)
   (putnam-2016-a6-mul
    mul
    (nth 1 coefficients)
    (putnam-2016-a6-inv
     inv
     (putnam-2016-a6-field-natural
      2 zero one add)))
   (putnam-2016-a6-mul
    mul
    (nth 2 coefficients)
    (putnam-2016-a6-inv
     inv
     (putnam-2016-a6-field-natural
      3 zero one add)))
   (putnam-2016-a6-mul
    mul
    (nth 3 coefficients)
    (putnam-2016-a6-inv
     inv
     (putnam-2016-a6-field-natural
      4 zero one add)))))

(defun putnam-2016-a6-midpoint
    (left right zero one add mul inv)
  (putnam-2016-a6-mul
   mul
   (putnam-2016-a6-add add left right)
   (putnam-2016-a6-inv
    inv
    (putnam-2016-a6-field-natural
     2 zero one add))))

(defun putnam-2016-a6-segment-sign-point-p
    (coefficients left right negativep x
                  carrier zero neg lt evaluate)
  (declare (ignore neg))
  (implies
   (and
    (apply$ carrier (list x))
    (putnam-2016-a6-interval-p x left right lt))
   (let ((value
          (putnam-2016-a6-eval
           coefficients x evaluate)))
     (if negativep
         (putnam-2016-a6-le lt value zero)
       (putnam-2016-a6-le lt zero value)))))

(defun putnam-2016-a6-segment-sign-function
    (coefficients left right negativep
                  carrier zero neg lt evaluate)
  (list
   'lambda
   '(x)
   (list
    'putnam-2016-a6-segment-sign-point-p
    (putnam-2016-a6-quoted coefficients)
    (putnam-2016-a6-quoted left)
    (putnam-2016-a6-quoted right)
    (putnam-2016-a6-quoted negativep)
    'x
    (putnam-2016-a6-quoted carrier)
    (putnam-2016-a6-quoted zero)
    (putnam-2016-a6-quoted neg)
    (putnam-2016-a6-quoted lt)
    (putnam-2016-a6-quoted evaluate))))

(defun putnam-2016-a6-segment-sign-valid-p
    (coefficients left right negativep
                  carrier zero neg lt evaluate)
  (let ((condition
         (putnam-2016-a6-segment-sign-function
          coefficients left right negativep
          carrier zero neg lt evaluate))
        (always-true
         (putnam-2016-a6-true-function '(x))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnam-2016-a6-segment-negative-p
    (coefficients left right zero one add mul inv lt evaluate)
  (putnam-2016-a6-lt
   lt
   (putnam-2016-a6-eval
    coefficients
    (putnam-2016-a6-midpoint
     left right zero one add mul inv)
    evaluate)
   zero))

(defun putnam-2016-a6-segment-integral
    (coefficients left right zero one add mul neg inv lt evaluate)
  (let* ((antiderivative
          (putnam-2016-a6-antiderivative-coefficients
           coefficients zero one add mul inv))
         (left-value
          (putnam-2016-a6-eval
           antiderivative left evaluate))
         (right-value
          (putnam-2016-a6-eval
           antiderivative right evaluate)))
    (if
        (putnam-2016-a6-segment-negative-p
         coefficients left right zero one add mul inv lt evaluate)
        (putnam-2016-a6-sub
         add neg left-value right-value)
      (putnam-2016-a6-sub
       add neg right-value left-value))))

(defun putnam-2016-a6-segment-valid-p
    (coefficients left right
                  carrier zero one add mul neg inv lt evaluate)
  (let ((negativep
         (putnam-2016-a6-segment-negative-p
          coefficients left right zero one add mul inv lt evaluate)))
    (putnam-2016-a6-segment-sign-valid-p
     coefficients left right negativep
     carrier zero neg lt evaluate)))

(defun putnam-2016-a6-four-segment-integral
    (coefficients cut1 cut2 cut3
                  zero one add mul neg inv lt evaluate)
  (putnam-2016-a6-add
   add
   (putnam-2016-a6-segment-integral
    coefficients zero cut1
    zero one add mul neg inv lt evaluate)
   (putnam-2016-a6-add
    add
    (putnam-2016-a6-segment-integral
     coefficients cut1 cut2
     zero one add mul neg inv lt evaluate)
    (putnam-2016-a6-add
     add
     (putnam-2016-a6-segment-integral
      coefficients cut2 cut3
      zero one add mul neg inv lt evaluate)
     (putnam-2016-a6-segment-integral
      coefficients cut3 one
      zero one add mul neg inv lt evaluate)))))

(defun putnam-2016-a6-integral-relation-p
    (coefficients cut1 cut2 cut3 integral
                  carrier zero one add mul neg inv lt evaluate)
  (and
   (putnam-2016-a6-le lt zero cut1)
   (putnam-2016-a6-le lt cut1 cut2)
   (putnam-2016-a6-le lt cut2 cut3)
   (putnam-2016-a6-le lt cut3 one)
   (putnam-2016-a6-segment-valid-p
    coefficients zero cut1
    carrier zero one add mul neg inv lt evaluate)
   (putnam-2016-a6-segment-valid-p
    coefficients cut1 cut2
    carrier zero one add mul neg inv lt evaluate)
   (putnam-2016-a6-segment-valid-p
    coefficients cut2 cut3
    carrier zero one add mul neg inv lt evaluate)
   (putnam-2016-a6-segment-valid-p
    coefficients cut3 one
    carrier zero one add mul neg inv lt evaluate)
   (equal
    integral
    (putnam-2016-a6-four-segment-integral
     coefficients cut1 cut2 cut3
     zero one add mul neg inv lt evaluate))))

(defun putnam-2016-a6-max-upper-point-field-p
    (coefficients maximum x carrier zero one neg lt evaluate)
  (implies
   (and
    (apply$ carrier (list x))
    (putnam-2016-a6-interval-p x zero one lt))
   (putnam-2016-a6-le
    lt
    (putnam-2016-a6-abs
     (putnam-2016-a6-eval coefficients x evaluate)
     zero neg lt)
    maximum)))

(defun putnam-2016-a6-max-upper-function
    (coefficients maximum carrier zero one neg lt evaluate)
  (list
   'lambda
   '(x)
   (list
    'putnam-2016-a6-max-upper-point-field-p
    (putnam-2016-a6-quoted coefficients)
    (putnam-2016-a6-quoted maximum)
    'x
    (putnam-2016-a6-quoted carrier)
    (putnam-2016-a6-quoted zero)
    (putnam-2016-a6-quoted one)
    (putnam-2016-a6-quoted neg)
    (putnam-2016-a6-quoted lt)
    (putnam-2016-a6-quoted evaluate))))

(defun putnam-2016-a6-max-upper-p
    (coefficients maximum carrier zero one neg lt evaluate)
  (let ((condition
         (putnam-2016-a6-max-upper-function
          coefficients maximum carrier zero one neg lt evaluate))
        (always-true
         (putnam-2016-a6-true-function '(x))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnam-2016-a6-maximum-relation-p
    (coefficients maximum maximum-point
                  carrier zero one neg lt evaluate)
  (and
   (putnam-2016-a6-interval-p maximum-point zero one lt)
   (equal
    maximum
    (putnam-2016-a6-abs
     (putnam-2016-a6-eval
      coefficients maximum-point evaluate)
     zero neg lt))
   (putnam-2016-a6-max-upper-p
    coefficients maximum carrier zero one neg lt evaluate)))

(defun putnam-2016-a6-carrier-elements-p
    (values carrier)
  (if (endp values)
      (equal values nil)
    (and
     (apply$ carrier (list (car values)))
     (putnam-2016-a6-carrier-elements-p
      (cdr values) carrier))))

(defun putnam-2016-a6-bound-instance-p
    (witness constant
             carrier zero one add mul neg inv lt evaluate)
  (if
      (and
       (true-listp witness)
       (equal (len witness) 11)
       (putnam-2016-a6-carrier-elements-p witness carrier)
       (not (equal (nth 3 witness) zero))
       (putnam-2016-a6-interval-p
        (nth 4 witness) zero one lt)
       (equal
        (putnam-2016-a6-eval
         (list (nth 0 witness)
               (nth 1 witness)
               (nth 2 witness)
               (nth 3 witness))
         (nth 4 witness)
         evaluate)
        zero)
       (putnam-2016-a6-integral-relation-p
        (list (nth 0 witness)
              (nth 1 witness)
              (nth 2 witness)
              (nth 3 witness))
        (nth 5 witness)
        (nth 6 witness)
        (nth 7 witness)
        (nth 8 witness)
        carrier zero one add mul neg inv lt evaluate)
       (putnam-2016-a6-maximum-relation-p
        (list (nth 0 witness)
              (nth 1 witness)
              (nth 2 witness)
              (nth 3 witness))
        (nth 9 witness)
        (nth 10 witness)
        carrier zero one neg lt evaluate))
      (putnam-2016-a6-le
       lt
       (nth 8 witness)
       (putnam-2016-a6-mul
        mul constant (nth 9 witness)))
    t))

(defun putnam-2016-a6-bound-function
    (constant carrier zero one add mul neg inv lt evaluate)
  (list
   'lambda
   '(witness)
   (list
    'putnam-2016-a6-bound-instance-p
    'witness
    (putnam-2016-a6-quoted constant)
    (putnam-2016-a6-quoted carrier)
    (putnam-2016-a6-quoted zero)
    (putnam-2016-a6-quoted one)
    (putnam-2016-a6-quoted add)
    (putnam-2016-a6-quoted mul)
    (putnam-2016-a6-quoted neg)
    (putnam-2016-a6-quoted inv)
    (putnam-2016-a6-quoted lt)
    (putnam-2016-a6-quoted evaluate))))

(defun putnam-2016-a6-bound-p
    (constant carrier zero one add mul neg inv lt evaluate)
  (let ((condition
         (putnam-2016-a6-bound-function
          constant carrier zero one add mul neg inv lt evaluate))
        (always-true
         (putnam-2016-a6-true-function '(witness))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnambench-putnam-2016-a6-statement
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate constant)
  (implies
   (putnam-2016-a6-real-closed-field-p
    carrier zero one add mul neg inv lt
    square-root odd-root evaluate)
   (let ((solution
          (putnam-2016-a6-field-rational
           5 6 zero one add mul inv)))
     (and
      (putnam-2016-a6-bound-p
       solution carrier zero one add mul neg inv lt evaluate)
      (implies
       (and
        (apply$ carrier (list constant))
        (putnam-2016-a6-bound-p
         constant carrier zero one add mul neg inv lt evaluate))
       (putnam-2016-a6-le lt solution constant))))))

(value-triple :itpeval-statement-checked)
:q
