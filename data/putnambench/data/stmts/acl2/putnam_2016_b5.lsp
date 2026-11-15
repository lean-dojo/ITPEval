;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_b5:
;; classification of functions from (1,infinity) to (1,infinity) preserving
;; the stated square-to-cube interval bounds as exactly the positive real
;; power functions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Exact reals are represented by rational regular Cauchy names, and functions
;; on (1,infinity) are extensional ACL2 function objects on those names.
;; FN-EQUAL supplies unbounded universal quantification over names and function
;; objects. NOT/FN-EQUAL keeps the source's exponent witness internal.
;;
;; The internal power oracle P(s,x) is required, for every real s>1, to be
;; positive, normalized by P(s,0)=1 and P(s,1)=s, additive-to-multiplicative
;; in the exponent, and monotone in the exponent. These laws uniquely
;; characterize the standard real power s^x, and standard real power supplies
;; such an oracle. Thus the oracle is a bidirectionally equivalent definition,
;; not an uninterpreted operation or a restriction to rational exponents.

(defun putnam-2016-b5-quoted (object)
  (list 'quote object))

(defun putnam-2016-b5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2016-b5-term-list (cdr terms)))
    nil))

(defun putnam-2016-b5-apply-term (function arguments)
  (list 'apply$
        (putnam-2016-b5-quoted function)
        (putnam-2016-b5-term-list arguments)))

(defun putnam-2016-b5-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2016-b5-term-list arguments)))

(defun putnam-2016-b5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2016-b5-and-terms (cdr terms))
            (putnam-2016-b5-quoted nil))
    (putnam-2016-b5-quoted t)))

(defun putnam-2016-b5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2016-b5-quoted t)))

(defun putnam-2016-b5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2016-b5-negate-term (value)
  (list 'unary-- value))

(defun putnam-2016-b5-subtract-term (left right)
  (putnam-2016-b5-add-term
   left
   (putnam-2016-b5-negate-term right)))

(defun putnam-2016-b5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2016-b5-divide-term (numerator denominator)
  (putnam-2016-b5-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2016-b5-absolute-term (value)
  (list 'if
        (list '< value (putnam-2016-b5-quoted 0))
        (putnam-2016-b5-negate-term value)
        value))

(defun putnam-2016-b5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2016-b5-quoted nil)
        (putnam-2016-b5-quoted t)))

(defun putnam-2016-b5-positive-rational-term (value)
  (putnam-2016-b5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2016-b5-quoted 0) value))))

(defun putnam-2016-b5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2016-b5-quoted t)))

(defun putnam-2016-b5-real-value-term (name precision)
  (putnam-2016-b5-apply-term name (list precision)))

(defun putnam-2016-b5-object-real-value-term
    (name-term precision)
  (putnam-2016-b5-apply-object-term
   name-term
   (list precision)))

(defun putnam-2016-b5-real-cauchy-function (name)
  (let* ((left
          (putnam-2016-b5-real-value-term name 'epsilon))
         (right
          (putnam-2016-b5-real-value-term name 'eta))
         (distance
          (putnam-2016-b5-absolute-term
           (putnam-2016-b5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (putnam-2016-b5-positive-rational-term 'epsilon)
        (putnam-2016-b5-positive-rational-term 'eta)))
      (putnam-2016-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2016-b5-less-equal-term
         distance
         (putnam-2016-b5-add-term
          'epsilon 'eta))))))))

(defun putnam-2016-b5-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2016-b5-real-cauchy-function name)
    (putnam-2016-b5-true-function
     '(epsilon eta)))))

;; Sampling at eta/4 makes these exact predicates on the represented limits.

(defun putnam-2016-b5-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2016-b5-multiply-term 1/4 'eta))
         (left
          (putnam-2016-b5-real-value-term
           left-name precision))
         (right
          (putnam-2016-b5-real-value-term
           right-name precision))
         (distance
          (putnam-2016-b5-absolute-term
           (putnam-2016-b5-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-positive-rational-term 'eta)
      (putnam-2016-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2016-b5-less-equal-term
         distance
         (putnam-2016-b5-add-term
          (putnam-2016-b5-quoted bound)
          'eta))))))))

(defun putnam-2016-b5-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2016-b5-real-name-p left-name)
   (putnam-2016-b5-real-name-p right-name)
   (fn-equal
    (putnam-2016-b5-real-distance-function
     left-name right-name bound)
    (putnam-2016-b5-true-function '(eta)))))

(defun putnam-2016-b5-real-equal-p
    (left-name right-name)
  (putnam-2016-b5-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2016-b5-real-order-function
    (left-name right-name)
  (let* ((precision
          (putnam-2016-b5-multiply-term 1/4 'eta))
         (left
          (putnam-2016-b5-real-value-term
           left-name precision))
         (right
          (putnam-2016-b5-real-value-term
           right-name precision)))
    (list
     'lambda
     '(eta)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-positive-rational-term 'eta)
      (putnam-2016-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2016-b5-less-equal-term
         left
         (putnam-2016-b5-add-term
          right 'eta))))))))

(defun putnam-2016-b5-real-le-p
    (left-name right-name)
  (and
   (putnam-2016-b5-real-name-p left-name)
   (putnam-2016-b5-real-name-p right-name)
   (fn-equal
    (putnam-2016-b5-real-order-function
     left-name right-name)
    (putnam-2016-b5-true-function '(eta)))))

(defun putnam-2016-b5-real-lt-p
    (left-name right-name)
  (and
   (putnam-2016-b5-real-le-p left-name right-name)
   (not
    (putnam-2016-b5-real-equal-p
     left-name right-name))))

(defun putnam-2016-b5-rational-name (value)
  (list 'lambda
        '(precision)
        (putnam-2016-b5-quoted value)))

(defun putnam-2016-b5-add-name (left-name right-name)
  (let* ((precision
          (putnam-2016-b5-multiply-term 1/2 'epsilon))
         (left
          (putnam-2016-b5-object-real-value-term
           (putnam-2016-b5-quoted left-name)
           precision))
         (right
          (putnam-2016-b5-object-real-value-term
           (putnam-2016-b5-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2016-b5-add-term left right))))

(defun putnam-2016-b5-multiply-name
    (left-name right-name)
  (let* ((left-at-one
          (putnam-2016-b5-object-real-value-term
           (putnam-2016-b5-quoted left-name)
           1))
         (right-at-one
          (putnam-2016-b5-object-real-value-term
           (putnam-2016-b5-quoted right-name)
           1))
         (scale
          (putnam-2016-b5-multiply-term
           8
           (putnam-2016-b5-add-term
            3
            (putnam-2016-b5-add-term
             (putnam-2016-b5-absolute-term left-at-one)
             (putnam-2016-b5-absolute-term right-at-one)))))
         (candidate
          (putnam-2016-b5-divide-term
           'epsilon scale))
         (precision
          (list 'if
                (list '< 1 candidate)
                1
                candidate))
         (left
          (putnam-2016-b5-object-real-value-term
           (putnam-2016-b5-quoted left-name)
           precision))
         (right
          (putnam-2016-b5-object-real-value-term
           (putnam-2016-b5-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2016-b5-multiply-term left right))))

(defun putnam-2016-b5-interval-function-output-function
    (function)
  (let ((output
         (putnam-2016-b5-apply-term function '(x)))
        (one-name
         (putnam-2016-b5-rational-name 1)))
    (list
     'lambda
     '(x)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'x)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'x)))
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p output)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              output)))))))

(defun putnam-2016-b5-interval-function-extensional-function
    (function)
  (let ((left-output
         (putnam-2016-b5-apply-term
          function '(left)))
        (right-output
         (putnam-2016-b5-apply-term
          function '(right)))
        (one-name
         (putnam-2016-b5-rational-name 1)))
    (list
     'lambda
     '(left right)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'left)
        (list 'putnam-2016-b5-real-name-p 'right)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'left)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'right)
        (list 'putnam-2016-b5-real-equal-p
              'left 'right)))
      (list 'putnam-2016-b5-real-equal-p
            left-output right-output)))))

(defun putnam-2016-b5-interval-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2016-b5-interval-function-output-function
     function)
    (putnam-2016-b5-true-function '(x)))
   (fn-equal
    (putnam-2016-b5-interval-function-extensional-function
     function)
    (putnam-2016-b5-true-function
     '(left right)))))

(defun putnam-2016-b5-bound-condition-function (function)
  (let* ((one-name
          (putnam-2016-b5-rational-name 1))
         (x-square
          (list 'putnam-2016-b5-multiply-name
                'x 'x))
         (x-cube
          (list 'putnam-2016-b5-multiply-name
                x-square 'x))
         (fx
          (putnam-2016-b5-apply-term function '(x)))
         (fy
          (putnam-2016-b5-apply-term function '(y)))
         (fx-square
          (list 'putnam-2016-b5-multiply-name
                fx fx))
         (fx-cube
          (list 'putnam-2016-b5-multiply-name
                fx-square fx)))
    (list
     'lambda
     '(x y)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'x)
        (list 'putnam-2016-b5-real-name-p 'y)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'x)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'y)
        (list 'putnam-2016-b5-real-le-p
              x-square 'y)
        (list 'putnam-2016-b5-real-le-p
              'y x-cube)))
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-le-p
              fx-square fy)
        (list 'putnam-2016-b5-real-le-p
              fy fx-cube)))))))

(defun putnam-2016-b5-bound-condition-p (function)
  (fn-equal
   (putnam-2016-b5-bound-condition-function function)
   (putnam-2016-b5-true-function '(x y))))

(defun putnam-2016-b5-power-output-function (power)
  (let ((output
         (putnam-2016-b5-apply-term power '(base exponent)))
        (one-name
         (putnam-2016-b5-rational-name 1)))
    (list
     'lambda
     '(base exponent)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'base)
        (list 'putnam-2016-b5-real-name-p 'exponent)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'base)))
      (list 'putnam-2016-b5-real-name-p output)))))

(defun putnam-2016-b5-power-extensional-function (power)
  (let ((left-output
         (putnam-2016-b5-apply-term
          power '(base-left exponent-left)))
        (right-output
         (putnam-2016-b5-apply-term
          power '(base-right exponent-right)))
        (one-name
         (putnam-2016-b5-rational-name 1)))
    (list
     'lambda
     '(base-left base-right exponent-left exponent-right)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'base-left)
        (list 'putnam-2016-b5-real-name-p 'base-right)
        (list 'putnam-2016-b5-real-name-p 'exponent-left)
        (list 'putnam-2016-b5-real-name-p 'exponent-right)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'base-left)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'base-right)
        (list 'putnam-2016-b5-real-equal-p
              'base-left 'base-right)
        (list 'putnam-2016-b5-real-equal-p
              'exponent-left 'exponent-right)))
      (list 'putnam-2016-b5-real-equal-p
            left-output right-output)))))

(defun putnam-2016-b5-power-law-function (power)
  (let* ((zero-name
          (putnam-2016-b5-rational-name 0))
         (one-name
          (putnam-2016-b5-rational-name 1))
         (at-x
          (putnam-2016-b5-apply-term
           power '(base x)))
         (at-y
          (putnam-2016-b5-apply-term
           power '(base y)))
         (at-zero
          (putnam-2016-b5-apply-term
           power
           (list 'base
                 (putnam-2016-b5-quoted zero-name))))
         (at-one
          (putnam-2016-b5-apply-term
           power
           (list 'base
                 (putnam-2016-b5-quoted one-name))))
         (sum-name
          (list 'putnam-2016-b5-add-name 'x 'y))
         (at-sum
          (putnam-2016-b5-apply-term
           power
           (list 'base sum-name)))
         (product-name
          (list 'putnam-2016-b5-multiply-name
                at-x at-y)))
    (list
     'lambda
     '(base x y)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'base)
        (list 'putnam-2016-b5-real-name-p 'x)
        (list 'putnam-2016-b5-real-name-p 'y)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'base)))
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted zero-name)
              at-x)
        (list 'putnam-2016-b5-real-equal-p
              at-zero
              (putnam-2016-b5-quoted one-name))
        (list 'putnam-2016-b5-real-equal-p
              at-one 'base)
        (list 'putnam-2016-b5-real-equal-p
              at-sum product-name)
        (putnam-2016-b5-implies-term
         (list 'putnam-2016-b5-real-le-p 'x 'y)
         (list 'putnam-2016-b5-real-le-p
               at-x at-y))))))))

(defun putnam-2016-b5-power-oracle-p (power)
  (and
   (tamep-functionp power)
   (fn-equal
    (putnam-2016-b5-power-output-function power)
    (putnam-2016-b5-true-function
     '(base exponent)))
   (fn-equal
    (putnam-2016-b5-power-extensional-function power)
    (putnam-2016-b5-true-function
     '(base-left base-right exponent-left exponent-right)))
   (fn-equal
    (putnam-2016-b5-power-law-function power)
    (putnam-2016-b5-true-function
     '(base x y)))))

(defun putnam-2016-b5-solution-equality-function
    (function exponent power)
  (let ((function-value
         (putnam-2016-b5-apply-term function '(x)))
        (power-value
         (putnam-2016-b5-apply-term
          power
          (list 'x
                (putnam-2016-b5-quoted exponent))))
        (one-name
         (putnam-2016-b5-rational-name 1)))
    (list
     'lambda
     '(x)
     (putnam-2016-b5-implies-term
      (putnam-2016-b5-and-terms
       (list
        (list 'putnam-2016-b5-real-name-p 'x)
        (list 'putnam-2016-b5-real-lt-p
              (putnam-2016-b5-quoted one-name)
              'x)))
      (list 'putnam-2016-b5-real-equal-p
            function-value power-value)))))

(defun putnam-2016-b5-solution-witness-p
    (witness function)
  (and
   (true-listp witness)
   (equal (len witness) 2)
   (let ((exponent (nth 0 witness))
         (power (nth 1 witness))
         (zero-name
          (putnam-2016-b5-rational-name 0)))
     (and
      (putnam-2016-b5-real-name-p exponent)
      (putnam-2016-b5-real-lt-p zero-name exponent)
      (putnam-2016-b5-power-oracle-p power)
      (fn-equal
       (putnam-2016-b5-solution-equality-function
        function exponent power)
       (putnam-2016-b5-true-function '(x)))))))

(defun putnam-2016-b5-solution-failure-function (function)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list 'putnam-2016-b5-solution-witness-p
          'witness
          (putnam-2016-b5-quoted function))
    (putnam-2016-b5-quoted nil)
    (putnam-2016-b5-quoted t))))

(defun putnam-2016-b5-solution-exists-p (function)
  (not
   (fn-equal
    (putnam-2016-b5-solution-failure-function function)
    (putnam-2016-b5-true-function '(witness)))))

(defun putnambench-putnam-2016-b5-statement (function)
  (implies
   (putnam-2016-b5-interval-function-p function)
   (iff
    (putnam-2016-b5-bound-condition-p function)
    (putnam-2016-b5-solution-exists-p function))))

(value-triple :itpeval-statement-checked)
:q
