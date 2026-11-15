;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_b5:
;; continuously differentiable real functions preserving reduced rational
;; denominators are exactly integer translates of x or -x. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, and real functions are extensional
;; function objects on those names. Positive rational tolerances and moduli are
;; cofinal in the positive reals. For a continuous function, convergence of
;; difference quotients along nonzero rational increments is equivalent to the
;; full real derivative limit. Thus the internal continuous derivative witness
;; below is equivalent to continuous differentiability on all of R.

(defun putnam-2008-b5-quoted (object)
  (list 'quote object))

(defun putnam-2008-b5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2008-b5-term-list (cdr terms)))
    nil))

(defun putnam-2008-b5-apply-term (function arguments)
  (list 'apply$
        (putnam-2008-b5-quoted function)
        (putnam-2008-b5-term-list arguments)))

(defun putnam-2008-b5-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2008-b5-term-list arguments)))

(defun putnam-2008-b5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2008-b5-and-terms (cdr terms))
            (putnam-2008-b5-quoted nil))
    (putnam-2008-b5-quoted t)))

(defun putnam-2008-b5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2008-b5-quoted t)))

(defun putnam-2008-b5-not-term (term)
  (list 'if
        term
        (putnam-2008-b5-quoted nil)
        (putnam-2008-b5-quoted t)))

(defun putnam-2008-b5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2008-b5-negate-term (value)
  (list 'unary-- value))

(defun putnam-2008-b5-subtract-term (left right)
  (putnam-2008-b5-add-term
   left
   (putnam-2008-b5-negate-term right)))

(defun putnam-2008-b5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2008-b5-divide-term (numerator denominator)
  (putnam-2008-b5-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2008-b5-absolute-term (value)
  (list 'if
        (list '< value (putnam-2008-b5-quoted 0))
        (putnam-2008-b5-negate-term value)
        value))

(defun putnam-2008-b5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2008-b5-quoted nil)
        (putnam-2008-b5-quoted t)))

(defun putnam-2008-b5-positive-rational-term (value)
  (putnam-2008-b5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2008-b5-quoted 0) value))))

(defun putnam-2008-b5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2008-b5-quoted t)))

(defun putnam-2008-b5-real-value-term (name precision)
  (putnam-2008-b5-apply-term name (list precision)))

(defun putnam-2008-b5-object-real-value-term
    (name-term precision)
  (putnam-2008-b5-apply-object-term
   name-term
   (list precision)))

(defun putnam-2008-b5-real-cauchy-function (name)
  (let* ((left
          (putnam-2008-b5-real-value-term name 'epsilon))
         (right
          (putnam-2008-b5-real-value-term name 'eta))
         (distance
          (putnam-2008-b5-absolute-term
           (putnam-2008-b5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2008-b5-implies-term
      (putnam-2008-b5-and-terms
       (list
        (putnam-2008-b5-positive-rational-term 'epsilon)
        (putnam-2008-b5-positive-rational-term 'eta)))
      (putnam-2008-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2008-b5-less-equal-term
         distance
         (putnam-2008-b5-add-term
          'epsilon 'eta))))))))

(defun putnam-2008-b5-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2008-b5-real-cauchy-function name)
    (putnam-2008-b5-true-function
     '(epsilon eta)))))

;; Sampling both names at eta/4 makes the displayed universal inequality
;; equivalent to distance between their represented limits being at most BOUND.

(defun putnam-2008-b5-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2008-b5-multiply-term
           (putnam-2008-b5-quoted 1/4)
           'eta))
         (left
          (putnam-2008-b5-real-value-term
           left-name precision))
         (right
          (putnam-2008-b5-real-value-term
           right-name precision))
         (distance
          (putnam-2008-b5-absolute-term
           (putnam-2008-b5-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2008-b5-implies-term
      (putnam-2008-b5-positive-rational-term 'eta)
      (putnam-2008-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2008-b5-less-equal-term
         distance
         (putnam-2008-b5-add-term
          (putnam-2008-b5-quoted bound)
          'eta))))))))

(defun putnam-2008-b5-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2008-b5-real-name-p left-name)
   (putnam-2008-b5-real-name-p right-name)
   (fn-equal
    (putnam-2008-b5-real-distance-function
     left-name right-name bound)
    (putnam-2008-b5-true-function '(eta)))))

(defun putnam-2008-b5-real-equal-p
    (left-name right-name)
  (putnam-2008-b5-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2008-b5-unary-output-function
    (function)
  (let ((output
         (putnam-2008-b5-apply-term function (list 'x))))
    (list
     'lambda
     '(x)
     (putnam-2008-b5-implies-term
      (list 'putnam-2008-b5-real-name-p 'x)
      (list 'putnam-2008-b5-real-name-p output)))))

(defun putnam-2008-b5-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-2008-b5-apply-term
          function (list 'x-left)))
        (right-output
         (putnam-2008-b5-apply-term
          function (list 'x-right))))
    (list
     'lambda
     '(x-left x-right)
     (putnam-2008-b5-implies-term
      (list 'putnam-2008-b5-real-equal-p
            'x-left 'x-right)
      (list 'putnam-2008-b5-real-equal-p
            left-output right-output)))))

(defun putnam-2008-b5-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2008-b5-unary-output-function function)
    (putnam-2008-b5-true-function '(x)))
   (fn-equal
    (putnam-2008-b5-unary-extensional-function function)
    (putnam-2008-b5-true-function
     '(x-left x-right)))))

(defun putnam-2008-b5-rational-name (value)
  (list 'lambda
        '(precision)
        (putnam-2008-b5-quoted value)))

(defun putnam-2008-b5-rational-shift-name (name shift)
  (let ((value
         (putnam-2008-b5-object-real-value-term
          (putnam-2008-b5-quoted name)
          (putnam-2008-b5-multiply-term
           (putnam-2008-b5-quoted 1/2)
           'precision))))
    (list
     'lambda
     '(precision)
     (putnam-2008-b5-add-term
      value
      (putnam-2008-b5-quoted shift)))))

(defun putnam-2008-b5-affine-name (name integer slope)
  (let* ((value
          (putnam-2008-b5-object-real-value-term
           (putnam-2008-b5-quoted name)
           (putnam-2008-b5-multiply-term
            (putnam-2008-b5-quoted 1/2)
            'precision)))
         (signed-value
          (if (equal slope -1)
              (putnam-2008-b5-negate-term value)
            value)))
    (list
     'lambda
     '(precision)
     (putnam-2008-b5-add-term
      signed-value
      (putnam-2008-b5-quoted integer)))))

;; Continuity is stated with closed rational balls and non-strict output
;; bounds. Rescaling epsilon and delta gives the usual open-ball definition in
;; both directions.

(defun putnam-2008-b5-continuous-at-delta-function
    (function x epsilon delta)
  (let ((at-x
         (putnam-2008-b5-apply-term
          function
          (list (putnam-2008-b5-quoted x))))
        (at-y
         (putnam-2008-b5-apply-term
          function
          (list 'y))))
    (list
     'lambda
     '(y)
     (putnam-2008-b5-implies-term
      (putnam-2008-b5-and-terms
       (list
        (list 'putnam-2008-b5-real-name-p 'y)
        (list 'putnam-2008-b5-real-distance-at-most-p
              (putnam-2008-b5-quoted x)
              'y
              (putnam-2008-b5-quoted delta))))
      (list 'putnam-2008-b5-real-distance-at-most-p
            at-x
            at-y
            (putnam-2008-b5-quoted epsilon))))))

(defun putnam-2008-b5-continuous-at-delta-p
    (function x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2008-b5-continuous-at-delta-function
     function x epsilon delta)
    (putnam-2008-b5-true-function '(y)))))

(defun putnam-2008-b5-continuity-delta-failure-function
    (function x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2008-b5-continuous-at-delta-p
          (putnam-2008-b5-quoted function)
          (putnam-2008-b5-quoted x)
          (putnam-2008-b5-quoted epsilon)
          'delta)
    (putnam-2008-b5-quoted nil)
    (putnam-2008-b5-quoted t))))

(defun putnam-2008-b5-continuity-delta-exists-p
    (function x epsilon)
  (not
   (fn-equal
    (putnam-2008-b5-continuity-delta-failure-function
     function x epsilon)
    (putnam-2008-b5-true-function '(delta)))))

(defun putnam-2008-b5-continuity-function (function)
  (list
   'lambda
   '(x epsilon)
   (putnam-2008-b5-implies-term
    (putnam-2008-b5-and-terms
     (list
      (list 'putnam-2008-b5-real-name-p 'x)
      (putnam-2008-b5-positive-rational-term 'epsilon)))
    (list 'putnam-2008-b5-continuity-delta-exists-p
          (putnam-2008-b5-quoted function)
          'x
          'epsilon))))

(defun putnam-2008-b5-continuous-p (function)
  (and
   (putnam-2008-b5-real-function-p function)
   (fn-equal
    (putnam-2008-b5-continuity-function function)
    (putnam-2008-b5-true-function
     '(x epsilon)))))

;; At precision eta, each numerator value below is sampled at
;; |h|*eta/4. Hence the quotient is a regular Cauchy name for
;; (f(x+h)-f(x))/h whenever h is a nonzero rational.

(defun putnam-2008-b5-difference-quotient-name
    (function x h)
  (let* ((shifted-x
          (putnam-2008-b5-rational-shift-name x h))
         (at-shifted-x
          (putnam-2008-b5-apply-term
           function
           (list (putnam-2008-b5-quoted shifted-x))))
         (at-x
          (putnam-2008-b5-apply-term
           function
           (list (putnam-2008-b5-quoted x))))
         (sample-precision
          (putnam-2008-b5-multiply-term
           (putnam-2008-b5-quoted (/ (abs h) 4))
           'eta))
         (shifted-value
          (putnam-2008-b5-object-real-value-term
           at-shifted-x sample-precision))
         (value
          (putnam-2008-b5-object-real-value-term
           at-x sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-2008-b5-divide-term
      (putnam-2008-b5-subtract-term
       shifted-value value)
      (putnam-2008-b5-quoted h)))))

(defun putnam-2008-b5-derivative-at-delta-function
    (function derivative x epsilon delta)
  (let ((quotient
         (list 'putnam-2008-b5-difference-quotient-name
               (putnam-2008-b5-quoted function)
               (putnam-2008-b5-quoted x)
               'h))
        (derivative-at-x
         (putnam-2008-b5-apply-term
          derivative
          (list (putnam-2008-b5-quoted x)))))
    (list
     'lambda
     '(h)
     (putnam-2008-b5-implies-term
      (putnam-2008-b5-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-2008-b5-not-term
         (list 'equal 'h (putnam-2008-b5-quoted 0)))
        (putnam-2008-b5-less-equal-term
         (putnam-2008-b5-absolute-term 'h)
         (putnam-2008-b5-quoted delta))))
      (list 'putnam-2008-b5-real-distance-at-most-p
            quotient
            derivative-at-x
            (putnam-2008-b5-quoted epsilon))))))

(defun putnam-2008-b5-derivative-at-delta-p
    (function derivative x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2008-b5-derivative-at-delta-function
     function derivative x epsilon delta)
    (putnam-2008-b5-true-function '(h)))))

(defun putnam-2008-b5-derivative-delta-failure-function
    (function derivative x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2008-b5-derivative-at-delta-p
          (putnam-2008-b5-quoted function)
          (putnam-2008-b5-quoted derivative)
          (putnam-2008-b5-quoted x)
          (putnam-2008-b5-quoted epsilon)
          'delta)
    (putnam-2008-b5-quoted nil)
    (putnam-2008-b5-quoted t))))

(defun putnam-2008-b5-derivative-delta-exists-p
    (function derivative x epsilon)
  (not
   (fn-equal
    (putnam-2008-b5-derivative-delta-failure-function
     function derivative x epsilon)
    (putnam-2008-b5-true-function '(delta)))))

(defun putnam-2008-b5-derivative-function
    (function derivative)
  (list
   'lambda
   '(x epsilon)
   (putnam-2008-b5-implies-term
    (putnam-2008-b5-and-terms
     (list
      (list 'putnam-2008-b5-real-name-p 'x)
      (putnam-2008-b5-positive-rational-term 'epsilon)))
    (list 'putnam-2008-b5-derivative-delta-exists-p
          (putnam-2008-b5-quoted function)
          (putnam-2008-b5-quoted derivative)
          'x
          'epsilon))))

(defun putnam-2008-b5-derivative-relation-p
    (function derivative)
  (and
   (putnam-2008-b5-real-function-p function)
   (putnam-2008-b5-real-function-p derivative)
   (fn-equal
    (putnam-2008-b5-derivative-function
     function derivative)
    (putnam-2008-b5-true-function
     '(x epsilon)))))

(defun putnam-2008-b5-c1-witness-p
    (derivative function)
  (and
   (putnam-2008-b5-continuous-p function)
   (putnam-2008-b5-continuous-p derivative)
   (putnam-2008-b5-derivative-relation-p
    function derivative)))

(defun putnam-2008-b5-c1-witness-failure-function
    (function)
  (list
   'lambda
   '(derivative)
   (list
    'if
    (list 'putnam-2008-b5-c1-witness-p
          'derivative
          (putnam-2008-b5-quoted function))
    (putnam-2008-b5-quoted nil)
    (putnam-2008-b5-quoted t))))

(defun putnam-2008-b5-continuously-differentiable-p
    (function)
  (not
   (fn-equal
    (putnam-2008-b5-c1-witness-failure-function
     function)
    (putnam-2008-b5-true-function
     '(derivative)))))

;; The rational witness p is internal, and ACL2's DENOMINATOR is the positive
;; denominator of a reduced exact rational.

(defun putnam-2008-b5-same-denominator-witness-p
    (p function q)
  (and
   (rationalp p)
   (equal (denominator p)
          (denominator q))
   (putnam-2008-b5-real-equal-p
    (apply$ function
            (list
             (putnam-2008-b5-rational-name q)))
    (putnam-2008-b5-rational-name p))))

(defun putnam-2008-b5-rational-witness-failure-function
    (function q)
  (list
   'lambda
   '(p)
   (list
    'if
    (list 'putnam-2008-b5-same-denominator-witness-p
          'p
          (putnam-2008-b5-quoted function)
          (putnam-2008-b5-quoted q))
    (putnam-2008-b5-quoted nil)
    (putnam-2008-b5-quoted t))))

(defun putnam-2008-b5-rational-witness-exists-p
    (function q)
  (not
   (fn-equal
    (putnam-2008-b5-rational-witness-failure-function
     function q)
    (putnam-2008-b5-true-function '(p)))))

(defun putnam-2008-b5-denominator-property-function
    (function)
  (list
   'lambda
   '(q)
   (putnam-2008-b5-implies-term
    (list 'rationalp 'q)
    (list 'putnam-2008-b5-rational-witness-exists-p
          (putnam-2008-b5-quoted function)
          'q))))

(defun putnam-2008-b5-denominator-property-p
    (function)
  (and
   (putnam-2008-b5-real-function-p function)
   (fn-equal
    (putnam-2008-b5-denominator-property-function
     function)
    (putnam-2008-b5-true-function '(q)))))

;; The integer n remains existentially quantified inside each of the two
;; source solution families.

(defun putnam-2008-b5-affine-solution-function
    (function integer slope)
  (let ((actual
         (putnam-2008-b5-apply-term
          function (list 'x)))
        (expected
         (list 'putnam-2008-b5-affine-name
               'x
               (putnam-2008-b5-quoted integer)
               (putnam-2008-b5-quoted slope))))
    (list
     'lambda
     '(x)
     (putnam-2008-b5-implies-term
      (list 'putnam-2008-b5-real-name-p 'x)
      (list 'putnam-2008-b5-real-equal-p
            actual expected)))))

(defun putnam-2008-b5-affine-solution-with-integer-p
    (integer function slope)
  (and
   (integerp integer)
   (fn-equal
    (putnam-2008-b5-affine-solution-function
     function integer slope)
    (putnam-2008-b5-true-function '(x)))))

(defun putnam-2008-b5-affine-witness-failure-function
    (function slope)
  (list
   'lambda
   '(integer)
   (list
    'if
    (list 'putnam-2008-b5-affine-solution-with-integer-p
          'integer
          (putnam-2008-b5-quoted function)
          (putnam-2008-b5-quoted slope))
    (putnam-2008-b5-quoted nil)
    (putnam-2008-b5-quoted t))))

(defun putnam-2008-b5-affine-witness-exists-p
    (function slope)
  (not
   (fn-equal
    (putnam-2008-b5-affine-witness-failure-function
     function slope)
    (putnam-2008-b5-true-function '(integer)))))

(defun putnam-2008-b5-solution-p (function)
  (and
   (putnam-2008-b5-real-function-p function)
   (or
    (putnam-2008-b5-affine-witness-exists-p
     function 1)
    (putnam-2008-b5-affine-witness-exists-p
     function -1))))

(defun putnambench-putnam-2008-b5-statement (function)
  (let ((hypothesis
         (and
          (putnam-2008-b5-continuously-differentiable-p
           function)
          (putnam-2008-b5-denominator-property-p
           function)))
        (classification
         (putnam-2008-b5-solution-p function)))
    (equal
     (if hypothesis t nil)
     (if classification t nil))))

(value-triple :itpeval-statement-checked)
:q
