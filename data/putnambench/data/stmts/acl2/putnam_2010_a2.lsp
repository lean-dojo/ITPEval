;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_a2:
;; differentiable real functions satisfying the positive-integer
;; difference-quotient identity are exactly the affine functions. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, and real functions are extensional
;; ACL2 function objects on those names. Positive rational tolerances and
;; radii are cofinal in the positive reals. The derivative, its epsilon-delta
;; radii, and the two affine coefficients are all internally quantified by
;; negated FN-EQUAL tests; none is an additional parameter of the statement.
;;
;; Differentiability is expressed using every real base point and every
;; nonzero rational increment. Continuity is included in the same internal
;; witness; it follows from source differentiability, and it makes convergence
;; along the dense rational increments equivalent to the full real derivative
;; limit. Thus the Boolean equality in the final predicate is the source
;; biconditional for each arbitrary function R -> R.

(defun putnam-2010-a2-quoted (object)
  (list 'quote object))

(defun putnam-2010-a2-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2010-a2-term-list (cdr terms)))
    nil))

(defun putnam-2010-a2-apply-term (function arguments)
  (list 'apply$
        (putnam-2010-a2-quoted function)
        (putnam-2010-a2-term-list arguments)))

(defun putnam-2010-a2-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2010-a2-term-list arguments)))

(defun putnam-2010-a2-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2010-a2-and-terms (cdr terms))
            (putnam-2010-a2-quoted nil))
    (putnam-2010-a2-quoted t)))

(defun putnam-2010-a2-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2010-a2-quoted t)))

(defun putnam-2010-a2-not-term (term)
  (list 'if
        term
        (putnam-2010-a2-quoted nil)
        (putnam-2010-a2-quoted t)))

(defun putnam-2010-a2-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2010-a2-negate-term (value)
  (list 'unary-- value))

(defun putnam-2010-a2-subtract-term (left right)
  (putnam-2010-a2-add-term
   left
   (putnam-2010-a2-negate-term right)))

(defun putnam-2010-a2-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2010-a2-divide-term (numerator denominator)
  (putnam-2010-a2-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2010-a2-absolute-term (value)
  (list 'if
        (list '< value (putnam-2010-a2-quoted 0))
        (putnam-2010-a2-negate-term value)
        value))

(defun putnam-2010-a2-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2010-a2-quoted nil)
        (putnam-2010-a2-quoted t)))

(defun putnam-2010-a2-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-2010-a2-positive-rational-term (value)
  (putnam-2010-a2-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2010-a2-quoted 0) value))))

(defun putnam-2010-a2-true-function (formals)
  (list 'lambda
        formals
        (putnam-2010-a2-quoted t)))

(defun putnam-2010-a2-real-value-term (name precision)
  (putnam-2010-a2-apply-term name (list precision)))

(defun putnam-2010-a2-object-real-value-term
    (name-term precision)
  (putnam-2010-a2-apply-object-term
   name-term
   (list precision)))

(defun putnam-2010-a2-real-cauchy-function (name)
  (let* ((left
          (putnam-2010-a2-real-value-term name 'epsilon))
         (right
          (putnam-2010-a2-real-value-term name 'eta))
         (distance
          (putnam-2010-a2-absolute-term
           (putnam-2010-a2-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2010-a2-implies-term
      (putnam-2010-a2-and-terms
       (list
        (putnam-2010-a2-positive-rational-term 'epsilon)
        (putnam-2010-a2-positive-rational-term 'eta)))
      (putnam-2010-a2-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2010-a2-less-equal-term
         distance
         (putnam-2010-a2-add-term
          'epsilon 'eta))))))))

(defun putnam-2010-a2-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2010-a2-real-cauchy-function name)
    (putnam-2010-a2-true-function
     '(epsilon eta)))))

;; Sampling both names at eta/4 makes the universal inequality equivalent to
;; the represented real distance being at most BOUND.
(defun putnam-2010-a2-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2010-a2-multiply-term
           (putnam-2010-a2-quoted 1/4)
           'eta))
         (left
          (putnam-2010-a2-real-value-term
           left-name precision))
         (right
          (putnam-2010-a2-real-value-term
           right-name precision))
         (distance
          (putnam-2010-a2-absolute-term
           (putnam-2010-a2-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2010-a2-implies-term
      (putnam-2010-a2-positive-rational-term 'eta)
      (putnam-2010-a2-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2010-a2-less-equal-term
         distance
         (putnam-2010-a2-add-term
          (putnam-2010-a2-quoted bound)
          'eta))))))))

(defun putnam-2010-a2-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2010-a2-real-name-p left-name)
   (putnam-2010-a2-real-name-p right-name)
   (fn-equal
    (putnam-2010-a2-real-distance-function
     left-name right-name bound)
    (putnam-2010-a2-true-function '(eta)))))

(defun putnam-2010-a2-real-equal-p
    (left-name right-name)
  (putnam-2010-a2-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2010-a2-unary-output-function
    (function)
  (let ((output
         (putnam-2010-a2-apply-term function (list 'x))))
    (list
     'lambda
     '(x)
     (putnam-2010-a2-implies-term
      (list 'putnam-2010-a2-real-name-p 'x)
      (list 'putnam-2010-a2-real-name-p output)))))

(defun putnam-2010-a2-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-2010-a2-apply-term
          function (list 'x-left)))
        (right-output
         (putnam-2010-a2-apply-term
          function (list 'x-right))))
    (list
     'lambda
     '(x-left x-right)
     (putnam-2010-a2-implies-term
      (list 'putnam-2010-a2-real-equal-p
            'x-left 'x-right)
      (list 'putnam-2010-a2-real-equal-p
            left-output right-output)))))

(defun putnam-2010-a2-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2010-a2-unary-output-function function)
    (putnam-2010-a2-true-function '(x)))
   (fn-equal
    (putnam-2010-a2-unary-extensional-function function)
    (putnam-2010-a2-true-function
     '(x-left x-right)))))

(defun putnam-2010-a2-rational-shift-name (name shift)
  (let ((value
         (putnam-2010-a2-object-real-value-term
          (putnam-2010-a2-quoted name)
          (putnam-2010-a2-multiply-term
           (putnam-2010-a2-quoted 1/2)
           'precision))))
    (list
     'lambda
     '(precision)
     (putnam-2010-a2-add-term
      value
      (putnam-2010-a2-quoted shift)))))

;; Continuity is stated using closed rational radii. Rescaling epsilon and
;; delta gives the usual open-ball definition in both directions.
(defun putnam-2010-a2-continuous-at-delta-function
    (function x epsilon delta)
  (let ((at-x
         (putnam-2010-a2-apply-term
          function
          (list (putnam-2010-a2-quoted x))))
        (at-y
         (putnam-2010-a2-apply-term
          function
          (list 'y))))
    (list
     'lambda
     '(y)
     (putnam-2010-a2-implies-term
      (putnam-2010-a2-and-terms
       (list
        (list 'putnam-2010-a2-real-name-p 'y)
        (list 'putnam-2010-a2-real-distance-at-most-p
              (putnam-2010-a2-quoted x)
              'y
              (putnam-2010-a2-quoted delta))))
      (list 'putnam-2010-a2-real-distance-at-most-p
            at-x
            at-y
            (putnam-2010-a2-quoted epsilon))))))

(defun putnam-2010-a2-continuous-at-delta-p
    (function x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2010-a2-continuous-at-delta-function
     function x epsilon delta)
    (putnam-2010-a2-true-function '(y)))))

(defun putnam-2010-a2-continuity-delta-failure-function
    (function x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2010-a2-continuous-at-delta-p
          (putnam-2010-a2-quoted function)
          (putnam-2010-a2-quoted x)
          (putnam-2010-a2-quoted epsilon)
          'delta)
    (putnam-2010-a2-quoted nil)
    (putnam-2010-a2-quoted t))))

(defun putnam-2010-a2-continuity-delta-exists-p
    (function x epsilon)
  (not
   (fn-equal
    (putnam-2010-a2-continuity-delta-failure-function
     function x epsilon)
    (putnam-2010-a2-true-function '(delta)))))

(defun putnam-2010-a2-continuity-function (function)
  (list
   'lambda
   '(x epsilon)
   (putnam-2010-a2-implies-term
    (putnam-2010-a2-and-terms
     (list
      (list 'putnam-2010-a2-real-name-p 'x)
      (putnam-2010-a2-positive-rational-term 'epsilon)))
    (list 'putnam-2010-a2-continuity-delta-exists-p
          (putnam-2010-a2-quoted function)
          'x
          'epsilon))))

(defun putnam-2010-a2-continuous-p (function)
  (and
   (putnam-2010-a2-real-function-p function)
   (fn-equal
    (putnam-2010-a2-continuity-function function)
    (putnam-2010-a2-true-function
     '(x epsilon)))))

;; At precision eta, each numerator value is sampled at |h|*eta/4, so this is
;; a regular Cauchy name for (f(x+h)-f(x))/h when h is a nonzero rational.
(defun putnam-2010-a2-difference-quotient-name
    (function x h)
  (let* ((shifted-x
          (putnam-2010-a2-rational-shift-name x h))
         (at-shifted-x
          (putnam-2010-a2-apply-term
           function
           (list (putnam-2010-a2-quoted shifted-x))))
         (at-x
          (putnam-2010-a2-apply-term
           function
           (list (putnam-2010-a2-quoted x))))
         (sample-precision
          (putnam-2010-a2-multiply-term
           (putnam-2010-a2-quoted (/ (abs h) 4))
           'eta))
         (shifted-value
          (putnam-2010-a2-object-real-value-term
           at-shifted-x sample-precision))
         (value
          (putnam-2010-a2-object-real-value-term
           at-x sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-2010-a2-divide-term
      (putnam-2010-a2-subtract-term
       shifted-value value)
      (putnam-2010-a2-quoted h)))))

(defun putnam-2010-a2-derivative-at-delta-function
    (function derivative x epsilon delta)
  (let ((quotient
         (list 'putnam-2010-a2-difference-quotient-name
               (putnam-2010-a2-quoted function)
               (putnam-2010-a2-quoted x)
               'h))
        (derivative-at-x
         (putnam-2010-a2-apply-term
          derivative
          (list (putnam-2010-a2-quoted x)))))
    (list
     'lambda
     '(h)
     (putnam-2010-a2-implies-term
      (putnam-2010-a2-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-2010-a2-not-term
         (list 'equal 'h (putnam-2010-a2-quoted 0)))
        (putnam-2010-a2-less-equal-term
         (putnam-2010-a2-absolute-term 'h)
         (putnam-2010-a2-quoted delta))))
      (list 'putnam-2010-a2-real-distance-at-most-p
            quotient
            derivative-at-x
            (putnam-2010-a2-quoted epsilon))))))

(defun putnam-2010-a2-derivative-at-delta-p
    (function derivative x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2010-a2-derivative-at-delta-function
     function derivative x epsilon delta)
    (putnam-2010-a2-true-function '(h)))))

(defun putnam-2010-a2-derivative-delta-failure-function
    (function derivative x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2010-a2-derivative-at-delta-p
          (putnam-2010-a2-quoted function)
          (putnam-2010-a2-quoted derivative)
          (putnam-2010-a2-quoted x)
          (putnam-2010-a2-quoted epsilon)
          'delta)
    (putnam-2010-a2-quoted nil)
    (putnam-2010-a2-quoted t))))

(defun putnam-2010-a2-derivative-delta-exists-p
    (function derivative x epsilon)
  (not
   (fn-equal
    (putnam-2010-a2-derivative-delta-failure-function
     function derivative x epsilon)
    (putnam-2010-a2-true-function '(delta)))))

(defun putnam-2010-a2-derivative-function
    (function derivative)
  (list
   'lambda
   '(x epsilon)
   (putnam-2010-a2-implies-term
    (putnam-2010-a2-and-terms
     (list
      (list 'putnam-2010-a2-real-name-p 'x)
      (putnam-2010-a2-positive-rational-term 'epsilon)))
    (list 'putnam-2010-a2-derivative-delta-exists-p
          (putnam-2010-a2-quoted function)
          (putnam-2010-a2-quoted derivative)
          'x
          'epsilon))))

(defun putnam-2010-a2-derivative-relation-p
    (function derivative)
  (and
   (putnam-2010-a2-real-function-p function)
   (putnam-2010-a2-real-function-p derivative)
   (fn-equal
    (putnam-2010-a2-derivative-function
     function derivative)
    (putnam-2010-a2-true-function
     '(x epsilon)))))

(defun putnam-2010-a2-difference-equation-function
    (function derivative)
  (let ((derivative-at-x
         (putnam-2010-a2-apply-term
          derivative (list 'x)))
        (finite-difference
         (list 'putnam-2010-a2-difference-quotient-name
               (putnam-2010-a2-quoted function)
               'x
               'n)))
    (list
     'lambda
     '(x n)
     (putnam-2010-a2-implies-term
      (putnam-2010-a2-and-terms
       (list
        (list 'putnam-2010-a2-real-name-p 'x)
        (list 'integerp 'n)
        (list '< (putnam-2010-a2-quoted 0) 'n)))
      (list 'putnam-2010-a2-real-equal-p
            derivative-at-x
            finite-difference)))))

(defun putnam-2010-a2-difference-equation-p
    (function derivative)
  (fn-equal
   (putnam-2010-a2-difference-equation-function
    function derivative)
   (putnam-2010-a2-true-function '(x n))))

(defun putnam-2010-a2-hypothesis-witness-p
    (derivative function)
  (and
   (putnam-2010-a2-continuous-p function)
   (putnam-2010-a2-derivative-relation-p
    function derivative)
   (putnam-2010-a2-difference-equation-p
    function derivative)))

(defun putnam-2010-a2-hypothesis-witness-failure-function
    (function)
  (list
   'lambda
   '(derivative)
   (list
    'if
    (list 'putnam-2010-a2-hypothesis-witness-p
          'derivative
          (putnam-2010-a2-quoted function))
    (putnam-2010-a2-quoted nil)
    (putnam-2010-a2-quoted t))))

(defun putnam-2010-a2-hypothesis-p (function)
  (let ((failure-function
         (putnam-2010-a2-hypothesis-witness-failure-function
          function))
        (true-function
         (putnam-2010-a2-true-function '(derivative))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

;; This name denotes slope*x+intercept. Coarse samples bound the product
;; factors, and the adaptive precision makes the resulting rational sequence
;; a regular Cauchy name for the exact real affine value.
(defun putnam-2010-a2-affine-name
    (slope intercept x)
  (let* ((slope-coarse
          (putnam-2010-a2-object-real-value-term
           (putnam-2010-a2-quoted slope)
           (putnam-2010-a2-quoted 1)))
         (x-coarse
          (putnam-2010-a2-object-real-value-term
           (putnam-2010-a2-quoted x)
           (putnam-2010-a2-quoted 1)))
         (scale
          (putnam-2010-a2-multiply-term
           (putnam-2010-a2-quoted 64)
           (putnam-2010-a2-add-term
            (putnam-2010-a2-quoted 1)
            (putnam-2010-a2-add-term
             (putnam-2010-a2-absolute-term slope-coarse)
             (putnam-2010-a2-absolute-term x-coarse)))))
         (factor-precision
          (putnam-2010-a2-minimum-term
           (putnam-2010-a2-quoted 1)
           (putnam-2010-a2-divide-term
            'precision scale)))
         (intercept-precision
          (putnam-2010-a2-minimum-term
           (putnam-2010-a2-quoted 1)
           (putnam-2010-a2-multiply-term
            (putnam-2010-a2-quoted 1/8)
            'precision)))
         (slope-value
          (putnam-2010-a2-object-real-value-term
           (putnam-2010-a2-quoted slope)
           factor-precision))
         (x-value
          (putnam-2010-a2-object-real-value-term
           (putnam-2010-a2-quoted x)
           factor-precision))
         (intercept-value
          (putnam-2010-a2-object-real-value-term
           (putnam-2010-a2-quoted intercept)
           intercept-precision)))
    (list
     'lambda
     '(precision)
     (putnam-2010-a2-add-term
      (putnam-2010-a2-multiply-term
       slope-value x-value)
      intercept-value))))

(defun putnam-2010-a2-affine-solution-function
    (function slope intercept)
  (let ((actual
         (putnam-2010-a2-apply-term
          function (list 'x)))
        (expected
         (list 'putnam-2010-a2-affine-name
               (putnam-2010-a2-quoted slope)
               (putnam-2010-a2-quoted intercept)
               'x)))
    (list
     'lambda
     '(x)
     (putnam-2010-a2-implies-term
      (list 'putnam-2010-a2-real-name-p 'x)
      (list 'putnam-2010-a2-real-equal-p
            actual expected)))))

(defun putnam-2010-a2-affine-witness-p
    (slope intercept function)
  (and
   (putnam-2010-a2-real-name-p slope)
   (putnam-2010-a2-real-name-p intercept)
   (putnam-2010-a2-real-function-p function)
   (fn-equal
    (putnam-2010-a2-affine-solution-function
     function slope intercept)
    (putnam-2010-a2-true-function '(x)))))

(defun putnam-2010-a2-affine-witness-failure-function
    (function)
  (list
   'lambda
   '(slope intercept)
   (list
    'if
    (list 'putnam-2010-a2-affine-witness-p
          'slope
          'intercept
          (putnam-2010-a2-quoted function))
    (putnam-2010-a2-quoted nil)
    (putnam-2010-a2-quoted t))))

(defun putnam-2010-a2-affine-solution-p (function)
  (let ((failure-function
         (putnam-2010-a2-affine-witness-failure-function
          function))
        (true-function
         (putnam-2010-a2-true-function
          '(slope intercept))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2010-a2-statement (function)
  (equal
   (if (putnam-2010-a2-hypothesis-p function)
       t
     nil)
   (if (putnam-2010-a2-affine-solution-p function)
       t
     nil)))

(value-triple :itpeval-statement-checked)
:q
