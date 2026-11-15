;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_a6:
;; a twice differentiable real function that is small relative to x^r at zero
;; has either derivative tending to zero or unbounded scaled second derivative
;; near zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, and real functions are extensional
;; function objects on those names. Positive rational tolerances, thresholds,
;; and moduli are cofinal in the positive reals. All derivative, power, limit,
;; and supremum witnesses remain internally quantified.

(defun putnam-2019-a6-quoted (object)
  (list 'quote object))

(defun putnam-2019-a6-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2019-a6-term-list (cdr terms)))
    nil))

(defun putnam-2019-a6-apply-term (function arguments)
  (list 'apply$
        (putnam-2019-a6-quoted function)
        (putnam-2019-a6-term-list arguments)))

(defun putnam-2019-a6-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2019-a6-term-list arguments)))

(defun putnam-2019-a6-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2019-a6-and-terms (cdr terms))
            (putnam-2019-a6-quoted nil))
    (putnam-2019-a6-quoted t)))

(defun putnam-2019-a6-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2019-a6-quoted t)))

(defun putnam-2019-a6-not-term (term)
  (list 'if
        term
        (putnam-2019-a6-quoted nil)
        (putnam-2019-a6-quoted t)))

(defun putnam-2019-a6-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2019-a6-negate-term (value)
  (list 'unary-- value))

(defun putnam-2019-a6-subtract-term (left right)
  (putnam-2019-a6-add-term
   left
   (putnam-2019-a6-negate-term right)))

(defun putnam-2019-a6-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2019-a6-divide-term (numerator denominator)
  (putnam-2019-a6-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2019-a6-absolute-term (value)
  (list 'if
        (list '< value (putnam-2019-a6-quoted 0))
        (putnam-2019-a6-negate-term value)
        value))

(defun putnam-2019-a6-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2019-a6-quoted nil)
        (putnam-2019-a6-quoted t)))

(defun putnam-2019-a6-positive-rational-term (value)
  (putnam-2019-a6-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2019-a6-quoted 0) value))))

(defun putnam-2019-a6-true-function (formals)
  (list 'lambda
        formals
        (putnam-2019-a6-quoted t)))

(defun putnam-2019-a6-real-value-term (name precision)
  (putnam-2019-a6-apply-term name (list precision)))

(defun putnam-2019-a6-object-real-value-term
    (name-term precision)
  (putnam-2019-a6-apply-object-term
   name-term
   (list precision)))

(defun putnam-2019-a6-real-cauchy-function (name)
  (let* ((left
          (putnam-2019-a6-real-value-term name 'epsilon))
         (right
          (putnam-2019-a6-real-value-term name 'eta))
         (distance
          (putnam-2019-a6-absolute-term
           (putnam-2019-a6-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (putnam-2019-a6-positive-rational-term 'epsilon)
        (putnam-2019-a6-positive-rational-term 'eta)))
      (putnam-2019-a6-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2019-a6-less-equal-term
         distance
         (putnam-2019-a6-add-term
          'epsilon 'eta))))))))

(defun putnam-2019-a6-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2019-a6-real-cauchy-function name)
    (putnam-2019-a6-true-function
     '(epsilon eta)))))

;; Sampling both names at eta/4 makes the displayed universal inequality
;; equivalent to distance between their represented limits being at most BOUND.

(defun putnam-2019-a6-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2019-a6-multiply-term
           (putnam-2019-a6-quoted 1/4)
           'eta))
         (left
          (putnam-2019-a6-real-value-term
           left-name precision))
         (right
          (putnam-2019-a6-real-value-term
           right-name precision))
         (distance
          (putnam-2019-a6-absolute-term
           (putnam-2019-a6-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-positive-rational-term 'eta)
      (putnam-2019-a6-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2019-a6-less-equal-term
         distance
         (putnam-2019-a6-add-term
          (putnam-2019-a6-quoted bound)
          'eta))))))))

(defun putnam-2019-a6-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2019-a6-real-name-p left-name)
   (putnam-2019-a6-real-name-p right-name)
   (fn-equal
    (putnam-2019-a6-real-distance-function
     left-name right-name bound)
    (putnam-2019-a6-true-function '(eta)))))

(defun putnam-2019-a6-real-equal-p
    (left-name right-name)
  (putnam-2019-a6-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2019-a6-real-order-function
    (left-name right-name)
  (let* ((precision
          (putnam-2019-a6-multiply-term
           (putnam-2019-a6-quoted 1/4)
           'eta))
         (left
          (putnam-2019-a6-real-value-term
           left-name precision))
         (right
          (putnam-2019-a6-real-value-term
           right-name precision)))
    (list
     'lambda
     '(eta)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-positive-rational-term 'eta)
      (putnam-2019-a6-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2019-a6-less-equal-term
         left
         (putnam-2019-a6-add-term
          right 'eta))))))))

(defun putnam-2019-a6-real-le-p
    (left-name right-name)
  (and
   (putnam-2019-a6-real-name-p left-name)
   (putnam-2019-a6-real-name-p right-name)
   (fn-equal
    (putnam-2019-a6-real-order-function
     left-name right-name)
    (putnam-2019-a6-true-function '(eta)))))

(defun putnam-2019-a6-real-lt-p
    (left-name right-name)
  (and
   (putnam-2019-a6-real-le-p left-name right-name)
   (not
    (putnam-2019-a6-real-equal-p
     left-name right-name))))

(defun putnam-2019-a6-unary-output-function
    (function)
  (let ((output
         (putnam-2019-a6-apply-term function (list 'x))))
    (list
     'lambda
     '(x)
     (putnam-2019-a6-implies-term
      (list 'putnam-2019-a6-real-name-p 'x)
      (list 'putnam-2019-a6-real-name-p output)))))

(defun putnam-2019-a6-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-2019-a6-apply-term
          function (list 'x-left)))
        (right-output
         (putnam-2019-a6-apply-term
          function (list 'x-right))))
    (list
     'lambda
     '(x-left x-right)
     (putnam-2019-a6-implies-term
      (list 'putnam-2019-a6-real-equal-p
            'x-left 'x-right)
      (list 'putnam-2019-a6-real-equal-p
            left-output right-output)))))

(defun putnam-2019-a6-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2019-a6-unary-output-function function)
    (putnam-2019-a6-true-function '(x)))
   (fn-equal
    (putnam-2019-a6-unary-extensional-function function)
    (putnam-2019-a6-true-function
     '(x-left x-right)))))

(defun putnam-2019-a6-rational-name (value)
  (list 'lambda
        '(precision)
        (putnam-2019-a6-quoted value)))

(defun putnam-2019-a6-add-name
    (left-name right-name)
  (let* ((precision
          (putnam-2019-a6-multiply-term
           (putnam-2019-a6-quoted 1/2)
           'epsilon))
         (left
          (putnam-2019-a6-object-real-value-term
           (putnam-2019-a6-quoted left-name)
           precision))
         (right
          (putnam-2019-a6-object-real-value-term
           (putnam-2019-a6-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2019-a6-add-term left right))))

(defun putnam-2019-a6-multiply-name
    (left-name right-name)
  (let* ((left-at-one
          (putnam-2019-a6-object-real-value-term
           (putnam-2019-a6-quoted left-name)
           (putnam-2019-a6-quoted 1)))
         (right-at-one
          (putnam-2019-a6-object-real-value-term
           (putnam-2019-a6-quoted right-name)
           (putnam-2019-a6-quoted 1)))
         (scale
          (putnam-2019-a6-multiply-term
           (putnam-2019-a6-quoted 8)
           (putnam-2019-a6-add-term
            (putnam-2019-a6-quoted 3)
            (putnam-2019-a6-add-term
             (putnam-2019-a6-absolute-term left-at-one)
             (putnam-2019-a6-absolute-term right-at-one)))))
         (candidate
          (putnam-2019-a6-divide-term
           'epsilon scale))
         (precision
          (list 'if
                (list '<
                      (putnam-2019-a6-quoted 1)
                      candidate)
                (putnam-2019-a6-quoted 1)
                candidate))
         (left
          (putnam-2019-a6-object-real-value-term
           (putnam-2019-a6-quoted left-name)
           precision))
         (right
          (putnam-2019-a6-object-real-value-term
           (putnam-2019-a6-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2019-a6-multiply-term left right))))

(defun putnam-2019-a6-absolute-name (name)
  (let ((value
         (putnam-2019-a6-object-real-value-term
          (putnam-2019-a6-quoted name)
          'epsilon)))
    (list
     'lambda
     '(epsilon)
     (putnam-2019-a6-absolute-term value))))

(defun putnam-2019-a6-rational-shift-name (name shift)
  (let ((value
         (putnam-2019-a6-object-real-value-term
          (putnam-2019-a6-quoted name)
          (putnam-2019-a6-multiply-term
           (putnam-2019-a6-quoted 1/2)
           'precision))))
    (list
     'lambda
     '(precision)
     (putnam-2019-a6-add-term
      value
      (putnam-2019-a6-quoted shift)))))

(defun putnam-2019-a6-in-closed-unit-p (x)
  (and
   (putnam-2019-a6-real-name-p x)
   (putnam-2019-a6-real-le-p
    (putnam-2019-a6-rational-name 0)
    x)
   (putnam-2019-a6-real-le-p
    x
    (putnam-2019-a6-rational-name 1))))

(defun putnam-2019-a6-in-open-unit-p (x)
  (and
   (putnam-2019-a6-real-name-p x)
   (putnam-2019-a6-real-lt-p
    (putnam-2019-a6-rational-name 0)
    x)
   (putnam-2019-a6-real-lt-p
    x
    (putnam-2019-a6-rational-name 1))))

;; Continuity is stated with closed rational balls and non-strict output
;; bounds. Rescaling epsilon and delta gives the usual open-ball definition in
;; both directions.

(defun putnam-2019-a6-continuous-at-delta-function
    (function x epsilon delta closedp)
  (let ((domain-predicate
         (if closedp
             'putnam-2019-a6-in-closed-unit-p
           'putnam-2019-a6-in-open-unit-p))
        (at-x
         (putnam-2019-a6-apply-term
          function
          (list (putnam-2019-a6-quoted x))))
        (at-y
         (putnam-2019-a6-apply-term
          function
          (list 'y))))
    (list
     'lambda
     '(y)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (list domain-predicate 'y)
        (list 'putnam-2019-a6-real-distance-at-most-p
              (putnam-2019-a6-quoted x)
              'y
              (putnam-2019-a6-quoted delta))))
      (list 'putnam-2019-a6-real-distance-at-most-p
            at-x
            at-y
            (putnam-2019-a6-quoted epsilon))))))

(defun putnam-2019-a6-continuous-at-delta-p
    (function x epsilon delta closedp)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2019-a6-continuous-at-delta-function
     function x epsilon delta closedp)
    (putnam-2019-a6-true-function '(y)))))

(defun putnam-2019-a6-continuity-delta-failure-function
    (function x epsilon closedp)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2019-a6-continuous-at-delta-p
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted x)
          (putnam-2019-a6-quoted epsilon)
          'delta
          (putnam-2019-a6-quoted closedp))
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-continuity-delta-exists-p
    (function x epsilon closedp)
  (not
   (fn-equal
    (putnam-2019-a6-continuity-delta-failure-function
     function x epsilon closedp)
    (putnam-2019-a6-true-function '(delta)))))

(defun putnam-2019-a6-continuity-function
    (function closedp)
  (let ((domain-predicate
         (if closedp
             'putnam-2019-a6-in-closed-unit-p
           'putnam-2019-a6-in-open-unit-p)))
    (list
     'lambda
     '(x epsilon)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (list domain-predicate 'x)
        (putnam-2019-a6-positive-rational-term 'epsilon)))
      (list 'putnam-2019-a6-continuity-delta-exists-p
            (putnam-2019-a6-quoted function)
            'x
            'epsilon
            (putnam-2019-a6-quoted closedp))))))

(defun putnam-2019-a6-continuous-on-p
    (function closedp)
  (and
   (putnam-2019-a6-real-function-p function)
   (fn-equal
    (putnam-2019-a6-continuity-function
     function closedp)
    (putnam-2019-a6-true-function
     '(x epsilon)))))

;; At precision eta, each numerator value below is sampled at
;; |h|*eta/4. Hence the quotient is a regular Cauchy name for
;; (f(x+h)-f(x))/h whenever h is a nonzero rational.

(defun putnam-2019-a6-difference-quotient-name
    (function x h)
  (let* ((shifted-x
          (putnam-2019-a6-rational-shift-name x h))
         (at-shifted-x
          (putnam-2019-a6-apply-term
           function
           (list (putnam-2019-a6-quoted shifted-x))))
         (at-x
          (putnam-2019-a6-apply-term
           function
           (list (putnam-2019-a6-quoted x))))
         (sample-precision
          (putnam-2019-a6-multiply-term
           (putnam-2019-a6-quoted (/ (abs h) 4))
           'eta))
         (shifted-value
          (putnam-2019-a6-object-real-value-term
           at-shifted-x sample-precision))
         (value
          (putnam-2019-a6-object-real-value-term
           at-x sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-2019-a6-divide-term
      (putnam-2019-a6-subtract-term
       shifted-value value)
      (putnam-2019-a6-quoted h)))))

(defun putnam-2019-a6-derivative-at-delta-function
    (function derivative x epsilon delta)
  (let ((shifted-x
         (list 'putnam-2019-a6-rational-shift-name
               (putnam-2019-a6-quoted x)
               'h))
        (quotient
         (list 'putnam-2019-a6-difference-quotient-name
               (putnam-2019-a6-quoted function)
               (putnam-2019-a6-quoted x)
               'h))
        (derivative-at-x
         (putnam-2019-a6-apply-term
          derivative
          (list (putnam-2019-a6-quoted x)))))
    (list
     'lambda
     '(h)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-2019-a6-not-term
         (list 'equal 'h (putnam-2019-a6-quoted 0)))
        (list 'putnam-2019-a6-in-open-unit-p
              shifted-x)
        (putnam-2019-a6-less-equal-term
         (putnam-2019-a6-absolute-term 'h)
         (putnam-2019-a6-quoted delta))))
      (list 'putnam-2019-a6-real-distance-at-most-p
            quotient
            derivative-at-x
            (putnam-2019-a6-quoted epsilon))))))

(defun putnam-2019-a6-derivative-at-delta-p
    (function derivative x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2019-a6-derivative-at-delta-function
     function derivative x epsilon delta)
    (putnam-2019-a6-true-function '(h)))))

(defun putnam-2019-a6-derivative-delta-failure-function
    (function derivative x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2019-a6-derivative-at-delta-p
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted derivative)
          (putnam-2019-a6-quoted x)
          (putnam-2019-a6-quoted epsilon)
          'delta)
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-derivative-delta-exists-p
    (function derivative x epsilon)
  (not
   (fn-equal
    (putnam-2019-a6-derivative-delta-failure-function
     function derivative x epsilon)
    (putnam-2019-a6-true-function '(delta)))))

(defun putnam-2019-a6-derivative-function
    (function derivative)
  (list
   'lambda
   '(x epsilon)
    (putnam-2019-a6-implies-term
     (putnam-2019-a6-and-terms
      (list
       (list 'putnam-2019-a6-in-open-unit-p 'x)
       (putnam-2019-a6-positive-rational-term 'epsilon)))
     (list 'putnam-2019-a6-derivative-delta-exists-p
           (putnam-2019-a6-quoted function)
           (putnam-2019-a6-quoted derivative)
           'x
           'epsilon))))

(defun putnam-2019-a6-derivative-on-open-p
    (function derivative)
  (and
   (putnam-2019-a6-real-function-p function)
   (putnam-2019-a6-real-function-p derivative)
   (fn-equal
    (putnam-2019-a6-derivative-function
     function derivative)
    (putnam-2019-a6-true-function
     '(x epsilon)))))

(defun putnam-2019-a6-power-output-function (power)
  (let ((zero-name
         (putnam-2019-a6-rational-name 0))
        (output
         (putnam-2019-a6-apply-term
          power
          (list 'base 'exponent))))
    (list
     'lambda
     '(base exponent)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (list 'putnam-2019-a6-real-name-p 'base)
        (list 'putnam-2019-a6-real-name-p 'exponent)
        (list 'putnam-2019-a6-real-lt-p
              (putnam-2019-a6-quoted zero-name)
              'base)))
      (list 'putnam-2019-a6-real-name-p output)))))

(defun putnam-2019-a6-power-extensional-function
    (power)
  (let ((zero-name
         (putnam-2019-a6-rational-name 0))
        (left-output
         (putnam-2019-a6-apply-term
          power
          (list 'base-left 'exponent-left)))
        (right-output
         (putnam-2019-a6-apply-term
          power
          (list 'base-right 'exponent-right))))
    (list
     'lambda
     '(base-left base-right exponent-left exponent-right)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (list 'putnam-2019-a6-real-lt-p
              (putnam-2019-a6-quoted zero-name)
              'base-left)
        (list 'putnam-2019-a6-real-equal-p
              'base-left 'base-right)
        (list 'putnam-2019-a6-real-equal-p
              'exponent-left 'exponent-right)))
      (list 'putnam-2019-a6-real-equal-p
            left-output right-output)))))

(defun putnam-2019-a6-power-law-function (power)
  (let* ((zero-name
          (putnam-2019-a6-rational-name 0))
         (one-name
          (putnam-2019-a6-rational-name 1))
         (at-left
          (putnam-2019-a6-apply-term
           power
           (list 'base 'exponent-left)))
         (at-right
          (putnam-2019-a6-apply-term
           power
           (list 'base 'exponent-right)))
         (at-zero
          (putnam-2019-a6-apply-term
           power
           (list 'base
                 (putnam-2019-a6-quoted zero-name))))
         (at-one
          (putnam-2019-a6-apply-term
           power
           (list 'base
                 (putnam-2019-a6-quoted one-name))))
         (sum-name
          (list 'putnam-2019-a6-add-name
                'exponent-left
                'exponent-right))
         (at-sum
          (putnam-2019-a6-apply-term
           power
           (list 'base sum-name)))
         (product-name
          (list 'putnam-2019-a6-multiply-name
                at-left at-right)))
    (list
     'lambda
     '(base exponent-left exponent-right)
     (putnam-2019-a6-implies-term
      (putnam-2019-a6-and-terms
       (list
        (list 'putnam-2019-a6-real-lt-p
              (putnam-2019-a6-quoted zero-name)
              'base)
        (list 'putnam-2019-a6-real-name-p
              'exponent-left)
        (list 'putnam-2019-a6-real-name-p
              'exponent-right)))
      (putnam-2019-a6-and-terms
       (list
        (list 'putnam-2019-a6-real-lt-p
              (putnam-2019-a6-quoted zero-name)
              at-left)
        (list 'putnam-2019-a6-real-equal-p
              at-zero
              (putnam-2019-a6-quoted one-name))
        (list 'putnam-2019-a6-real-equal-p
              at-one
              'base)
        (list 'putnam-2019-a6-real-equal-p
              at-sum product-name)
        (putnam-2019-a6-implies-term
         (putnam-2019-a6-and-terms
          (list
           (list 'putnam-2019-a6-real-le-p
                 (putnam-2019-a6-quoted one-name)
                 'base)
           (list 'putnam-2019-a6-real-le-p
                 'exponent-left 'exponent-right)))
         (list 'putnam-2019-a6-real-le-p
               at-left at-right))
        (putnam-2019-a6-implies-term
         (putnam-2019-a6-and-terms
          (list
           (list 'putnam-2019-a6-real-le-p
                 'base
                 (putnam-2019-a6-quoted one-name))
           (list 'putnam-2019-a6-real-le-p
                 'exponent-left 'exponent-right)))
         (list 'putnam-2019-a6-real-le-p
               at-right at-left))))))))

(defun putnam-2019-a6-power-oracle-p (power)
  (and
   (tamep-functionp power)
   (fn-equal
    (putnam-2019-a6-power-output-function power)
    (putnam-2019-a6-true-function
     '(base exponent)))
   (fn-equal
    (putnam-2019-a6-power-extensional-function
     power)
    (putnam-2019-a6-true-function
     '(base-left base-right
       exponent-left exponent-right)))
   (fn-equal
    (putnam-2019-a6-power-law-function power)
    (putnam-2019-a6-true-function
     '(base exponent-left exponent-right)))))

(defun putnam-2019-a6-in-right-neighborhood-p
    (x delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-2019-a6-real-name-p x)
   (putnam-2019-a6-real-lt-p
    (putnam-2019-a6-rational-name 0)
    x)
   (putnam-2019-a6-real-le-p
    x
    (putnam-2019-a6-rational-name delta))))

(defun putnam-2019-a6-right-limit-zero-delta-function
    (function epsilon delta)
  (let ((value
         (putnam-2019-a6-apply-term
          function (list 'x)))
        (zero-name
         (putnam-2019-a6-rational-name 0)))
    (list
     'lambda
     '(x)
     (putnam-2019-a6-implies-term
      (list 'putnam-2019-a6-in-right-neighborhood-p
            'x
            (putnam-2019-a6-quoted delta))
      (list 'putnam-2019-a6-real-distance-at-most-p
            value
            (putnam-2019-a6-quoted zero-name)
            (putnam-2019-a6-quoted epsilon))))))

(defun putnam-2019-a6-right-limit-zero-delta-p
    (function epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2019-a6-right-limit-zero-delta-function
     function epsilon delta)
    (putnam-2019-a6-true-function '(x)))))

(defun putnam-2019-a6-right-limit-zero-delta-failure-function
    (function epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2019-a6-right-limit-zero-delta-p
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted epsilon)
          'delta)
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-right-limit-zero-delta-exists-p
    (function epsilon)
  (not
   (fn-equal
    (putnam-2019-a6-right-limit-zero-delta-failure-function
     function epsilon)
    (putnam-2019-a6-true-function '(delta)))))

(defun putnam-2019-a6-right-limit-zero-function
    (function)
  (list
   'lambda
   '(epsilon)
   (putnam-2019-a6-implies-term
    (putnam-2019-a6-positive-rational-term
     'epsilon)
    (list 'putnam-2019-a6-right-limit-zero-delta-exists-p
          (putnam-2019-a6-quoted function)
          'epsilon))))

(defun putnam-2019-a6-right-limit-zero-p
    (function)
  (and
   (putnam-2019-a6-real-function-p function)
   (fn-equal
    (putnam-2019-a6-right-limit-zero-function
     function)
    (putnam-2019-a6-true-function '(epsilon)))))

(defun putnam-2019-a6-small-o-delta-function
    (function r power epsilon delta)
  (let* ((value
          (putnam-2019-a6-apply-term
           function (list 'x)))
         (absolute-value
          (list 'putnam-2019-a6-absolute-name
                value))
         (power-value
          (putnam-2019-a6-apply-term
           power
           (list 'x
                 (putnam-2019-a6-quoted r))))
         (epsilon-name
          (putnam-2019-a6-rational-name epsilon))
         (bound
          (list 'putnam-2019-a6-multiply-name
                (putnam-2019-a6-quoted epsilon-name)
                power-value)))
    (list
     'lambda
     '(x)
     (putnam-2019-a6-implies-term
      (list 'putnam-2019-a6-in-right-neighborhood-p
            'x
            (putnam-2019-a6-quoted delta))
      (list 'putnam-2019-a6-real-le-p
            absolute-value bound)))))

(defun putnam-2019-a6-small-o-delta-p
    (function r power epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2019-a6-small-o-delta-function
     function r power epsilon delta)
    (putnam-2019-a6-true-function '(x)))))

(defun putnam-2019-a6-small-o-delta-failure-function
    (function r power epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2019-a6-small-o-delta-p
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted r)
          (putnam-2019-a6-quoted power)
          (putnam-2019-a6-quoted epsilon)
          'delta)
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-small-o-delta-exists-p
    (function r power epsilon)
  (not
   (fn-equal
    (putnam-2019-a6-small-o-delta-failure-function
     function r power epsilon)
    (putnam-2019-a6-true-function '(delta)))))

(defun putnam-2019-a6-small-o-function
    (function r power)
  (list
   'lambda
   '(epsilon)
   (putnam-2019-a6-implies-term
    (putnam-2019-a6-positive-rational-term
     'epsilon)
    (list 'putnam-2019-a6-small-o-delta-exists-p
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted r)
          (putnam-2019-a6-quoted power)
          'epsilon))))

(defun putnam-2019-a6-small-o-p
    (function r power)
  (fn-equal
   (putnam-2019-a6-small-o-function
    function r power)
   (putnam-2019-a6-true-function '(epsilon))))

(defun putnam-2019-a6-in-right-interval-p
    (x-prime x)
  (and
   (putnam-2019-a6-real-name-p x-prime)
   (putnam-2019-a6-real-name-p x)
   (putnam-2019-a6-real-lt-p
    (putnam-2019-a6-rational-name 0)
    x-prime)
   (putnam-2019-a6-real-le-p x-prime x)))

(defun putnam-2019-a6-scaled-second-name
    (x-prime second r power)
  (putnam-2019-a6-multiply-name
   (apply$ power (list x-prime r))
   (putnam-2019-a6-absolute-name
    (apply$ second (list x-prime)))))

(defun putnam-2019-a6-blowup-point-witness-p
    (x-prime x target second r power)
  (and
   (rationalp target)
   (putnam-2019-a6-in-right-interval-p
    x-prime x)
   (putnam-2019-a6-real-le-p
    (putnam-2019-a6-rational-name target)
    (putnam-2019-a6-scaled-second-name
     x-prime second r power))))

(defun putnam-2019-a6-blowup-point-failure-function
    (x target second r power)
  (list
   'lambda
   '(x-prime)
   (list
    'if
    (list 'putnam-2019-a6-blowup-point-witness-p
          'x-prime
          (putnam-2019-a6-quoted x)
          (putnam-2019-a6-quoted target)
          (putnam-2019-a6-quoted second)
          (putnam-2019-a6-quoted r)
          (putnam-2019-a6-quoted power))
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-blowup-point-exists-p
    (x target second r power)
  (not
   (fn-equal
    (putnam-2019-a6-blowup-point-failure-function
     x target second r power)
    (putnam-2019-a6-true-function '(x-prime)))))

;; Requiring a family member above every rational threshold is equivalent to
;; the source supremum tending to +infinity: rational thresholds are cofinal,
;; and a supremum above M+1 has a member above M.

(defun putnam-2019-a6-blowup-delta-function
    (target second r power delta)
  (list
   'lambda
   '(x)
   (putnam-2019-a6-implies-term
    (list 'putnam-2019-a6-in-right-neighborhood-p
          'x
          (putnam-2019-a6-quoted delta))
    (list 'putnam-2019-a6-blowup-point-exists-p
          'x
          (putnam-2019-a6-quoted target)
          (putnam-2019-a6-quoted second)
          (putnam-2019-a6-quoted r)
          (putnam-2019-a6-quoted power)))))

(defun putnam-2019-a6-blowup-delta-p
    (target second r power delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2019-a6-blowup-delta-function
     target second r power delta)
    (putnam-2019-a6-true-function '(x)))))

(defun putnam-2019-a6-blowup-delta-failure-function
    (target second r power)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2019-a6-blowup-delta-p
          (putnam-2019-a6-quoted target)
          (putnam-2019-a6-quoted second)
          (putnam-2019-a6-quoted r)
          (putnam-2019-a6-quoted power)
          'delta)
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-blowup-delta-exists-p
    (target second r power)
  (not
   (fn-equal
    (putnam-2019-a6-blowup-delta-failure-function
     target second r power)
    (putnam-2019-a6-true-function '(delta)))))

(defun putnam-2019-a6-blowup-function
    (second r power)
  (list
   'lambda
   '(target)
   (putnam-2019-a6-implies-term
    (list 'rationalp 'target)
    (list 'putnam-2019-a6-blowup-delta-exists-p
          'target
          (putnam-2019-a6-quoted second)
          (putnam-2019-a6-quoted r)
          (putnam-2019-a6-quoted power)))))

(defun putnam-2019-a6-blowup-p
    (second r power)
  (fn-equal
   (putnam-2019-a6-blowup-function
    second r power)
   (putnam-2019-a6-true-function '(target))))

(defun putnam-2019-a6-analytic-witness-p
    (witness function r)
  (and
   (true-listp witness)
   (equal (len witness) 3)
   (let ((derivative (nth 0 witness))
         (second (nth 1 witness))
         (power (nth 2 witness)))
     (and
      (putnam-2019-a6-real-function-p function)
      (putnam-2019-a6-real-name-p r)
      (putnam-2019-a6-real-lt-p
       (putnam-2019-a6-rational-name 1)
       r)
      (putnam-2019-a6-power-oracle-p power)
      (putnam-2019-a6-continuous-on-p
       function t)
      (putnam-2019-a6-continuous-on-p
       derivative nil)
      (putnam-2019-a6-derivative-on-open-p
       function derivative)
      (putnam-2019-a6-derivative-on-open-p
       derivative second)))))

(defun putnam-2019-a6-hypothesis-witness-p
    (witness function r)
  (and
   (putnam-2019-a6-analytic-witness-p
    witness function r)
   (putnam-2019-a6-small-o-p
    function r (nth 2 witness))))

(defun putnam-2019-a6-conclusion-witness-p
    (witness function r)
  (and
   (putnam-2019-a6-hypothesis-witness-p
    witness function r)
   (let ((derivative (nth 0 witness))
         (second (nth 1 witness))
         (power (nth 2 witness)))
     (or
      (putnam-2019-a6-right-limit-zero-p
       derivative)
      (putnam-2019-a6-blowup-p
       second r power)))))

(defun putnam-2019-a6-hypothesis-failure-function
    (function r)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list 'putnam-2019-a6-hypothesis-witness-p
          'witness
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted r))
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-hypothesis-exists-p
    (function r)
  (not
   (fn-equal
    (putnam-2019-a6-hypothesis-failure-function
     function r)
    (putnam-2019-a6-true-function '(witness)))))

(defun putnam-2019-a6-conclusion-failure-function
    (function r)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list 'putnam-2019-a6-conclusion-witness-p
          'witness
          (putnam-2019-a6-quoted function)
          (putnam-2019-a6-quoted r))
    (putnam-2019-a6-quoted nil)
    (putnam-2019-a6-quoted t))))

(defun putnam-2019-a6-conclusion-exists-p
    (function r)
  (not
   (fn-equal
    (putnam-2019-a6-conclusion-failure-function
     function r)
    (putnam-2019-a6-true-function '(witness)))))

(defun putnambench-putnam-2019-a6-statement
    (function r)
  (implies
   (putnam-2019-a6-hypothesis-exists-p
    function r)
   (putnam-2019-a6-conclusion-exists-p
    function r)))

(value-triple :itpeval-statement-checked)
:q
