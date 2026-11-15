;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_a5:
;; twice continuously differentiable real functions with diagonal zeroes,
;; controlled positive g, and gradient parallel to (g(u),-g(v)) satisfy the
;; stated O(1/n) pair-value bound. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, and real functions are extensional
;; ACL2 function objects on those names. Positive rational tolerances and
;; radii are cofinal in the positive reals. Derivative functions, pointwise
;; parallelism scalars, and the concluding constant are all internally
;; quantified by negated FN-EQUAL tests; none is an external parameter.
;;
;; Differentiability is expressed using every real base point and every
;; nonzero rational increment. Joint continuity of F and all partial
;; derivatives, and continuity of g and its first two derivatives, make these
;; dense-increment limits equivalent to the source C^2 assumptions. A list of
;; exactly n+1 real names is a bijective encoding of Fin (n+1) -> R, and the
;; recursive pair search is exactly the finite minimum conclusion.

(defun putnam-2011-a5-quoted (object)
  (list 'quote object))

(defun putnam-2011-a5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2011-a5-term-list (cdr terms)))
    nil))

(defun putnam-2011-a5-apply-term (function arguments)
  (list 'apply$
        (putnam-2011-a5-quoted function)
        (putnam-2011-a5-term-list arguments)))

(defun putnam-2011-a5-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2011-a5-term-list arguments)))

(defun putnam-2011-a5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2011-a5-and-terms (cdr terms))
            (putnam-2011-a5-quoted nil))
    (putnam-2011-a5-quoted t)))

(defun putnam-2011-a5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2011-a5-quoted t)))

(defun putnam-2011-a5-not-term (term)
  (list 'if
        term
        (putnam-2011-a5-quoted nil)
        (putnam-2011-a5-quoted t)))

(defun putnam-2011-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2011-a5-negate-term (value)
  (list 'unary-- value))

(defun putnam-2011-a5-subtract-term (left right)
  (putnam-2011-a5-add-term
   left
   (putnam-2011-a5-negate-term right)))

(defun putnam-2011-a5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2011-a5-divide-term (numerator denominator)
  (putnam-2011-a5-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2011-a5-absolute-term (value)
  (list 'if
        (list '< value (putnam-2011-a5-quoted 0))
        (putnam-2011-a5-negate-term value)
        value))

(defun putnam-2011-a5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2011-a5-quoted nil)
        (putnam-2011-a5-quoted t)))

(defun putnam-2011-a5-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-2011-a5-positive-rational-term (value)
  (putnam-2011-a5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2011-a5-quoted 0) value))))

(defun putnam-2011-a5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2011-a5-quoted t)))

(defun putnam-2011-a5-real-value-term (name precision)
  (putnam-2011-a5-apply-term name (list precision)))

(defun putnam-2011-a5-object-real-value-term
    (name-term precision)
  (putnam-2011-a5-apply-object-term
   name-term
   (list precision)))

(defun putnam-2011-a5-real-cauchy-function (name)
  (let* ((left
          (putnam-2011-a5-real-value-term name 'epsilon))
         (right
          (putnam-2011-a5-real-value-term name 'eta))
         (distance
          (putnam-2011-a5-absolute-term
           (putnam-2011-a5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-and-terms
       (list
        (putnam-2011-a5-positive-rational-term 'epsilon)
        (putnam-2011-a5-positive-rational-term 'eta)))
      (putnam-2011-a5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2011-a5-less-equal-term
         distance
         (putnam-2011-a5-add-term
          'epsilon 'eta))))))))

(defun putnam-2011-a5-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2011-a5-real-cauchy-function name)
    (putnam-2011-a5-true-function
     '(epsilon eta)))))

;; Sampling both names at eta/4 makes the universal inequality equivalent to
;; the represented real distance being at most BOUND.
(defun putnam-2011-a5-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2011-a5-multiply-term
           (putnam-2011-a5-quoted 1/4)
           'eta))
         (left
          (putnam-2011-a5-real-value-term
           left-name precision))
         (right
          (putnam-2011-a5-real-value-term
           right-name precision))
         (distance
          (putnam-2011-a5-absolute-term
           (putnam-2011-a5-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-positive-rational-term 'eta)
      (putnam-2011-a5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2011-a5-less-equal-term
         distance
         (putnam-2011-a5-add-term
          (putnam-2011-a5-quoted bound)
          'eta))))))))

(defun putnam-2011-a5-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2011-a5-real-name-p left-name)
   (putnam-2011-a5-real-name-p right-name)
   (fn-equal
    (putnam-2011-a5-real-distance-function
     left-name right-name bound)
    (putnam-2011-a5-true-function '(eta)))))

(defun putnam-2011-a5-real-equal-p
    (left-name right-name)
  (putnam-2011-a5-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2011-a5-unary-output-function
    (function)
  (let ((output
         (putnam-2011-a5-apply-term function (list 'x))))
    (list
     'lambda
     '(x)
     (putnam-2011-a5-implies-term
      (list 'putnam-2011-a5-real-name-p 'x)
      (list 'putnam-2011-a5-real-name-p output)))))

(defun putnam-2011-a5-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-2011-a5-apply-term
          function (list 'x-left)))
        (right-output
         (putnam-2011-a5-apply-term
          function (list 'x-right))))
    (list
     'lambda
     '(x-left x-right)
     (putnam-2011-a5-implies-term
      (list 'putnam-2011-a5-real-equal-p
            'x-left 'x-right)
      (list 'putnam-2011-a5-real-equal-p
            left-output right-output)))))

(defun putnam-2011-a5-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2011-a5-unary-output-function function)
    (putnam-2011-a5-true-function '(x)))
   (fn-equal
    (putnam-2011-a5-unary-extensional-function function)
    (putnam-2011-a5-true-function
     '(x-left x-right)))))

(defun putnam-2011-a5-rational-shift-name (name shift)
  (let ((value
         (putnam-2011-a5-object-real-value-term
          (putnam-2011-a5-quoted name)
          (putnam-2011-a5-multiply-term
           (putnam-2011-a5-quoted 1/2)
           'precision))))
    (list
     'lambda
     '(precision)
     (putnam-2011-a5-add-term
      value
      (putnam-2011-a5-quoted shift)))))

;; Continuity is stated using closed rational radii. Rescaling epsilon and
;; delta gives the usual open-ball definition in both directions.
(defun putnam-2011-a5-continuous-at-delta-function
    (function x epsilon delta)
  (let ((at-x
         (putnam-2011-a5-apply-term
          function
          (list (putnam-2011-a5-quoted x))))
        (at-y
         (putnam-2011-a5-apply-term
          function
          (list 'y))))
    (list
     'lambda
     '(y)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-and-terms
       (list
        (list 'putnam-2011-a5-real-name-p 'y)
        (list 'putnam-2011-a5-real-distance-at-most-p
              (putnam-2011-a5-quoted x)
              'y
              (putnam-2011-a5-quoted delta))))
      (list 'putnam-2011-a5-real-distance-at-most-p
            at-x
            at-y
            (putnam-2011-a5-quoted epsilon))))))

(defun putnam-2011-a5-continuous-at-delta-p
    (function x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2011-a5-continuous-at-delta-function
     function x epsilon delta)
    (putnam-2011-a5-true-function '(y)))))

(defun putnam-2011-a5-continuity-delta-failure-function
    (function x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2011-a5-continuous-at-delta-p
          (putnam-2011-a5-quoted function)
          (putnam-2011-a5-quoted x)
          (putnam-2011-a5-quoted epsilon)
          'delta)
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-continuity-delta-exists-p
    (function x epsilon)
  (not
   (fn-equal
    (putnam-2011-a5-continuity-delta-failure-function
     function x epsilon)
    (putnam-2011-a5-true-function '(delta)))))

(defun putnam-2011-a5-continuity-function (function)
  (list
   'lambda
   '(x epsilon)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'putnam-2011-a5-real-name-p 'x)
      (putnam-2011-a5-positive-rational-term 'epsilon)))
    (list 'putnam-2011-a5-continuity-delta-exists-p
          (putnam-2011-a5-quoted function)
          'x
          'epsilon))))

(defun putnam-2011-a5-continuous-p (function)
  (and
   (putnam-2011-a5-real-function-p function)
   (fn-equal
    (putnam-2011-a5-continuity-function function)
    (putnam-2011-a5-true-function
     '(x epsilon)))))

;; At precision eta, each numerator value is sampled at |h|*eta/4, so this is
;; a regular Cauchy name for (f(x+h)-f(x))/h when h is a nonzero rational.
(defun putnam-2011-a5-difference-quotient-name
    (function x h)
  (let* ((shifted-x
          (putnam-2011-a5-rational-shift-name x h))
         (at-shifted-x
          (putnam-2011-a5-apply-term
           function
           (list (putnam-2011-a5-quoted shifted-x))))
         (at-x
          (putnam-2011-a5-apply-term
           function
           (list (putnam-2011-a5-quoted x))))
         (sample-precision
          (putnam-2011-a5-multiply-term
           (putnam-2011-a5-quoted (/ (abs h) 4))
           'eta))
         (shifted-value
          (putnam-2011-a5-object-real-value-term
           at-shifted-x sample-precision))
         (value
          (putnam-2011-a5-object-real-value-term
           at-x sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-2011-a5-divide-term
      (putnam-2011-a5-subtract-term
       shifted-value value)
      (putnam-2011-a5-quoted h)))))

(defun putnam-2011-a5-derivative-at-delta-function
    (function derivative x epsilon delta)
  (let ((quotient
         (list 'putnam-2011-a5-difference-quotient-name
               (putnam-2011-a5-quoted function)
               (putnam-2011-a5-quoted x)
               'h))
        (derivative-at-x
         (putnam-2011-a5-apply-term
          derivative
          (list (putnam-2011-a5-quoted x)))))
    (list
     'lambda
     '(h)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-2011-a5-not-term
         (list 'equal 'h (putnam-2011-a5-quoted 0)))
        (putnam-2011-a5-less-equal-term
         (putnam-2011-a5-absolute-term 'h)
         (putnam-2011-a5-quoted delta))))
      (list 'putnam-2011-a5-real-distance-at-most-p
            quotient
            derivative-at-x
            (putnam-2011-a5-quoted epsilon))))))

(defun putnam-2011-a5-derivative-at-delta-p
    (function derivative x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2011-a5-derivative-at-delta-function
     function derivative x epsilon delta)
    (putnam-2011-a5-true-function '(h)))))

(defun putnam-2011-a5-derivative-delta-failure-function
    (function derivative x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2011-a5-derivative-at-delta-p
          (putnam-2011-a5-quoted function)
          (putnam-2011-a5-quoted derivative)
          (putnam-2011-a5-quoted x)
          (putnam-2011-a5-quoted epsilon)
          'delta)
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-derivative-delta-exists-p
    (function derivative x epsilon)
  (not
   (fn-equal
    (putnam-2011-a5-derivative-delta-failure-function
     function derivative x epsilon)
    (putnam-2011-a5-true-function '(delta)))))

(defun putnam-2011-a5-derivative-function
    (function derivative)
  (list
   'lambda
   '(x epsilon)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'putnam-2011-a5-real-name-p 'x)
      (putnam-2011-a5-positive-rational-term 'epsilon)))
    (list 'putnam-2011-a5-derivative-delta-exists-p
          (putnam-2011-a5-quoted function)
          (putnam-2011-a5-quoted derivative)
          'x
          'epsilon))))

(defun putnam-2011-a5-derivative-relation-p
    (function derivative)
  (and
   (putnam-2011-a5-real-function-p function)
   (putnam-2011-a5-real-function-p derivative)
   (fn-equal
    (putnam-2011-a5-derivative-function
     function derivative)
    (putnam-2011-a5-true-function
     '(x epsilon)))))

(defun putnam-2011-a5-constant-name (value)
  (list
   'lambda
   '(precision)
   (putnam-2011-a5-quoted value)))

(defun putnam-2011-a5-real-negate-name (name)
  (let ((value
         (putnam-2011-a5-object-real-value-term
          (putnam-2011-a5-quoted name)
          'precision)))
    (list
     'lambda
     '(precision)
     (putnam-2011-a5-negate-term value))))

(defun putnam-2011-a5-real-scale-name (name scalar)
  (let* ((sample-precision
          (putnam-2011-a5-divide-term
           'precision
           (putnam-2011-a5-add-term
            (putnam-2011-a5-quoted 1)
            (putnam-2011-a5-absolute-term
             (putnam-2011-a5-quoted scalar)))))
         (value
          (putnam-2011-a5-object-real-value-term
           (putnam-2011-a5-quoted name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-2011-a5-multiply-term
      (putnam-2011-a5-quoted scalar)
      value))))

(defun putnam-2011-a5-real-product-name (left-name right-name)
  (let* ((left-coarse
          (putnam-2011-a5-object-real-value-term
           (putnam-2011-a5-quoted left-name)
           (putnam-2011-a5-quoted 1)))
         (right-coarse
          (putnam-2011-a5-object-real-value-term
           (putnam-2011-a5-quoted right-name)
           (putnam-2011-a5-quoted 1)))
         (scale
          (putnam-2011-a5-multiply-term
           (putnam-2011-a5-quoted 64)
           (putnam-2011-a5-add-term
            (putnam-2011-a5-quoted 1)
            (putnam-2011-a5-add-term
             (putnam-2011-a5-absolute-term left-coarse)
             (putnam-2011-a5-absolute-term right-coarse)))))
         (sample-precision
          (putnam-2011-a5-minimum-term
           (putnam-2011-a5-quoted 1)
           (putnam-2011-a5-divide-term
            'precision scale)))
         (left-value
          (putnam-2011-a5-object-real-value-term
           (putnam-2011-a5-quoted left-name)
           sample-precision))
         (right-value
          (putnam-2011-a5-object-real-value-term
           (putnam-2011-a5-quoted right-name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-2011-a5-multiply-term
      left-value right-value))))

(defun putnam-2011-a5-real-absolute-name (name)
  (let ((value
         (putnam-2011-a5-object-real-value-term
          (putnam-2011-a5-quoted name)
          'precision)))
    (list
     'lambda
     '(precision)
     (putnam-2011-a5-absolute-term value))))

(defun putnam-2011-a5-real-less-equal-function
    (left-name right-name)
  (let* ((sample-precision
          (putnam-2011-a5-multiply-term
           (putnam-2011-a5-quoted 1/4)
           'eta))
         (left
          (putnam-2011-a5-real-value-term
           left-name sample-precision))
         (right
          (putnam-2011-a5-real-value-term
           right-name sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-positive-rational-term 'eta)
      (putnam-2011-a5-less-equal-term
       left
       (putnam-2011-a5-add-term right 'eta))))))

(defun putnam-2011-a5-real-less-equal-p
    (left-name right-name)
  (and
   (putnam-2011-a5-real-name-p left-name)
   (putnam-2011-a5-real-name-p right-name)
   (fn-equal
    (putnam-2011-a5-real-less-equal-function
     left-name right-name)
    (putnam-2011-a5-true-function '(eta)))))

(defun putnam-2011-a5-positive-witness-p
    (epsilon name)
  (and
   (rationalp epsilon)
   (< 0 epsilon)
   (putnam-2011-a5-real-less-equal-p
    (putnam-2011-a5-constant-name epsilon)
    name)))

(defun putnam-2011-a5-positive-witness-failure-function
    (name)
  (list
   'lambda
   '(epsilon)
   (list
    'if
    (list 'putnam-2011-a5-positive-witness-p
          'epsilon
          (putnam-2011-a5-quoted name))
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-real-positive-p (name)
  (let ((failure
         (putnam-2011-a5-positive-witness-failure-function
          name))
        (always-true
         (putnam-2011-a5-true-function '(epsilon))))
    (and
     (putnam-2011-a5-real-name-p name)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-2011-a5-binary-output-function
    (function)
  (let ((output
         (putnam-2011-a5-apply-term
          function (list 'x 'y))))
    (list
     'lambda
     '(x y)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-and-terms
       (list
        (list 'putnam-2011-a5-real-name-p 'x)
        (list 'putnam-2011-a5-real-name-p 'y)))
      (list 'putnam-2011-a5-real-name-p output)))))

(defun putnam-2011-a5-binary-extensional-function
    (function)
  (let ((left-output
         (putnam-2011-a5-apply-term
          function (list 'x-left 'y-left)))
        (right-output
         (putnam-2011-a5-apply-term
          function (list 'x-right 'y-right))))
    (list
     'lambda
     '(x-left x-right y-left y-right)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-and-terms
       (list
        (list 'putnam-2011-a5-real-equal-p
              'x-left 'x-right)
        (list 'putnam-2011-a5-real-equal-p
              'y-left 'y-right)))
      (list 'putnam-2011-a5-real-equal-p
            left-output right-output)))))

(defun putnam-2011-a5-real-binary-function-p
    (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2011-a5-binary-output-function function)
    (putnam-2011-a5-true-function '(x y)))
   (fn-equal
    (putnam-2011-a5-binary-extensional-function function)
    (putnam-2011-a5-true-function
     '(x-left x-right y-left y-right)))))

(defun putnam-2011-a5-binary-continuous-at-delta-function
    (function x y epsilon delta)
  (let ((at-base
         (putnam-2011-a5-apply-term
          function
          (list
           (putnam-2011-a5-quoted x)
           (putnam-2011-a5-quoted y))))
        (at-point
         (putnam-2011-a5-apply-term
          function (list 'u 'v))))
    (list
     'lambda
     '(u v)
     (putnam-2011-a5-implies-term
      (putnam-2011-a5-and-terms
       (list
        (list 'putnam-2011-a5-real-name-p 'u)
        (list 'putnam-2011-a5-real-name-p 'v)
        (list 'putnam-2011-a5-real-distance-at-most-p
              (putnam-2011-a5-quoted x)
              'u
              (putnam-2011-a5-quoted delta))
        (list 'putnam-2011-a5-real-distance-at-most-p
              (putnam-2011-a5-quoted y)
              'v
              (putnam-2011-a5-quoted delta))))
      (list 'putnam-2011-a5-real-distance-at-most-p
            at-base
            at-point
            (putnam-2011-a5-quoted epsilon))))))

(defun putnam-2011-a5-binary-continuous-at-delta-p
    (function x y epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (fn-equal
    (putnam-2011-a5-binary-continuous-at-delta-function
     function x y epsilon delta)
    (putnam-2011-a5-true-function '(u v)))))

(defun putnam-2011-a5-binary-continuity-delta-failure-function
    (function x y epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list 'putnam-2011-a5-binary-continuous-at-delta-p
          (putnam-2011-a5-quoted function)
          (putnam-2011-a5-quoted x)
          (putnam-2011-a5-quoted y)
          (putnam-2011-a5-quoted epsilon)
          'delta)
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-binary-continuity-delta-exists-p
    (function x y epsilon)
  (not
   (fn-equal
    (putnam-2011-a5-binary-continuity-delta-failure-function
     function x y epsilon)
    (putnam-2011-a5-true-function '(delta)))))

(defun putnam-2011-a5-binary-continuity-function
    (function)
  (list
   'lambda
   '(x y epsilon)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'putnam-2011-a5-real-name-p 'x)
      (list 'putnam-2011-a5-real-name-p 'y)
      (putnam-2011-a5-positive-rational-term 'epsilon)))
    (list 'putnam-2011-a5-binary-continuity-delta-exists-p
          (putnam-2011-a5-quoted function)
          'x
          'y
          'epsilon))))

(defun putnam-2011-a5-binary-continuous-p
    (function)
  (and
   (putnam-2011-a5-real-binary-function-p function)
   (fn-equal
    (putnam-2011-a5-binary-continuity-function function)
    (putnam-2011-a5-true-function
     '(x y epsilon)))))

(defun putnam-2011-a5-first-slice-function
    (function fixed-second)
  (list
   'lambda
   '(x)
   (putnam-2011-a5-apply-term
    function
    (list
     'x
     (putnam-2011-a5-quoted fixed-second)))))

(defun putnam-2011-a5-second-slice-function
    (function fixed-first)
  (list
   'lambda
   '(y)
   (putnam-2011-a5-apply-term
    function
    (list
     (putnam-2011-a5-quoted fixed-first)
     'y))))

(defun putnam-2011-a5-first-partial-function
    (function derivative)
  (list
   'lambda
   '(u v epsilon)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'putnam-2011-a5-real-name-p 'u)
      (list 'putnam-2011-a5-real-name-p 'v)
      (putnam-2011-a5-positive-rational-term 'epsilon)))
    (list 'putnam-2011-a5-derivative-delta-exists-p
          (list 'putnam-2011-a5-first-slice-function
                (putnam-2011-a5-quoted function)
                'v)
          (list 'putnam-2011-a5-first-slice-function
                (putnam-2011-a5-quoted derivative)
                'v)
          'u
          'epsilon))))

(defun putnam-2011-a5-second-partial-function
    (function derivative)
  (list
   'lambda
   '(u v epsilon)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'putnam-2011-a5-real-name-p 'u)
      (list 'putnam-2011-a5-real-name-p 'v)
      (putnam-2011-a5-positive-rational-term 'epsilon)))
    (list 'putnam-2011-a5-derivative-delta-exists-p
          (list 'putnam-2011-a5-second-slice-function
                (putnam-2011-a5-quoted function)
                'u)
          (list 'putnam-2011-a5-second-slice-function
                (putnam-2011-a5-quoted derivative)
                'u)
          'v
          'epsilon))))

(defun putnam-2011-a5-first-partial-relation-p
    (function derivative)
  (and
   (putnam-2011-a5-real-binary-function-p function)
   (putnam-2011-a5-real-binary-function-p derivative)
   (fn-equal
    (putnam-2011-a5-first-partial-function
     function derivative)
    (putnam-2011-a5-true-function
     '(u v epsilon)))))

(defun putnam-2011-a5-second-partial-relation-p
    (function derivative)
  (and
   (putnam-2011-a5-real-binary-function-p function)
   (putnam-2011-a5-real-binary-function-p derivative)
   (fn-equal
    (putnam-2011-a5-second-partial-function
     function derivative)
    (putnam-2011-a5-true-function
     '(u v epsilon)))))

(defun putnam-2011-a5-diagonal-function (function)
  (let ((value
         (putnam-2011-a5-apply-term
          function (list 'u 'u))))
    (list
     'lambda
     '(u)
     (putnam-2011-a5-implies-term
      (list 'putnam-2011-a5-real-name-p 'u)
      (list 'putnam-2011-a5-real-equal-p
            value
            (list 'putnam-2011-a5-constant-name
                  (putnam-2011-a5-quoted 0)))))))

(defun putnam-2011-a5-diagonal-zero-p (function)
  (fn-equal
   (putnam-2011-a5-diagonal-function function)
   (putnam-2011-a5-true-function '(u))))

(defun putnam-2011-a5-g-bound-function (g)
  (let* ((gx
          (putnam-2011-a5-apply-term g (list 'x)))
         (square
          (list 'putnam-2011-a5-real-product-name
                'x 'x))
         (weighted-square
          (list 'putnam-2011-a5-real-product-name
                square gx)))
    (list
     'lambda
     '(x)
     (putnam-2011-a5-implies-term
      (list 'putnam-2011-a5-real-name-p 'x)
      (putnam-2011-a5-and-terms
       (list
        (list 'putnam-2011-a5-real-positive-p gx)
        (list 'putnam-2011-a5-real-less-equal-p
              weighted-square
              (list 'putnam-2011-a5-constant-name
                    (putnam-2011-a5-quoted 1)))))))))

(defun putnam-2011-a5-g-bound-p (g)
  (fn-equal
   (putnam-2011-a5-g-bound-function g)
   (putnam-2011-a5-true-function '(x))))

(defun putnam-2011-a5-parallel-witness-p
    (c u v g first-partial second-partial)
  (let* ((gu (apply$ g (list u)))
         (gv (apply$ g (list v)))
         (du (apply$ first-partial (list u v)))
         (dv (apply$ second-partial (list u v))))
    (and
     (putnam-2011-a5-real-name-p c)
     (putnam-2011-a5-real-equal-p
      du
      (putnam-2011-a5-real-product-name c gu))
     (putnam-2011-a5-real-equal-p
      dv
      (putnam-2011-a5-real-product-name
       c
       (putnam-2011-a5-real-negate-name gv))))))

(defun putnam-2011-a5-parallel-witness-failure-function
    (u v g first-partial second-partial)
  (list
   'lambda
   '(c)
   (list
    'if
    (list 'putnam-2011-a5-parallel-witness-p
          'c
          (putnam-2011-a5-quoted u)
          (putnam-2011-a5-quoted v)
          (putnam-2011-a5-quoted g)
          (putnam-2011-a5-quoted first-partial)
          (putnam-2011-a5-quoted second-partial))
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-parallel-witness-exists-p
    (u v g first-partial second-partial)
  (let ((failure
         (putnam-2011-a5-parallel-witness-failure-function
          u v g first-partial second-partial))
        (always-true
         (putnam-2011-a5-true-function '(c))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-2011-a5-parallel-function
    (g first-partial second-partial)
  (list
   'lambda
   '(u v)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'putnam-2011-a5-real-name-p 'u)
      (list 'putnam-2011-a5-real-name-p 'v)))
    (list 'putnam-2011-a5-parallel-witness-exists-p
          'u
          'v
          (putnam-2011-a5-quoted g)
          (putnam-2011-a5-quoted first-partial)
          (putnam-2011-a5-quoted second-partial)))))

(defun putnam-2011-a5-parallel-p
    (g first-partial second-partial)
  (fn-equal
   (putnam-2011-a5-parallel-function
    g first-partial second-partial)
   (putnam-2011-a5-true-function '(u v))))

(defun putnam-2011-a5-hypothesis-witness-p
    (g-first g-second
     f-first f-second
     f-first-first f-first-second
     f-second-first f-second-second
     f g)
  (and
   (putnam-2011-a5-continuous-p g)
   (putnam-2011-a5-continuous-p g-first)
   (putnam-2011-a5-continuous-p g-second)
   (putnam-2011-a5-derivative-relation-p g g-first)
   (putnam-2011-a5-derivative-relation-p
    g-first g-second)
   (putnam-2011-a5-binary-continuous-p f)
   (putnam-2011-a5-binary-continuous-p f-first)
   (putnam-2011-a5-binary-continuous-p f-second)
   (putnam-2011-a5-binary-continuous-p f-first-first)
   (putnam-2011-a5-binary-continuous-p f-first-second)
   (putnam-2011-a5-binary-continuous-p f-second-first)
   (putnam-2011-a5-binary-continuous-p f-second-second)
   (putnam-2011-a5-first-partial-relation-p f f-first)
   (putnam-2011-a5-second-partial-relation-p f f-second)
   (putnam-2011-a5-first-partial-relation-p
    f-first f-first-first)
   (putnam-2011-a5-second-partial-relation-p
    f-first f-first-second)
   (putnam-2011-a5-first-partial-relation-p
    f-second f-second-first)
   (putnam-2011-a5-second-partial-relation-p
    f-second f-second-second)
   (putnam-2011-a5-diagonal-zero-p f)
   (putnam-2011-a5-g-bound-p g)
   (putnam-2011-a5-parallel-p
    g f-first f-second)))

(defun putnam-2011-a5-hypothesis-witness-failure-function
    (f g)
  (list
   'lambda
   '(g-first g-second
     f-first f-second
     f-first-first f-first-second
     f-second-first f-second-second)
   (list
    'if
    (list 'putnam-2011-a5-hypothesis-witness-p
          'g-first 'g-second
          'f-first 'f-second
          'f-first-first 'f-first-second
          'f-second-first 'f-second-second
          (putnam-2011-a5-quoted f)
          (putnam-2011-a5-quoted g))
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-hypothesis-p (f g)
  (let ((failure
         (putnam-2011-a5-hypothesis-witness-failure-function
          f g))
        (always-true
         (putnam-2011-a5-true-function
          '(g-first g-second
            f-first f-second
            f-first-first f-first-second
            f-second-first f-second-second))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-2011-a5-real-vector-p
    (values expected-length)
  (if (zp expected-length)
      (equal values nil)
    (and
     (consp values)
     (putnam-2011-a5-real-name-p (car values))
     (putnam-2011-a5-real-vector-p
      (cdr values)
      (- expected-length 1)))))

(defun putnam-2011-a5-pair-bound-inner-p
    (f bound left-value right-values i j)
  (if (endp right-values)
      nil
    (or
     (and
      (not (equal i j))
      (putnam-2011-a5-real-less-equal-p
       (putnam-2011-a5-real-absolute-name
        (apply$ f (list left-value (car right-values))))
       bound))
     (putnam-2011-a5-pair-bound-inner-p
      f bound left-value (cdr right-values) i (+ j 1)))))

(defun putnam-2011-a5-pair-bound-outer-p
    (f bound left-values all-values i)
  (if (endp left-values)
      nil
    (or
     (putnam-2011-a5-pair-bound-inner-p
      f bound (car left-values) all-values i 0)
     (putnam-2011-a5-pair-bound-outer-p
      f bound (cdr left-values) all-values (+ i 1)))))

(defun putnam-2011-a5-pair-bound-p
    (f c n values)
  (let ((bound
         (putnam-2011-a5-real-scale-name c (/ 1 n))))
    (putnam-2011-a5-pair-bound-outer-p
     f bound values values 0)))

(defun putnam-2011-a5-conclusion-for-c-function
    (f c)
  (list
   'lambda
   '(n values)
   (putnam-2011-a5-implies-term
    (putnam-2011-a5-and-terms
     (list
      (list 'natp 'n)
      (list '<= (putnam-2011-a5-quoted 2) 'n)
      (list 'putnam-2011-a5-real-vector-p
            'values
            (list 'binary-+ 'n
                  (putnam-2011-a5-quoted 1)))))
    (list 'putnam-2011-a5-pair-bound-p
          (putnam-2011-a5-quoted f)
          (putnam-2011-a5-quoted c)
          'n
          'values))))

(defun putnam-2011-a5-conclusion-for-c-p (f c)
  (and
   (putnam-2011-a5-real-name-p c)
   (fn-equal
    (putnam-2011-a5-conclusion-for-c-function f c)
    (putnam-2011-a5-true-function '(n values)))))

(defun putnam-2011-a5-conclusion-witness-failure-function
    (f)
  (list
   'lambda
   '(c)
   (list
    'if
    (list 'putnam-2011-a5-conclusion-for-c-p
          (putnam-2011-a5-quoted f)
          'c)
    (putnam-2011-a5-quoted nil)
    (putnam-2011-a5-quoted t))))

(defun putnam-2011-a5-conclusion-p (f)
  (let ((failure
         (putnam-2011-a5-conclusion-witness-failure-function
          f))
        (always-true
         (putnam-2011-a5-true-function '(c))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnambench-putnam-2011-a5-statement (f g)
  (implies
   (putnam-2011-a5-hypothesis-p f g)
   (putnam-2011-a5-conclusion-p f)))

(value-triple :itpeval-statement-checked)
:q
