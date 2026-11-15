;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_b6:
;; classification of continuous positive-real functions satisfying the stated
;; two-variable functional equation as f(x)=1/(1+c*x) for some c>=0. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are represented by rational regular Cauchy names, and f is an
;; extensional ACL2 function object on positive-real names. FN-EQUAL supplies
;; unbounded universal quantification over names. Negated FN-EQUAL keeps the
;; coefficient c and each continuity delta internal.
;;
;; Continuity is stated using positive rational epsilon and delta. This is
;; equivalent to the usual real epsilon-delta definition by density of the
;; rationals. The solution equation is written as
;;
;;   (1+c*x)*f(x)=1,
;;
;; which is equivalent to f(x)=1/(1+c*x), since c>=0 and x>0 make the factor
;; 1+c*x strictly positive.

(defun putnam-2022-b6-quoted (object)
  (list 'quote object))

(defun putnam-2022-b6-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2022-b6-term-list (cdr terms)))
    nil))

(defun putnam-2022-b6-apply-term (function arguments)
  (list 'apply$
        (putnam-2022-b6-quoted function)
        (putnam-2022-b6-term-list arguments)))

(defun putnam-2022-b6-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2022-b6-term-list arguments)))

(defun putnam-2022-b6-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2022-b6-and-terms (cdr terms))
            (putnam-2022-b6-quoted nil))
    (putnam-2022-b6-quoted t)))

(defun putnam-2022-b6-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2022-b6-quoted t)))

(defun putnam-2022-b6-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2022-b6-negate-term (value)
  (list 'unary-- value))

(defun putnam-2022-b6-subtract-term (left right)
  (putnam-2022-b6-add-term
   left
   (putnam-2022-b6-negate-term right)))

(defun putnam-2022-b6-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2022-b6-divide-term (numerator denominator)
  (putnam-2022-b6-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2022-b6-absolute-term (value)
  (list 'if
        (list '< value (putnam-2022-b6-quoted 0))
        (putnam-2022-b6-negate-term value)
        value))

(defun putnam-2022-b6-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2022-b6-quoted nil)
        (putnam-2022-b6-quoted t)))

(defun putnam-2022-b6-positive-rational-term (value)
  (putnam-2022-b6-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2022-b6-quoted 0) value))))

(defun putnam-2022-b6-true-function (formals)
  (list 'lambda
        formals
        (putnam-2022-b6-quoted t)))

(defun putnam-2022-b6-real-value-term (name precision)
  (putnam-2022-b6-apply-term name (list precision)))

(defun putnam-2022-b6-object-real-value-term
    (name-term precision)
  (putnam-2022-b6-apply-object-term
   name-term
   (list precision)))

(defun putnam-2022-b6-real-cauchy-function (name)
  (let* ((left
          (putnam-2022-b6-real-value-term name 'epsilon))
         (right
          (putnam-2022-b6-real-value-term name 'eta))
         (distance
          (putnam-2022-b6-absolute-term
           (putnam-2022-b6-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2022-b6-implies-term
      (putnam-2022-b6-and-terms
       (list
        (putnam-2022-b6-positive-rational-term 'epsilon)
        (putnam-2022-b6-positive-rational-term 'eta)))
      (putnam-2022-b6-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2022-b6-less-equal-term
         distance
         (putnam-2022-b6-add-term
          'epsilon 'eta))))))))

(defun putnam-2022-b6-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2022-b6-real-cauchy-function name)
    (putnam-2022-b6-true-function
     '(epsilon eta)))))

(defun putnam-2022-b6-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2022-b6-multiply-term 1/4 'eta))
         (left
          (putnam-2022-b6-real-value-term
           left-name precision))
         (right
          (putnam-2022-b6-real-value-term
           right-name precision))
         (distance
          (putnam-2022-b6-absolute-term
           (putnam-2022-b6-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2022-b6-implies-term
      (putnam-2022-b6-positive-rational-term 'eta)
      (putnam-2022-b6-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2022-b6-less-equal-term
         distance
         (putnam-2022-b6-add-term
          (putnam-2022-b6-quoted bound)
          'eta))))))))

(defun putnam-2022-b6-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2022-b6-real-name-p left-name)
   (putnam-2022-b6-real-name-p right-name)
   (fn-equal
    (putnam-2022-b6-real-distance-function
     left-name right-name bound)
    (putnam-2022-b6-true-function '(eta)))))

(defun putnam-2022-b6-real-equal-p
    (left-name right-name)
  (putnam-2022-b6-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2022-b6-real-order-function
    (left-name right-name)
  (let* ((precision
          (putnam-2022-b6-multiply-term 1/4 'eta))
         (left
          (putnam-2022-b6-real-value-term
           left-name precision))
         (right
          (putnam-2022-b6-real-value-term
           right-name precision)))
    (list
     'lambda
     '(eta)
     (putnam-2022-b6-implies-term
      (putnam-2022-b6-positive-rational-term 'eta)
      (putnam-2022-b6-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2022-b6-less-equal-term
         left
         (putnam-2022-b6-add-term
          right 'eta))))))))

(defun putnam-2022-b6-real-le-p
    (left-name right-name)
  (and
   (putnam-2022-b6-real-name-p left-name)
   (putnam-2022-b6-real-name-p right-name)
   (fn-equal
    (putnam-2022-b6-real-order-function
     left-name right-name)
    (putnam-2022-b6-true-function '(eta)))))

(defun putnam-2022-b6-real-lt-p
    (left-name right-name)
  (and
   (putnam-2022-b6-real-le-p left-name right-name)
   (not
    (putnam-2022-b6-real-equal-p
     left-name right-name))))

(defun putnam-2022-b6-rational-name (value)
  (list 'lambda
        '(precision)
        (putnam-2022-b6-quoted value)))

(defun putnam-2022-b6-add-name (left-name right-name)
  (let* ((precision
          (putnam-2022-b6-multiply-term 1/2 'epsilon))
         (left
          (putnam-2022-b6-object-real-value-term
           (putnam-2022-b6-quoted left-name)
           precision))
         (right
          (putnam-2022-b6-object-real-value-term
           (putnam-2022-b6-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2022-b6-add-term left right))))

(defun putnam-2022-b6-negate-name (name)
  (let ((value
         (putnam-2022-b6-object-real-value-term
          (putnam-2022-b6-quoted name)
          'epsilon)))
    (list
     'lambda
     '(epsilon)
     (putnam-2022-b6-negate-term value))))

(defun putnam-2022-b6-subtract-name
    (left-name right-name)
  (putnam-2022-b6-add-name
   left-name
   (putnam-2022-b6-negate-name right-name)))

(defun putnam-2022-b6-absolute-name (name)
  (let ((value
         (putnam-2022-b6-object-real-value-term
          (putnam-2022-b6-quoted name)
          'epsilon)))
    (list
     'lambda
     '(epsilon)
     (putnam-2022-b6-absolute-term value))))

(defun putnam-2022-b6-distance-name
    (left-name right-name)
  (putnam-2022-b6-absolute-name
   (putnam-2022-b6-subtract-name
    left-name right-name)))

(defun putnam-2022-b6-multiply-name
    (left-name right-name)
  (let* ((left-at-one
          (putnam-2022-b6-object-real-value-term
           (putnam-2022-b6-quoted left-name)
           1))
         (right-at-one
          (putnam-2022-b6-object-real-value-term
           (putnam-2022-b6-quoted right-name)
           1))
         (scale
          (putnam-2022-b6-multiply-term
           8
           (putnam-2022-b6-add-term
            3
            (putnam-2022-b6-add-term
             (putnam-2022-b6-absolute-term left-at-one)
             (putnam-2022-b6-absolute-term right-at-one)))))
         (candidate
          (putnam-2022-b6-divide-term
           'epsilon scale))
         (precision
          (list 'if
                (list '< 1 candidate)
                1
                candidate))
         (left
          (putnam-2022-b6-object-real-value-term
           (putnam-2022-b6-quoted left-name)
           precision))
         (right
          (putnam-2022-b6-object-real-value-term
           (putnam-2022-b6-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2022-b6-multiply-term left right))))

(defun putnam-2022-b6-positive-real-p (name)
  (putnam-2022-b6-real-lt-p
   (putnam-2022-b6-rational-name 0)
   name))

(defun putnam-2022-b6-positive-function-output-function
    (function)
  (let ((output
         (putnam-2022-b6-apply-term function '(x))))
    (list
     'lambda
     '(x)
     (putnam-2022-b6-implies-term
      (list 'putnam-2022-b6-positive-real-p 'x)
      (list 'putnam-2022-b6-positive-real-p output)))))

(defun putnam-2022-b6-positive-function-extensional-function
    (function)
  (let ((left-output
         (putnam-2022-b6-apply-term
          function '(left)))
        (right-output
         (putnam-2022-b6-apply-term
          function '(right))))
    (list
     'lambda
     '(left right)
     (putnam-2022-b6-implies-term
      (putnam-2022-b6-and-terms
       (list
        (list 'putnam-2022-b6-positive-real-p 'left)
        (list 'putnam-2022-b6-positive-real-p 'right)
        (list 'putnam-2022-b6-real-equal-p
              'left 'right)))
      (list 'putnam-2022-b6-real-equal-p
            left-output right-output)))))

(defun putnam-2022-b6-positive-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2022-b6-positive-function-output-function
     function)
    (putnam-2022-b6-true-function '(x)))
   (fn-equal
    (putnam-2022-b6-positive-function-extensional-function
     function)
    (putnam-2022-b6-true-function
     '(left right)))))

(defun putnam-2022-b6-functional-equation-function
    (function)
  (let* ((fx
          (putnam-2022-b6-apply-term function '(x)))
         (fy
          (putnam-2022-b6-apply-term function '(y)))
         (x-times-fy
          (list 'putnam-2022-b6-multiply-name 'x fy))
         (y-times-fx
          (list 'putnam-2022-b6-multiply-name 'y fx))
         (at-x-times-fy
          (putnam-2022-b6-apply-term
           function (list x-times-fy)))
         (at-y-times-fx
          (putnam-2022-b6-apply-term
           function (list y-times-fx)))
         (at-x-plus-y
          (putnam-2022-b6-apply-term
           function
           (list
            (list 'putnam-2022-b6-add-name 'x 'y))))
         (left
          (list 'putnam-2022-b6-add-name
                at-x-times-fy at-y-times-fx))
         (right
          (list
           'putnam-2022-b6-add-name
           (putnam-2022-b6-quoted
            (putnam-2022-b6-rational-name 1))
           at-x-plus-y)))
    (list
     'lambda
     '(x y)
     (putnam-2022-b6-implies-term
      (putnam-2022-b6-and-terms
       (list
        (list 'putnam-2022-b6-positive-real-p 'x)
        (list 'putnam-2022-b6-positive-real-p 'y)))
      (list 'putnam-2022-b6-real-equal-p
            left right)))))

(defun putnam-2022-b6-functional-equation-p
    (function)
  (fn-equal
   (putnam-2022-b6-functional-equation-function
    function)
   (putnam-2022-b6-true-function '(x y))))

(defun putnam-2022-b6-continuity-delta-function
    (function x epsilon delta)
  (let* ((fx
          (putnam-2022-b6-apply-term
           function
           (list (putnam-2022-b6-quoted x))))
         (fy
          (putnam-2022-b6-apply-term function '(y)))
         (input-distance
          (list 'putnam-2022-b6-distance-name
                (putnam-2022-b6-quoted x)
                'y))
         (output-distance
          (list 'putnam-2022-b6-distance-name
                fx fy))
         (delta-name
          (putnam-2022-b6-rational-name delta))
         (epsilon-name
          (putnam-2022-b6-rational-name epsilon)))
    (list
     'lambda
     '(y)
     (putnam-2022-b6-implies-term
      (putnam-2022-b6-and-terms
       (list
        (list 'putnam-2022-b6-positive-real-p 'y)
        (list 'putnam-2022-b6-real-lt-p
              input-distance
              (putnam-2022-b6-quoted delta-name))))
      (list 'putnam-2022-b6-real-lt-p
            output-distance
            (putnam-2022-b6-quoted epsilon-name))))))

(defun putnam-2022-b6-continuity-delta-p
    (function x epsilon delta)
  (let ((condition
         (putnam-2022-b6-continuity-delta-function
          function x epsilon delta))
        (true-function
         (putnam-2022-b6-true-function '(y))))
    (and
     (rationalp delta)
     (< 0 delta)
     (tamep-functionp condition)
     (tamep-functionp true-function)
     (fn-equal condition true-function))))

(defun putnam-2022-b6-continuity-delta-failure-function
    (function x epsilon)
  (list
   'lambda
   '(delta)
   (list
    'if
    (list
     'putnam-2022-b6-continuity-delta-p
     (putnam-2022-b6-quoted function)
     (putnam-2022-b6-quoted x)
     (putnam-2022-b6-quoted epsilon)
     'delta)
    (putnam-2022-b6-quoted nil)
    (putnam-2022-b6-quoted t))))

(defun putnam-2022-b6-continuous-at-scale-p
    (function x epsilon)
  (let ((failure-function
         (putnam-2022-b6-continuity-delta-failure-function
          function x epsilon))
        (true-function
         (putnam-2022-b6-true-function '(delta))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnam-2022-b6-continuity-function (function)
  (list
   'lambda
   '(x epsilon)
   (putnam-2022-b6-implies-term
    (putnam-2022-b6-and-terms
     (list
      (list 'putnam-2022-b6-positive-real-p 'x)
      (putnam-2022-b6-positive-rational-term 'epsilon)))
    (list
     'putnam-2022-b6-continuous-at-scale-p
     (putnam-2022-b6-quoted function)
     'x
     'epsilon))))

(defun putnam-2022-b6-continuous-p (function)
  (let ((condition
         (putnam-2022-b6-continuity-function function))
        (true-function
         (putnam-2022-b6-true-function
          '(x epsilon))))
    (and
     (tamep-functionp condition)
     (tamep-functionp true-function)
     (fn-equal condition true-function))))

(defun putnam-2022-b6-solution-equality-function
    (function coefficient)
  (let* ((one-name
          (putnam-2022-b6-rational-name 1))
         (coefficient-times-x
          (list 'putnam-2022-b6-multiply-name
                (putnam-2022-b6-quoted coefficient)
                'x))
         (denominator
          (list 'putnam-2022-b6-add-name
                (putnam-2022-b6-quoted one-name)
                coefficient-times-x))
         (function-value
          (putnam-2022-b6-apply-term function '(x)))
         (product
          (list 'putnam-2022-b6-multiply-name
                denominator function-value)))
    (list
     'lambda
     '(x)
     (putnam-2022-b6-implies-term
      (list 'putnam-2022-b6-positive-real-p 'x)
      (list 'putnam-2022-b6-real-equal-p
            product
            (putnam-2022-b6-quoted one-name))))))

(defun putnam-2022-b6-solution-witness-p
    (coefficient function)
  (let ((zero-name
         (putnam-2022-b6-rational-name 0))
        (equality-function
         (putnam-2022-b6-solution-equality-function
          function coefficient))
        (true-function
         (putnam-2022-b6-true-function '(x))))
    (and
     (putnam-2022-b6-real-name-p coefficient)
     (putnam-2022-b6-real-le-p
      zero-name coefficient)
     (tamep-functionp equality-function)
     (tamep-functionp true-function)
     (fn-equal equality-function true-function))))

(defun putnam-2022-b6-solution-failure-function
    (function)
  (list
   'lambda
   '(coefficient)
   (list
    'if
    (list
     'putnam-2022-b6-solution-witness-p
     'coefficient
     (putnam-2022-b6-quoted function))
    (putnam-2022-b6-quoted nil)
    (putnam-2022-b6-quoted t))))

(defun putnam-2022-b6-solution-exists-p (function)
  (let ((failure-function
         (putnam-2022-b6-solution-failure-function
          function))
        (true-function
         (putnam-2022-b6-true-function
          '(coefficient))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2022-b6-statement (function)
  (implies
   (putnam-2022-b6-positive-function-p function)
   (iff
    (and
     (putnam-2022-b6-continuous-p function)
     (putnam-2022-b6-functional-equation-p function))
    (putnam-2022-b6-solution-exists-p function))))

(value-triple :itpeval-statement-checked)
:q
