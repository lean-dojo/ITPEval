;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_b5:
;; bounded real functions with values at least one admit two real functions
;; whose affine suprema equal the suprema of g1(s)^x*g2(s). This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, and real functions are extensional
;; ACL2 function objects on those names. FN-EQUAL supplies unbounded universal
;; quantification over names and function objects; NOT/FN-EQUAL supplies the
;; source's internal existential quantifiers, so no finite carrier or external
;; witness replaces a source quantifier.
;;
;; A power oracle P(s,x) is bundled into the conclusion witness. Positivity,
;; P(s,0)=1, P(s,1)=g1(s), multiplicativity in x, and monotonicity in x
;; uniquely characterize g1(s)^x because g1(s)>=1. Every such base has this
;; oracle, so adding it as a definitional witness is bidirectionally
;; equivalent to using real powr.
;;
;; A common value is the supremum of each displayed family exactly when it is
;; an upper bound and is below every upper bound. The source hypotheses make
;; the left family nonempty and bounded for every real x. Thus the internal
;; common-supremum function is exactly equivalent to equality of the two sSup
;; values, including boundedness of the affine family.

(defun putnam-2012-b5-quoted (object)
  (list 'quote object))

(defun putnam-2012-b5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2012-b5-term-list (cdr terms)))
    nil))

(defun putnam-2012-b5-apply-term (function arguments)
  (list 'apply$
        (putnam-2012-b5-quoted function)
        (putnam-2012-b5-term-list arguments)))

(defun putnam-2012-b5-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-2012-b5-term-list arguments)))

(defun putnam-2012-b5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2012-b5-and-terms (cdr terms))
            (putnam-2012-b5-quoted nil))
    (putnam-2012-b5-quoted t)))

(defun putnam-2012-b5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2012-b5-quoted t)))

(defun putnam-2012-b5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2012-b5-negate-term (value)
  (list 'unary-- value))

(defun putnam-2012-b5-subtract-term (left right)
  (putnam-2012-b5-add-term
   left
   (putnam-2012-b5-negate-term right)))

(defun putnam-2012-b5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2012-b5-divide-term (numerator denominator)
  (putnam-2012-b5-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2012-b5-absolute-term (value)
  (list 'if
        (list '< value (putnam-2012-b5-quoted 0))
        (putnam-2012-b5-negate-term value)
        value))

(defun putnam-2012-b5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2012-b5-quoted nil)
        (putnam-2012-b5-quoted t)))

(defun putnam-2012-b5-positive-rational-term (value)
  (putnam-2012-b5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2012-b5-quoted 0) value))))

(defun putnam-2012-b5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2012-b5-quoted t)))

(defun putnam-2012-b5-real-value-term (name precision)
  (putnam-2012-b5-apply-term name (list precision)))

(defun putnam-2012-b5-object-real-value-term
    (name-term precision)
  (putnam-2012-b5-apply-object-term
   name-term
   (list precision)))

(defun putnam-2012-b5-real-cauchy-function (name)
  (let* ((left
          (putnam-2012-b5-real-value-term name 'epsilon))
         (right
          (putnam-2012-b5-real-value-term name 'eta))
         (distance
          (putnam-2012-b5-absolute-term
           (putnam-2012-b5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2012-b5-implies-term
      (putnam-2012-b5-and-terms
       (list
        (putnam-2012-b5-positive-rational-term 'epsilon)
        (putnam-2012-b5-positive-rational-term 'eta)))
      (putnam-2012-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2012-b5-less-equal-term
         distance
         (putnam-2012-b5-add-term
          'epsilon 'eta))))))))

(defun putnam-2012-b5-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2012-b5-real-cauchy-function name)
    (putnam-2012-b5-true-function
     '(epsilon eta)))))

;; Sampling at eta/4 makes these universal rational inequalities exact
;; predicates on the represented real limits.

(defun putnam-2012-b5-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-2012-b5-multiply-term 1/4 'eta))
         (left
          (putnam-2012-b5-real-value-term
           left-name precision))
         (right
          (putnam-2012-b5-real-value-term
           right-name precision))
         (distance
          (putnam-2012-b5-absolute-term
           (putnam-2012-b5-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-2012-b5-implies-term
      (putnam-2012-b5-positive-rational-term 'eta)
      (putnam-2012-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2012-b5-less-equal-term
         distance
         (putnam-2012-b5-add-term
          (putnam-2012-b5-quoted bound)
          'eta))))))))

(defun putnam-2012-b5-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-2012-b5-real-name-p left-name)
   (putnam-2012-b5-real-name-p right-name)
   (fn-equal
    (putnam-2012-b5-real-distance-function
     left-name right-name bound)
    (putnam-2012-b5-true-function '(eta)))))

(defun putnam-2012-b5-real-equal-p
    (left-name right-name)
  (putnam-2012-b5-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-2012-b5-real-order-function
    (left-name right-name)
  (let* ((precision
          (putnam-2012-b5-multiply-term 1/4 'eta))
         (left
          (putnam-2012-b5-real-value-term
           left-name precision))
         (right
          (putnam-2012-b5-real-value-term
           right-name precision)))
    (list
     'lambda
     '(eta)
     (putnam-2012-b5-implies-term
      (putnam-2012-b5-positive-rational-term 'eta)
      (putnam-2012-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2012-b5-less-equal-term
         left
         (putnam-2012-b5-add-term
          right 'eta))))))))

(defun putnam-2012-b5-real-le-p
    (left-name right-name)
  (and
   (putnam-2012-b5-real-name-p left-name)
   (putnam-2012-b5-real-name-p right-name)
   (fn-equal
    (putnam-2012-b5-real-order-function
     left-name right-name)
    (putnam-2012-b5-true-function '(eta)))))

(defun putnam-2012-b5-real-lt-p
    (left-name right-name)
  (and
   (putnam-2012-b5-real-le-p left-name right-name)
   (not
    (putnam-2012-b5-real-equal-p
     left-name right-name))))

(defun putnam-2012-b5-rational-name (value)
  (list 'lambda
        '(precision)
        (putnam-2012-b5-quoted value)))

(defun putnam-2012-b5-add-name (left-name right-name)
  (let* ((precision
          (putnam-2012-b5-multiply-term 1/2 'epsilon))
         (left
          (putnam-2012-b5-object-real-value-term
           (putnam-2012-b5-quoted left-name)
           precision))
         (right
          (putnam-2012-b5-object-real-value-term
           (putnam-2012-b5-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2012-b5-add-term left right))))

(defun putnam-2012-b5-multiply-name
    (left-name right-name)
  (let* ((left-at-one
          (putnam-2012-b5-object-real-value-term
           (putnam-2012-b5-quoted left-name)
           1))
         (right-at-one
          (putnam-2012-b5-object-real-value-term
           (putnam-2012-b5-quoted right-name)
           1))
         (scale
          (putnam-2012-b5-multiply-term
           8
           (putnam-2012-b5-add-term
            3
            (putnam-2012-b5-add-term
             (putnam-2012-b5-absolute-term left-at-one)
             (putnam-2012-b5-absolute-term right-at-one)))))
         (candidate
          (putnam-2012-b5-divide-term
           'epsilon scale))
         (precision
          (list 'if
                (list '< 1 candidate)
                1
                candidate))
         (left
          (putnam-2012-b5-object-real-value-term
           (putnam-2012-b5-quoted left-name)
           precision))
         (right
          (putnam-2012-b5-object-real-value-term
           (putnam-2012-b5-quoted right-name)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2012-b5-multiply-term left right))))

(defun putnam-2012-b5-unary-output-function
    (function)
  (let ((output
         (putnam-2012-b5-apply-term function '(x))))
    (list
     'lambda
     '(x)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-name-p 'x)
      (list 'putnam-2012-b5-real-name-p output)))))

(defun putnam-2012-b5-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-2012-b5-apply-term
          function '(left)))
        (right-output
         (putnam-2012-b5-apply-term
          function '(right))))
    (list
     'lambda
     '(left right)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-equal-p
            'left 'right)
      (list 'putnam-2012-b5-real-equal-p
            left-output right-output)))))

(defun putnam-2012-b5-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-2012-b5-unary-output-function function)
    (putnam-2012-b5-true-function '(x)))
   (fn-equal
    (putnam-2012-b5-unary-extensional-function function)
    (putnam-2012-b5-true-function
     '(left right)))))

(defun putnam-2012-b5-lower-one-function (function)
  (let ((value
         (putnam-2012-b5-apply-term function '(x))))
    (list
     'lambda
     '(x)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-name-p 'x)
      (list
       'putnam-2012-b5-real-le-p
       (putnam-2012-b5-quoted
        (putnam-2012-b5-rational-name 1))
       value)))))

(defun putnam-2012-b5-lower-one-p (function)
  (fn-equal
   (putnam-2012-b5-lower-one-function function)
   (putnam-2012-b5-true-function '(x))))

(defun putnam-2012-b5-bound-function
    (g1 g2 bound1 bound2)
  (let ((value1
         (putnam-2012-b5-apply-term g1 '(x)))
        (value2
         (putnam-2012-b5-apply-term g2 '(x))))
    (list
     'lambda
     '(x)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-name-p 'x)
      (putnam-2012-b5-and-terms
       (list
        (list 'putnam-2012-b5-real-le-p
              value1
              (putnam-2012-b5-quoted bound1))
        (list 'putnam-2012-b5-real-le-p
              value2
              (putnam-2012-b5-quoted bound2))))))))

(defun putnam-2012-b5-bound-witness-p
    (witness g1 g2)
  (and
   (true-listp witness)
   (equal (len witness) 2)
   (let ((bound1 (nth 0 witness))
         (bound2 (nth 1 witness)))
     (and
      (putnam-2012-b5-real-name-p bound1)
      (putnam-2012-b5-real-name-p bound2)
      (fn-equal
       (putnam-2012-b5-bound-function
        g1 g2 bound1 bound2)
       (putnam-2012-b5-true-function '(x)))))))

(defun putnam-2012-b5-bound-failure-function (g1 g2)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list 'putnam-2012-b5-bound-witness-p
          'witness
          (putnam-2012-b5-quoted g1)
          (putnam-2012-b5-quoted g2))
    (putnam-2012-b5-quoted nil)
    (putnam-2012-b5-quoted t))))

(defun putnam-2012-b5-bounds-exist-p (g1 g2)
  (not
   (fn-equal
    (putnam-2012-b5-bound-failure-function g1 g2)
    (putnam-2012-b5-true-function '(witness)))))

(defun putnam-2012-b5-power-output-function (power)
  (let ((output
         (putnam-2012-b5-apply-term power '(s x))))
    (list
     'lambda
     '(s x)
     (putnam-2012-b5-implies-term
      (putnam-2012-b5-and-terms
       (list
        (list 'putnam-2012-b5-real-name-p 's)
        (list 'putnam-2012-b5-real-name-p 'x)))
      (list 'putnam-2012-b5-real-name-p output)))))

(defun putnam-2012-b5-power-extensional-function (power)
  (let ((left-output
         (putnam-2012-b5-apply-term
          power '(s-left x-left)))
        (right-output
         (putnam-2012-b5-apply-term
          power '(s-right x-right))))
    (list
     'lambda
     '(s-left s-right x-left x-right)
     (putnam-2012-b5-implies-term
      (putnam-2012-b5-and-terms
       (list
        (list 'putnam-2012-b5-real-equal-p
              's-left 's-right)
        (list 'putnam-2012-b5-real-equal-p
              'x-left 'x-right)))
      (list 'putnam-2012-b5-real-equal-p
            left-output right-output)))))

(defun putnam-2012-b5-power-law-function (g1 power)
  (let* ((zero-name
          (putnam-2012-b5-rational-name 0))
         (one-name
          (putnam-2012-b5-rational-name 1))
         (at-x
          (putnam-2012-b5-apply-term power '(s x)))
         (at-y
          (putnam-2012-b5-apply-term power '(s y)))
         (at-zero
          (putnam-2012-b5-apply-term
           power
           (list 's
                 (putnam-2012-b5-quoted zero-name))))
         (at-one
          (putnam-2012-b5-apply-term
           power
           (list 's
                 (putnam-2012-b5-quoted one-name))))
         (base
          (putnam-2012-b5-apply-term g1 '(s)))
         (sum-name
          (list 'putnam-2012-b5-add-name 'x 'y))
         (at-sum
          (putnam-2012-b5-apply-term
           power
           (list 's sum-name)))
         (product-name
          (list 'putnam-2012-b5-multiply-name
                at-x at-y)))
    (list
     'lambda
     '(s x y)
     (putnam-2012-b5-implies-term
      (putnam-2012-b5-and-terms
       (list
        (list 'putnam-2012-b5-real-name-p 's)
        (list 'putnam-2012-b5-real-name-p 'x)
        (list 'putnam-2012-b5-real-name-p 'y)))
      (putnam-2012-b5-and-terms
       (list
        (list 'putnam-2012-b5-real-lt-p
              (putnam-2012-b5-quoted zero-name)
              at-x)
        (list 'putnam-2012-b5-real-equal-p
              at-zero
              (putnam-2012-b5-quoted one-name))
        (list 'putnam-2012-b5-real-equal-p
              at-one base)
        (list 'putnam-2012-b5-real-equal-p
              at-sum product-name)
        (putnam-2012-b5-implies-term
         (list 'putnam-2012-b5-real-le-p 'x 'y)
         (list 'putnam-2012-b5-real-le-p
               at-x at-y))))))))

(defun putnam-2012-b5-power-oracle-p (g1 power)
  (and
   (tamep-functionp power)
   (fn-equal
    (putnam-2012-b5-power-output-function power)
    (putnam-2012-b5-true-function '(s x)))
   (fn-equal
    (putnam-2012-b5-power-extensional-function power)
    (putnam-2012-b5-true-function
     '(s-left s-right x-left x-right)))
   (fn-equal
    (putnam-2012-b5-power-law-function g1 power)
    (putnam-2012-b5-true-function '(s x y)))))

(defun putnam-2012-b5-left-upper-bound-function
    (g2 power x bound)
  (let* ((power-value
          (putnam-2012-b5-apply-term
           power
           (list 's
                 (putnam-2012-b5-quoted x))))
         (g2-value
          (putnam-2012-b5-apply-term g2 '(s)))
         (family-value
          (list 'putnam-2012-b5-multiply-name
                power-value g2-value)))
    (list
     'lambda
     '(s)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-name-p 's)
      (list 'putnam-2012-b5-real-le-p
            family-value
            (putnam-2012-b5-quoted bound))))))

(defun putnam-2012-b5-left-upper-bound-p
    (g2 power x bound)
  (and
   (putnam-2012-b5-real-name-p x)
   (putnam-2012-b5-real-name-p bound)
   (fn-equal
    (putnam-2012-b5-left-upper-bound-function
     g2 power x bound)
    (putnam-2012-b5-true-function '(s)))))

(defun putnam-2012-b5-left-least-function
    (g2 power x supremum)
  (list
   'lambda
   '(bound)
   (putnam-2012-b5-implies-term
    (putnam-2012-b5-and-terms
     (list
      (list 'putnam-2012-b5-real-name-p 'bound)
      (list 'putnam-2012-b5-left-upper-bound-p
            (putnam-2012-b5-quoted g2)
            (putnam-2012-b5-quoted power)
            (putnam-2012-b5-quoted x)
            'bound)))
    (list 'putnam-2012-b5-real-le-p
          (putnam-2012-b5-quoted supremum)
          'bound))))

(defun putnam-2012-b5-left-supremum-p
    (g2 power x supremum)
  (and
   (putnam-2012-b5-left-upper-bound-p
    g2 power x supremum)
   (fn-equal
    (putnam-2012-b5-left-least-function
     g2 power x supremum)
    (putnam-2012-b5-true-function '(bound)))))

(defun putnam-2012-b5-right-upper-bound-function
    (h1 h2 x bound)
  (let* ((h1-value
          (putnam-2012-b5-apply-term h1 '(t-index)))
         (h2-value
          (putnam-2012-b5-apply-term h2 '(t-index)))
         (product
          (list 'putnam-2012-b5-multiply-name
                (putnam-2012-b5-quoted x)
                h1-value))
         (family-value
          (list 'putnam-2012-b5-add-name
                product h2-value)))
    (list
     'lambda
     '(t-index)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-name-p 't-index)
      (list 'putnam-2012-b5-real-le-p
            family-value
            (putnam-2012-b5-quoted bound))))))

(defun putnam-2012-b5-right-upper-bound-p
    (h1 h2 x bound)
  (and
   (putnam-2012-b5-real-name-p x)
   (putnam-2012-b5-real-name-p bound)
   (fn-equal
    (putnam-2012-b5-right-upper-bound-function
     h1 h2 x bound)
    (putnam-2012-b5-true-function '(t-index)))))

(defun putnam-2012-b5-right-least-function
    (h1 h2 x supremum)
  (list
   'lambda
   '(bound)
   (putnam-2012-b5-implies-term
    (putnam-2012-b5-and-terms
     (list
      (list 'putnam-2012-b5-real-name-p 'bound)
      (list 'putnam-2012-b5-right-upper-bound-p
            (putnam-2012-b5-quoted h1)
            (putnam-2012-b5-quoted h2)
            (putnam-2012-b5-quoted x)
            'bound)))
    (list 'putnam-2012-b5-real-le-p
          (putnam-2012-b5-quoted supremum)
          'bound))))

(defun putnam-2012-b5-right-supremum-p
    (h1 h2 x supremum)
  (and
   (putnam-2012-b5-right-upper-bound-p
    h1 h2 x supremum)
   (fn-equal
    (putnam-2012-b5-right-least-function
     h1 h2 x supremum)
    (putnam-2012-b5-true-function '(bound)))))

(defun putnam-2012-b5-common-supremum-function
    (g2 power h1 h2 supremum-function)
  (let ((supremum
         (putnam-2012-b5-apply-term
          supremum-function '(x))))
    (list
     'lambda
     '(x)
     (putnam-2012-b5-implies-term
      (list 'putnam-2012-b5-real-name-p 'x)
      (putnam-2012-b5-and-terms
       (list
        (list 'putnam-2012-b5-left-supremum-p
              (putnam-2012-b5-quoted g2)
              (putnam-2012-b5-quoted power)
              'x
              supremum)
        (list 'putnam-2012-b5-right-supremum-p
              (putnam-2012-b5-quoted h1)
              (putnam-2012-b5-quoted h2)
              'x
              supremum)))))))

(defun putnam-2012-b5-conclusion-witness-p
    (witness g1 g2)
  (and
   (true-listp witness)
   (equal (len witness) 4)
   (let ((power (nth 0 witness))
         (h1 (nth 1 witness))
         (h2 (nth 2 witness))
         (supremum-function (nth 3 witness)))
     (and
      (putnam-2012-b5-power-oracle-p g1 power)
      (putnam-2012-b5-real-function-p h1)
      (putnam-2012-b5-real-function-p h2)
      (putnam-2012-b5-real-function-p
       supremum-function)
      (fn-equal
       (putnam-2012-b5-common-supremum-function
        g2 power h1 h2 supremum-function)
       (putnam-2012-b5-true-function '(x)))))))

(defun putnam-2012-b5-conclusion-failure-function
    (g1 g2)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list 'putnam-2012-b5-conclusion-witness-p
          'witness
          (putnam-2012-b5-quoted g1)
          (putnam-2012-b5-quoted g2))
    (putnam-2012-b5-quoted nil)
    (putnam-2012-b5-quoted t))))

(defun putnam-2012-b5-conclusion-exists-p (g1 g2)
  (not
   (fn-equal
    (putnam-2012-b5-conclusion-failure-function
     g1 g2)
    (putnam-2012-b5-true-function '(witness)))))

(defun putnambench-putnam-2012-b5-statement (g1 g2)
  (implies
   (and
    (putnam-2012-b5-real-function-p g1)
    (putnam-2012-b5-real-function-p g2)
    (putnam-2012-b5-lower-one-p g1)
    (putnam-2012-b5-lower-one-p g2)
    (putnam-2012-b5-bounds-exist-p g1 g2))
   (putnam-2012-b5-conclusion-exists-p g1 g2)))

(value-triple :itpeval-statement-checked)
:q
