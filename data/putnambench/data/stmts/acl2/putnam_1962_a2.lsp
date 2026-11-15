;; Statement-only formalization of PutnamBench corpus artifact putnam_1962_a2:
;; classification of real functions whose interval average equals the
;; geometric mean of the endpoint values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The published problem and the Lean primary source split into a
;; nondegenerate rational family and zero-integral degeneracies. If f(0)=0,
;; the displayed equation is exactly the zero-average branch already present
;; in the Lean solution set. If f(0)>0 but f vanishes to the right of zero,
;; it is the separate spike branch. In every remaining case the equation
;; makes the indefinite integral positive and forces f to be continuous; the
;; usual separation-of-variables argument gives
;;
;;                   f(x) = f(0)/(1-c*x)^2.
;;
;; Thus all nontrivial counterexamples lie in the continuous f(0)>0 core
;; encoded below. The Lean truncated representative and the global rational
;; representative agree on every interval before the pole, so this
;; interval-wise formulation also preserves that representational choice.
;;
;; FUNCTION(x,epsilon) is a rational regular Cauchy name for f(x) at rational
;; x. A modulus on every bounded rational interval represents continuity on
;; the whole real line. Rational inputs and positive rational endpoints are
;; bidirectionally sufficient: continuity extends identities to real inputs,
;; and any real interval counterexample persists on a smaller rational
;; endpoint. The parameter c is itself a regular Cauchy name, so no real is
;; replaced by a rational.
;;
;; For positive rational x, the average is represented by right Riemann sums
;;
;;       (1/n) * sum_(i=1)^n f(i*x/n).
;;
;; In the continuous core these converge exactly to (1/x)*integral_0^x f.
;; Since f is nonnegative, equality with sqrt(f(0)*f(x)) is equivalent to
;; equality of the squares. Internal cutoff functions express convergence
;; and are existential witnesses, not external statement parameters.

(defun putnam-1962-a2-quoted (object)
  (list 'quote object))

(defun putnam-1962-a2-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1962-a2-term-list (cdr terms)))
    nil))

(defun putnam-1962-a2-apply-term (function arguments)
  (list 'apply$
        (putnam-1962-a2-quoted function)
        (putnam-1962-a2-term-list arguments)))

(defun putnam-1962-a2-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1962-a2-and-terms (cdr terms))
            (putnam-1962-a2-quoted nil))
    (putnam-1962-a2-quoted t)))

(defun putnam-1962-a2-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1962-a2-quoted t)))

(defun putnam-1962-a2-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1962-a2-negate-term (value)
  (list 'unary-- value))

(defun putnam-1962-a2-subtract-term (left right)
  (putnam-1962-a2-add-term
   left
   (putnam-1962-a2-negate-term right)))

(defun putnam-1962-a2-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1962-a2-divide-term (numerator denominator)
  (putnam-1962-a2-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-1962-a2-absolute-term (value)
  (list 'if
        (list '< value (putnam-1962-a2-quoted 0))
        (putnam-1962-a2-negate-term value)
        value))

(defun putnam-1962-a2-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-1962-a2-quoted nil)
        (putnam-1962-a2-quoted t)))

(defun putnam-1962-a2-positive-rational-term (value)
  (putnam-1962-a2-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-1962-a2-quoted 0) value))))

(defun putnam-1962-a2-bounded-rational-term
    (value bound)
  (putnam-1962-a2-and-terms
   (list
    (list 'rationalp value)
    (putnam-1962-a2-less-equal-term
     (putnam-1962-a2-negate-term bound)
     value)
    (putnam-1962-a2-less-equal-term value bound))))

(defun putnam-1962-a2-true-function (formals)
  (list 'lambda
        formals
        (putnam-1962-a2-quoted t)))

(defun putnam-1962-a2-function-term
    (function x precision)
  (putnam-1962-a2-apply-term
   function
   (list x precision)))

(defun putnam-1962-a2-function-cauchy-matrix (function)
  (let* ((at-epsilon
          (putnam-1962-a2-function-term
           function 'x 'epsilon))
         (at-eta
          (putnam-1962-a2-function-term
           function 'x 'eta))
         (distance
          (putnam-1962-a2-absolute-term
           (putnam-1962-a2-subtract-term
            at-epsilon at-eta))))
    (list
     'lambda
     '(x epsilon eta)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp 'x)
        (putnam-1962-a2-positive-rational-term 'epsilon)
        (putnam-1962-a2-positive-rational-term 'eta)))
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp at-epsilon)
        (list 'rationalp at-eta)
        (putnam-1962-a2-less-equal-term
         distance
         (putnam-1962-a2-add-term
          'epsilon 'eta))))))))

(defun putnam-1962-a2-function-cauchy-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-1962-a2-function-cauchy-matrix function)
    (putnam-1962-a2-true-function
     '(x epsilon eta)))))

(defun putnam-1962-a2-modulus-positive-matrix (modulus)
  (let ((delta
         (putnam-1962-a2-apply-term
          modulus '(bound epsilon))))
    (list
     'lambda
     '(bound epsilon)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (putnam-1962-a2-positive-rational-term 'bound)
        (putnam-1962-a2-positive-rational-term 'epsilon)))
      (putnam-1962-a2-positive-rational-term delta)))))

(defun putnam-1962-a2-continuity-matrix
    (function modulus)
  (let* ((delta
          (putnam-1962-a2-apply-term
           modulus '(bound epsilon)))
         (precision
          (putnam-1962-a2-multiply-term 1/4 'epsilon))
         (left
          (putnam-1962-a2-function-term
           function 'x precision))
         (right
          (putnam-1962-a2-function-term
           function 'y precision))
         (input-distance
          (putnam-1962-a2-absolute-term
           (putnam-1962-a2-subtract-term 'x 'y)))
         (output-distance
          (putnam-1962-a2-absolute-term
           (putnam-1962-a2-subtract-term left right))))
    (list
     'lambda
     '(bound x y epsilon)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (putnam-1962-a2-positive-rational-term 'bound)
        (putnam-1962-a2-bounded-rational-term 'x 'bound)
        (putnam-1962-a2-bounded-rational-term 'y 'bound)
        (putnam-1962-a2-positive-rational-term 'epsilon)
        (putnam-1962-a2-positive-rational-term delta)
        (list '< input-distance delta)))
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1962-a2-less-equal-term
         output-distance 'epsilon)))))))

(defun putnam-1962-a2-continuity-witness-p
    (function modulus)
  (and
   (tamep-functionp modulus)
   (fn-equal
    (putnam-1962-a2-modulus-positive-matrix modulus)
    (putnam-1962-a2-true-function
     '(bound epsilon)))
   (fn-equal
    (putnam-1962-a2-continuity-matrix
     function modulus)
    (putnam-1962-a2-true-function
     '(bound x y epsilon)))))

(defun putnam-1962-a2-continuity-failure-function
    (function)
  (list
   'lambda
   '(modulus)
   (list
    'if
    (list
     'putnam-1962-a2-continuity-witness-p
     (putnam-1962-a2-quoted function)
     'modulus)
    (putnam-1962-a2-quoted nil)
    (putnam-1962-a2-quoted t))))

(defun putnam-1962-a2-continuous-p (function)
  (let ((failure
         (putnam-1962-a2-continuity-failure-function
          function))
        (always-true
         (putnam-1962-a2-true-function '(modulus))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-1962-a2-nonnegative-matrix (function)
  (let ((value
         (putnam-1962-a2-function-term
          function 'x 'epsilon)))
    (list
     'lambda
     '(x epsilon)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp 'x)
        (putnam-1962-a2-positive-rational-term 'epsilon)))
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp value)
        (putnam-1962-a2-less-equal-term
         (putnam-1962-a2-negate-term 'epsilon)
         value)))))))

(defun putnam-1962-a2-nonnegative-p (function)
  (fn-equal
   (putnam-1962-a2-nonnegative-matrix function)
   (putnam-1962-a2-true-function '(x epsilon))))

(defun putnam-1962-a2-positive-zero-matrix
    (function lower-bound)
  (let ((value
         (putnam-1962-a2-function-term
          function
          (putnam-1962-a2-quoted 0)
          'epsilon)))
    (list
     'lambda
     '(epsilon)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-positive-rational-term 'epsilon)
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp value)
        (putnam-1962-a2-less-equal-term
         (putnam-1962-a2-quoted lower-bound)
         (putnam-1962-a2-add-term
          value 'epsilon))))))))

(defun putnam-1962-a2-positive-zero-witness-p
    (function lower-bound)
  (and
   (rationalp lower-bound)
   (< 0 lower-bound)
   (fn-equal
    (putnam-1962-a2-positive-zero-matrix
     function lower-bound)
    (putnam-1962-a2-true-function '(epsilon)))))

(defun putnam-1962-a2-positive-zero-failure-function
    (function)
  (list
   'lambda
   '(lower-bound)
   (list
    'if
    (list
     'putnam-1962-a2-positive-zero-witness-p
     (putnam-1962-a2-quoted function)
     'lower-bound)
    (putnam-1962-a2-quoted nil)
    (putnam-1962-a2-quoted t))))

(defun putnam-1962-a2-positive-at-zero-p (function)
  (let ((failure
         (putnam-1962-a2-positive-zero-failure-function
          function))
        (always-true
         (putnam-1962-a2-true-function '(lower-bound))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-1962-a2-real-name-matrix (name)
  (let* ((left
          (putnam-1962-a2-apply-term
           name '(epsilon)))
         (right
          (putnam-1962-a2-apply-term
           name '(eta)))
         (distance
          (putnam-1962-a2-absolute-term
           (putnam-1962-a2-subtract-term
            left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (putnam-1962-a2-positive-rational-term 'epsilon)
        (putnam-1962-a2-positive-rational-term 'eta)))
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1962-a2-less-equal-term
         distance
         (putnam-1962-a2-add-term
          'epsilon 'eta))))))))

(defun putnam-1962-a2-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-1962-a2-real-name-matrix name)
    (putnam-1962-a2-true-function
     '(epsilon eta)))))

(defun putnam-1962-a2-domain-term (x endpoint positive-only)
  (putnam-1962-a2-and-terms
   (append
    (list
     (list 'rationalp x)
     (if positive-only
         (list '< (putnam-1962-a2-quoted 0) x)
       (putnam-1962-a2-less-equal-term
        (putnam-1962-a2-quoted 0) x)))
    (if endpoint
        (list
         (list '< x
               (putnam-1962-a2-quoted endpoint)))
      nil))))

;; SUM$+ keeps the generated universal convergence matrices tame.

(defun putnam-1962-a2-singleton-function ()
  '(lambda (value) (cons value 'nil)))

(defun putnam-1962-a2-index-tuples-term (upper)
  (list
   'collect$
   (putnam-1962-a2-quoted
    (putnam-1962-a2-singleton-function))
   (list
    'from-to-by
    (putnam-1962-a2-quoted 1)
    upper
    (putnam-1962-a2-quoted 1))))

(defun putnam-1962-a2-grid-summand-function (function)
  (let* ((x
          (list 'nth
                (putnam-1962-a2-quoted 0)
                'globals))
         (precision
          (list 'nth
                (putnam-1962-a2-quoted 1)
                'globals))
         (subdivisions
          (list 'nth
                (putnam-1962-a2-quoted 2)
                'globals))
         (index (list 'car 'index-tuple))
         (sample
          (putnam-1962-a2-divide-term
           (putnam-1962-a2-multiply-term x index)
           subdivisions)))
    (list
     'lambda
     '(globals index-tuple)
     (putnam-1962-a2-function-term
      function sample precision))))

(defun putnam-1962-a2-average-term
    (function x precision subdivisions)
  (let ((summand
         (putnam-1962-a2-grid-summand-function
          function)))
    (putnam-1962-a2-divide-term
     (list
      'sum$+
      (putnam-1962-a2-quoted summand)
      (putnam-1962-a2-term-list
       (list x precision subdivisions))
      (putnam-1962-a2-index-tuples-term subdivisions))
     subdivisions)))

(defun putnam-1962-a2-cutoff-positive-matrix
    (cutoff endpoint positive-only)
  (let ((index
         (putnam-1962-a2-apply-term
          cutoff '(x epsilon))))
    (list
     'lambda
     '(x epsilon)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (putnam-1962-a2-domain-term
         'x endpoint positive-only)
        (putnam-1962-a2-positive-rational-term 'epsilon)))
      (putnam-1962-a2-and-terms
       (list
        (list 'natp index)
        (list '< (putnam-1962-a2-quoted 0)
              index)))))))

(defun putnam-1962-a2-average-equation-matrix
    (function endpoint cutoff)
  (let* ((index
          (putnam-1962-a2-apply-term
           cutoff '(x epsilon)))
         (precision
          (putnam-1962-a2-divide-term
           (putnam-1962-a2-quoted 1)
           'stage))
         (average
          (putnam-1962-a2-average-term
           function 'x precision 'stage))
         (at-zero
          (putnam-1962-a2-function-term
           function
           (putnam-1962-a2-quoted 0)
           precision))
         (at-x
          (putnam-1962-a2-function-term
           function 'x precision))
         (residual
          (putnam-1962-a2-subtract-term
           (putnam-1962-a2-multiply-term
            average average)
           (putnam-1962-a2-multiply-term
            at-zero at-x))))
    (list
     'lambda
     '(x epsilon stage)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (putnam-1962-a2-domain-term 'x endpoint t)
        (putnam-1962-a2-positive-rational-term 'epsilon)
        (list 'natp 'stage)
        (list '< (putnam-1962-a2-quoted 0) 'stage)
        (putnam-1962-a2-less-equal-term
         index 'stage)))
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp average)
        (list 'rationalp at-zero)
        (list 'rationalp at-x)
        (putnam-1962-a2-less-equal-term
         (putnam-1962-a2-absolute-term residual)
         'epsilon)))))))

(defun putnam-1962-a2-average-witness-p
    (function endpoint cutoff)
  (and
   (tamep-functionp cutoff)
   (fn-equal
    (putnam-1962-a2-cutoff-positive-matrix
     cutoff endpoint t)
    (putnam-1962-a2-true-function
     '(x epsilon)))
   (fn-equal
    (putnam-1962-a2-average-equation-matrix
     function endpoint cutoff)
    (putnam-1962-a2-true-function
     '(x epsilon stage)))))

(defun putnam-1962-a2-average-failure-function
    (function endpoint)
  (list
   'lambda
   '(cutoff)
   (list
    'if
    (list
     'putnam-1962-a2-average-witness-p
     (putnam-1962-a2-quoted function)
     (putnam-1962-a2-quoted endpoint)
     'cutoff)
    (putnam-1962-a2-quoted nil)
    (putnam-1962-a2-quoted t))))

(defun putnam-1962-a2-average-condition-p
    (function endpoint)
  (let ((failure
         (putnam-1962-a2-average-failure-function
          function endpoint))
        (always-true
         (putnam-1962-a2-true-function '(cutoff))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-1962-a2-family-equation-matrix
    (function endpoint parameter cutoff)
  (let* ((index
          (putnam-1962-a2-apply-term
           cutoff '(x epsilon)))
         (precision
          (putnam-1962-a2-divide-term
           (putnam-1962-a2-quoted 1)
           'stage))
         (at-zero
          (putnam-1962-a2-function-term
           function
           (putnam-1962-a2-quoted 0)
           precision))
         (at-x
          (putnam-1962-a2-function-term
           function 'x precision))
         (c-value
          (putnam-1962-a2-apply-term
           parameter (list precision)))
         (denominator
          (putnam-1962-a2-subtract-term
           (putnam-1962-a2-quoted 1)
           (putnam-1962-a2-multiply-term
            c-value 'x)))
         (residual
          (putnam-1962-a2-subtract-term
           (putnam-1962-a2-multiply-term
            at-x
            (putnam-1962-a2-multiply-term
             denominator denominator))
           at-zero)))
    (list
     'lambda
     '(x epsilon stage)
     (putnam-1962-a2-implies-term
      (putnam-1962-a2-and-terms
       (list
        (putnam-1962-a2-domain-term 'x endpoint nil)
        (putnam-1962-a2-positive-rational-term 'epsilon)
        (list 'natp 'stage)
        (list '< (putnam-1962-a2-quoted 0) 'stage)
        (putnam-1962-a2-less-equal-term
         index 'stage)))
      (putnam-1962-a2-and-terms
       (list
        (list 'rationalp at-zero)
        (list 'rationalp at-x)
        (list 'rationalp c-value)
        (putnam-1962-a2-less-equal-term
         (putnam-1962-a2-absolute-term residual)
         'epsilon)))))))

(defun putnam-1962-a2-family-witness-p
    (witness function endpoint)
  (and
   (true-listp witness)
   (equal (len witness) 2)
   (let ((parameter (nth 0 witness))
         (cutoff (nth 1 witness)))
     (and
      (putnam-1962-a2-real-name-p parameter)
      (tamep-functionp cutoff)
      (fn-equal
       (putnam-1962-a2-cutoff-positive-matrix
        cutoff endpoint nil)
       (putnam-1962-a2-true-function
        '(x epsilon)))
      (fn-equal
       (putnam-1962-a2-family-equation-matrix
        function endpoint parameter cutoff)
       (putnam-1962-a2-true-function
        '(x epsilon stage)))))))

(defun putnam-1962-a2-family-failure-function
    (function endpoint)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'putnam-1962-a2-family-witness-p
     'witness
     (putnam-1962-a2-quoted function)
     (putnam-1962-a2-quoted endpoint))
    (putnam-1962-a2-quoted nil)
    (putnam-1962-a2-quoted t))))

(defun putnam-1962-a2-family-exists-p
    (function endpoint)
  (let ((failure
         (putnam-1962-a2-family-failure-function
          function endpoint))
        (always-true
         (putnam-1962-a2-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

;; NIL denotes the infinite interval. A positive rational ENDPOINT denotes
;; [0,ENDPOINT). Universal closure over FUNCTION and ENDPOINT is the
;; nondegenerate core of both directions of the source classification.
(defun putnambench-putnam-1962-a2-statement
    (function endpoint)
  (implies
   (and
    (putnam-1962-a2-function-cauchy-p function)
    (putnam-1962-a2-continuous-p function)
    (putnam-1962-a2-nonnegative-p function)
    (putnam-1962-a2-positive-at-zero-p function))
   (and
    (iff
     (putnam-1962-a2-average-condition-p function nil)
     (putnam-1962-a2-family-exists-p function nil))
    (implies
     (and (rationalp endpoint)
          (< 0 endpoint))
     (iff
      (putnam-1962-a2-average-condition-p
       function endpoint)
      (putnam-1962-a2-family-exists-p
       function endpoint))))))

(value-triple :itpeval-statement-checked)
:q
