;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_a5:
;; a C2 vector field on R^n whose antisymmetric first-partial differences are
;; constant admits a scalar function whose gradient makes every component
;; linear. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, vectors are length-n lists of such
;; names, and arbitrary extensional functions are tame APPLY$ objects.
;; FN-EQUAL supplies unbounded universal quantification; inequality with a
;; constant-false function supplies internal existential quantification.
;;
;; The internally quantified first- and second-partial fields express the C2
;; hypothesis by coordinate difference quotients and joint continuity on all
;; of R^n. The conclusion internally quantifies both g and the field of its
;; totalized coordinate derivatives, matching Mathlib's totalized FDERIV.

(defun putnam-1986-a5-quoted (object)
  (list 'quote object))

(defun putnam-1986-a5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1986-a5-term-list (cdr terms)))
    nil))

(defun putnam-1986-a5-apply-term (function arguments)
  (list 'apply$
        (putnam-1986-a5-quoted function)
        (putnam-1986-a5-term-list arguments)))

(defun putnam-1986-a5-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-1986-a5-term-list arguments)))

(defun putnam-1986-a5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1986-a5-and-terms (cdr terms))
            (putnam-1986-a5-quoted nil))
    (putnam-1986-a5-quoted t)))

(defun putnam-1986-a5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1986-a5-quoted t)))

(defun putnam-1986-a5-not-term (term)
  (list 'if
        term
        (putnam-1986-a5-quoted nil)
        (putnam-1986-a5-quoted t)))

(defun putnam-1986-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1986-a5-negate-term (value)
  (list 'unary-- value))

(defun putnam-1986-a5-subtract-term (left right)
  (putnam-1986-a5-add-term
   left
   (putnam-1986-a5-negate-term right)))

(defun putnam-1986-a5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1986-a5-divide-term (numerator denominator)
  (putnam-1986-a5-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-1986-a5-absolute-term (value)
  (list 'if
        (list '< value (putnam-1986-a5-quoted 0))
        (putnam-1986-a5-negate-term value)
        value))

(defun putnam-1986-a5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-1986-a5-quoted nil)
        (putnam-1986-a5-quoted t)))

(defun putnam-1986-a5-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-1986-a5-positive-rational-term (value)
  (putnam-1986-a5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-1986-a5-quoted 0) value))))

(defun putnam-1986-a5-true-function (formals)
  (list 'lambda
        formals
        (putnam-1986-a5-quoted t)))

(defun putnam-1986-a5-real-value-term (name precision)
  (putnam-1986-a5-apply-term name (list precision)))

(defun putnam-1986-a5-object-real-value-term
    (name-term precision)
  (putnam-1986-a5-apply-object-term
   name-term
   (list precision)))

(defun putnam-1986-a5-real-cauchy-function (name)
  (let* ((left
          (putnam-1986-a5-real-value-term name 'epsilon))
         (right
          (putnam-1986-a5-real-value-term name 'eta))
         (distance
          (putnam-1986-a5-absolute-term
           (putnam-1986-a5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (putnam-1986-a5-positive-rational-term 'epsilon)
        (putnam-1986-a5-positive-rational-term 'eta)))
      (putnam-1986-a5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1986-a5-less-equal-term
         distance
         (putnam-1986-a5-add-term
          'epsilon 'eta))))))))

(defun putnam-1986-a5-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-1986-a5-real-cauchy-function name)
    (putnam-1986-a5-true-function
     '(epsilon eta)))))

;; Sampling both names at eta/4 makes the universal inequality equivalent to
;; the represented real distance being at most BOUND.
(defun putnam-1986-a5-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-1986-a5-multiply-term
           (putnam-1986-a5-quoted 1/4)
           'eta))
         (left
          (putnam-1986-a5-real-value-term
           left-name precision))
         (right
          (putnam-1986-a5-real-value-term
           right-name precision))
         (distance
          (putnam-1986-a5-absolute-term
           (putnam-1986-a5-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-positive-rational-term 'eta)
      (putnam-1986-a5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1986-a5-less-equal-term
         distance
         (putnam-1986-a5-add-term
          (putnam-1986-a5-quoted bound)
          'eta))))))))

(defun putnam-1986-a5-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-1986-a5-real-name-p left-name)
   (putnam-1986-a5-real-name-p right-name)
   (fn-equal
    (putnam-1986-a5-real-distance-function
     left-name right-name bound)
    (putnam-1986-a5-true-function '(eta)))))

(defun putnam-1986-a5-real-equal-p
    (left-name right-name)
  (putnam-1986-a5-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-1986-a5-unary-output-function
    (function)
  (let ((output
         (putnam-1986-a5-apply-term function (list 'x))))
    (list
     'lambda
     '(x)
     (putnam-1986-a5-implies-term
      (list 'putnam-1986-a5-real-name-p 'x)
      (list 'putnam-1986-a5-real-name-p output)))))

(defun putnam-1986-a5-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-1986-a5-apply-term
          function (list 'x-left)))
        (right-output
         (putnam-1986-a5-apply-term
          function (list 'x-right))))
    (list
     'lambda
     '(x-left x-right)
     (putnam-1986-a5-implies-term
      (list 'putnam-1986-a5-real-equal-p
            'x-left 'x-right)
      (list 'putnam-1986-a5-real-equal-p
            left-output right-output)))))

(defun putnam-1986-a5-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-1986-a5-unary-output-function function)
    (putnam-1986-a5-true-function '(x)))
   (fn-equal
    (putnam-1986-a5-unary-extensional-function function)
    (putnam-1986-a5-true-function
     '(x-left x-right)))))

(defun putnam-1986-a5-rational-shift-name (name shift)
  (let ((value
         (putnam-1986-a5-object-real-value-term
          (putnam-1986-a5-quoted name)
          (putnam-1986-a5-multiply-term
           (putnam-1986-a5-quoted 1/2)
           'precision))))
    (list
     'lambda
     '(precision)
     (putnam-1986-a5-add-term
      value
      (putnam-1986-a5-quoted shift)))))

(defun putnam-1986-a5-constant-name (value)
  (list
   'lambda
   '(precision)
   (putnam-1986-a5-quoted value)))

(defun putnam-1986-a5-real-negate-name (name)
  (let ((value
         (putnam-1986-a5-object-real-value-term
          (putnam-1986-a5-quoted name)
          'precision)))
    (list
     'lambda
     '(precision)
     (putnam-1986-a5-negate-term value))))

(defun putnam-1986-a5-real-scale-name (name scalar)
  (let* ((sample-precision
          (putnam-1986-a5-divide-term
           'precision
           (putnam-1986-a5-add-term
            (putnam-1986-a5-quoted 1)
            (putnam-1986-a5-absolute-term
             (putnam-1986-a5-quoted scalar)))))
         (value
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-1986-a5-multiply-term
      (putnam-1986-a5-quoted scalar)
      value))))

(defun putnam-1986-a5-real-product-name (left-name right-name)
  (let* ((left-coarse
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted left-name)
           (putnam-1986-a5-quoted 1)))
         (right-coarse
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted right-name)
           (putnam-1986-a5-quoted 1)))
         (scale
          (putnam-1986-a5-multiply-term
           (putnam-1986-a5-quoted 64)
           (putnam-1986-a5-add-term
            (putnam-1986-a5-quoted 1)
            (putnam-1986-a5-add-term
             (putnam-1986-a5-absolute-term left-coarse)
             (putnam-1986-a5-absolute-term right-coarse)))))
         (sample-precision
          (putnam-1986-a5-minimum-term
           (putnam-1986-a5-quoted 1)
           (putnam-1986-a5-divide-term
            'precision scale)))
         (left-value
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted left-name)
           sample-precision))
         (right-value
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted right-name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-1986-a5-multiply-term
      left-value right-value))))

(defun putnam-1986-a5-real-absolute-name (name)
  (let ((value
         (putnam-1986-a5-object-real-value-term
          (putnam-1986-a5-quoted name)
          'precision)))
    (list
     'lambda
     '(precision)
     (putnam-1986-a5-absolute-term value))))

(defun putnam-1986-a5-real-less-equal-function
    (left-name right-name)
  (let* ((sample-precision
          (putnam-1986-a5-multiply-term
           (putnam-1986-a5-quoted 1/4)
           'eta))
         (left
          (putnam-1986-a5-real-value-term
           left-name sample-precision))
         (right
          (putnam-1986-a5-real-value-term
           right-name sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-positive-rational-term 'eta)
      (putnam-1986-a5-less-equal-term
       left
       (putnam-1986-a5-add-term right 'eta))))))

(defun putnam-1986-a5-real-less-equal-p
    (left-name right-name)
  (and
   (putnam-1986-a5-real-name-p left-name)
   (putnam-1986-a5-real-name-p right-name)
   (fn-equal
    (putnam-1986-a5-real-less-equal-function
     left-name right-name)
    (putnam-1986-a5-true-function '(eta)))))

(defun putnam-1986-a5-positive-witness-p
    (epsilon name)
  (and
   (rationalp epsilon)
   (< 0 epsilon)
   (putnam-1986-a5-real-less-equal-p
    (putnam-1986-a5-constant-name epsilon)
    name)))

(defun putnam-1986-a5-positive-witness-failure-function
    (name)
  (list
   'lambda
   '(epsilon)
   (list
    'if
    (list 'putnam-1986-a5-positive-witness-p
          'epsilon
          (putnam-1986-a5-quoted name))
    (putnam-1986-a5-quoted nil)
    (putnam-1986-a5-quoted t))))

(defun putnam-1986-a5-real-positive-p (name)
  (let ((failure
         (putnam-1986-a5-positive-witness-failure-function
          name))
        (always-true
         (putnam-1986-a5-true-function '(epsilon))))
    (and
     (putnam-1986-a5-real-name-p name)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-1986-a5-real-add-name
    (left-name right-name)
  (let* ((sample-precision
          (putnam-1986-a5-multiply-term
           (putnam-1986-a5-quoted 1/4)
           'precision))
         (left
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted left-name)
           sample-precision))
         (right
          (putnam-1986-a5-object-real-value-term
           (putnam-1986-a5-quoted right-name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-1986-a5-add-term left right))))

(defun putnam-1986-a5-false-function (formals)
  (list 'lambda formals (putnam-1986-a5-quoted nil)))

(defun putnam-1986-a5-universal-p (function formals)
  (let ((always-true
         (putnam-1986-a5-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun putnam-1986-a5-exists-p (function formals)
  (let ((always-false
         (putnam-1986-a5-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun putnam-1986-a5-real-subtract-name
    (left-name right-name)
  (putnam-1986-a5-real-add-name
   left-name
   (putnam-1986-a5-real-negate-name right-name)))

;; Exact finite-dimensional real vectors.

(defun putnam-1986-a5-real-list-p (values)
  (if (consp values)
      (and
       (putnam-1986-a5-real-name-p (car values))
       (putnam-1986-a5-real-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1986-a5-vector-p (vector n)
  (and
   (natp n)
   (true-listp vector)
   (equal (len vector) n)
   (putnam-1986-a5-real-list-p vector)))

(defun putnam-1986-a5-vector-equal-p (left right)
  (if (consp left)
      (and
       (consp right)
       (putnam-1986-a5-real-equal-p
        (car left) (car right))
       (putnam-1986-a5-vector-equal-p
        (cdr left) (cdr right)))
    (equal right nil)))

(defun putnam-1986-a5-vector-close-p
    (left right bound)
  (if (consp left)
      (and
       (consp right)
       (putnam-1986-a5-real-distance-at-most-p
        (car left) (car right) bound)
       (putnam-1986-a5-vector-close-p
        (cdr left) (cdr right) bound))
    (equal right nil)))

(defun putnam-1986-a5-vector-add (left right)
  (if (and (consp left) (consp right))
      (cons
       (putnam-1986-a5-real-add-name
        (car left) (car right))
       (putnam-1986-a5-vector-add
        (cdr left) (cdr right)))
    nil))

(defun putnam-1986-a5-vector-smul (scalar vector)
  (if (consp vector)
      (cons
       (putnam-1986-a5-real-product-name
        scalar (car vector))
       (putnam-1986-a5-vector-smul
        scalar (cdr vector)))
    nil))

(defun putnam-1986-a5-vector-rational-shift
    (vector index shift)
  (if (consp vector)
      (if (zp index)
          (cons
           (putnam-1986-a5-rational-shift-name
            (car vector) shift)
           (cdr vector))
        (cons
         (car vector)
         (putnam-1986-a5-vector-rational-shift
          (cdr vector) (- index 1) shift)))
    nil))

(defun putnam-1986-a5-index-p (index n)
  (and (natp index) (< index n)))

;; Extensional component families, scalar functions, and derivative fields.

(defun putnam-1986-a5-component-output-function
    (n function)
  (let ((output
         (putnam-1986-a5-apply-term function '(i x))))
    (list
     'lambda '(i x)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x (putnam-1986-a5-quoted n))))
      (list 'putnam-1986-a5-real-name-p output)))))

(defun putnam-1986-a5-component-extensional-function
    (n function)
  (let ((left
         (putnam-1986-a5-apply-term
          function '(i x-left)))
        (right
         (putnam-1986-a5-apply-term
          function '(i x-right))))
    (list
     'lambda '(i x-left x-right)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-left (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-right (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1986-a5-real-equal-p
            left right)))))

(defun putnam-1986-a5-component-function-p
    (n function)
  (and
   (tamep-functionp function)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-component-output-function
     n function)
    '(i x))
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-component-extensional-function
     n function)
    '(i x-left x-right))))

(defun putnam-1986-a5-scalar-output-function
    (n function)
  (let ((output
         (putnam-1986-a5-apply-term function '(x))))
    (list
     'lambda '(x)
     (putnam-1986-a5-implies-term
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-real-name-p output)))))

(defun putnam-1986-a5-scalar-extensional-function
    (n function)
  (let ((left
         (putnam-1986-a5-apply-term function '(x-left)))
        (right
         (putnam-1986-a5-apply-term function '(x-right))))
    (list
     'lambda '(x-left x-right)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-vector-p
              'x-left (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-right (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1986-a5-real-equal-p
            left right)))))

(defun putnam-1986-a5-scalar-function-p
    (n function)
  (and
   (tamep-functionp function)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-scalar-output-function
     n function)
    '(x))
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-scalar-extensional-function
     n function)
    '(x-left x-right))))

(defun putnam-1986-a5-first-field-output-function
    (n field)
  (let ((output
         (putnam-1986-a5-apply-term field '(i j x))))
    (list
     'lambda '(i j x)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'j (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x (putnam-1986-a5-quoted n))))
      (list 'putnam-1986-a5-real-name-p output)))))

(defun putnam-1986-a5-first-field-extensional-function
    (n field)
  (let ((left
         (putnam-1986-a5-apply-term
          field '(i j x-left)))
        (right
         (putnam-1986-a5-apply-term
          field '(i j x-right))))
    (list
     'lambda '(i j x-left x-right)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'j (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-left (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-right (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1986-a5-real-equal-p
            left right)))))

(defun putnam-1986-a5-first-field-p (n field)
  (and
   (tamep-functionp field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-first-field-output-function
     n field)
    '(i j x))
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-first-field-extensional-function
     n field)
    '(i j x-left x-right))))

(defun putnam-1986-a5-second-field-output-function
    (n field)
  (let ((output
         (putnam-1986-a5-apply-term field '(i j k x))))
    (list
     'lambda '(i j k x)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'j (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'k (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x (putnam-1986-a5-quoted n))))
      (list 'putnam-1986-a5-real-name-p output)))))

(defun putnam-1986-a5-second-field-extensional-function
    (n field)
  (let ((left
         (putnam-1986-a5-apply-term
          field '(i j k x-left)))
        (right
         (putnam-1986-a5-apply-term
          field '(i j k x-right))))
    (list
     'lambda '(i j k x-left x-right)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'j (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'k (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-left (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x-right (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1986-a5-real-equal-p
            left right)))))

(defun putnam-1986-a5-second-field-p (n field)
  (and
   (tamep-functionp field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-second-field-output-function
     n field)
    '(i j k x))
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-second-field-extensional-function
     n field)
    '(i j k x-left x-right))))

(defun putnam-1986-a5-constant-field-output-function
    (n field)
  (let ((output
         (putnam-1986-a5-apply-term field '(i j))))
    (list
     'lambda '(i j)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'j (putnam-1986-a5-quoted n))))
      (list 'putnam-1986-a5-real-name-p output)))))

(defun putnam-1986-a5-constant-field-p (n field)
  (and
   (tamep-functionp field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-constant-field-output-function
     n field)
    '(i j))))

;; Joint continuity on R^n, expressed with the sup metric.

(defun putnam-1986-a5-component-continuity-delta-row
    (n function i x epsilon delta)
  (let ((at-x
         (putnam-1986-a5-apply-term
          function
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted x))))
        (at-y
         (putnam-1986-a5-apply-term
          function
          (list (putnam-1986-a5-quoted i) 'y))))
    (list
     'lambda '(y)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-vector-p
              'y (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-close-p
              (putnam-1986-a5-quoted x)
              'y
              (putnam-1986-a5-quoted delta))))
      (list 'putnam-1986-a5-real-distance-at-most-p
            at-x at-y
            (putnam-1986-a5-quoted epsilon))))))

(defun putnam-1986-a5-component-continuity-delta-p
    (n function i x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-component-continuity-delta-row
     n function i x epsilon delta)
    '(y))))

(defun putnam-1986-a5-component-continuity-radius-function
    (n function i x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1986-a5-component-continuity-delta-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted function)
         (putnam-1986-a5-quoted i)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted epsilon)
         'delta)))

(defun putnam-1986-a5-component-continuity-row
    (n function)
  (list
   'lambda '(i x epsilon)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'i (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (putnam-1986-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1986-a5-exists-p
          (list
           'putnam-1986-a5-component-continuity-radius-function
           (putnam-1986-a5-quoted n)
           (putnam-1986-a5-quoted function)
           'i 'x 'epsilon)
          (putnam-1986-a5-quoted '(delta))))))

(defun putnam-1986-a5-component-continuous-p
    (n function)
  (and
   (putnam-1986-a5-component-function-p n function)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-component-continuity-row
     n function)
    '(i x epsilon))))

(defun putnam-1986-a5-first-continuity-delta-row
    (n field i j x epsilon delta)
  (let ((at-x
         (putnam-1986-a5-apply-term
          field
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted j)
                (putnam-1986-a5-quoted x))))
        (at-y
         (putnam-1986-a5-apply-term
          field
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted j)
                'y))))
    (list
     'lambda '(y)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-vector-p
              'y (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-close-p
              (putnam-1986-a5-quoted x)
              'y
              (putnam-1986-a5-quoted delta))))
      (list 'putnam-1986-a5-real-distance-at-most-p
            at-x at-y
            (putnam-1986-a5-quoted epsilon))))))

(defun putnam-1986-a5-first-continuity-delta-p
    (n field i j x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-first-continuity-delta-row
     n field i j x epsilon delta)
    '(y))))

(defun putnam-1986-a5-first-continuity-radius-function
    (n field i j x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1986-a5-first-continuity-delta-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted field)
         (putnam-1986-a5-quoted i)
         (putnam-1986-a5-quoted j)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted epsilon)
         'delta)))

(defun putnam-1986-a5-first-continuity-row
    (n field)
  (list
   'lambda '(i j x epsilon)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'i (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-index-p
            'j (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (putnam-1986-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1986-a5-exists-p
          (list
           'putnam-1986-a5-first-continuity-radius-function
           (putnam-1986-a5-quoted n)
           (putnam-1986-a5-quoted field)
           'i 'j 'x 'epsilon)
          (putnam-1986-a5-quoted '(delta))))))

(defun putnam-1986-a5-first-continuous-p (n field)
  (and
   (putnam-1986-a5-first-field-p n field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-first-continuity-row n field)
    '(i j x epsilon))))

(defun putnam-1986-a5-second-continuity-delta-row
    (n field i j k x epsilon delta)
  (let ((at-x
         (putnam-1986-a5-apply-term
          field
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted j)
                (putnam-1986-a5-quoted k)
                (putnam-1986-a5-quoted x))))
        (at-y
         (putnam-1986-a5-apply-term
          field
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted j)
                (putnam-1986-a5-quoted k)
                'y))))
    (list
     'lambda '(y)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-vector-p
              'y (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-close-p
              (putnam-1986-a5-quoted x)
              'y
              (putnam-1986-a5-quoted delta))))
      (list 'putnam-1986-a5-real-distance-at-most-p
            at-x at-y
            (putnam-1986-a5-quoted epsilon))))))

(defun putnam-1986-a5-second-continuity-delta-p
    (n field i j k x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-second-continuity-delta-row
     n field i j k x epsilon delta)
    '(y))))

(defun putnam-1986-a5-second-continuity-radius-function
    (n field i j k x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1986-a5-second-continuity-delta-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted field)
         (putnam-1986-a5-quoted i)
         (putnam-1986-a5-quoted j)
         (putnam-1986-a5-quoted k)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted epsilon)
         'delta)))

(defun putnam-1986-a5-second-continuity-row
    (n field)
  (list
   'lambda '(i j k x epsilon)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'i (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-index-p
            'j (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-index-p
            'k (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (putnam-1986-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1986-a5-exists-p
          (list
           'putnam-1986-a5-second-continuity-radius-function
           (putnam-1986-a5-quoted n)
           (putnam-1986-a5-quoted field)
           'i 'j 'k 'x 'epsilon)
          (putnam-1986-a5-quoted '(delta))))))

(defun putnam-1986-a5-second-continuous-p (n field)
  (and
   (putnam-1986-a5-second-field-p n field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-second-continuity-row n field)
    '(i j k x epsilon))))

;; Coordinate derivatives from rational increments, which are dense in R.

(defun putnam-1986-a5-component-difference-quotient-name
    (function i x j h)
  (let* ((shifted-x
          (putnam-1986-a5-vector-rational-shift
           x j h))
         (shifted-output
          (apply$ function (list i shifted-x)))
         (base-output
          (apply$ function (list i x)))
         (sample-precision
          (* (/ (abs h) 4) 1)))
    (list
     'lambda '(eta)
     (putnam-1986-a5-divide-term
      (putnam-1986-a5-subtract-term
       (putnam-1986-a5-object-real-value-term
        (putnam-1986-a5-quoted shifted-output)
        (putnam-1986-a5-multiply-term
         (putnam-1986-a5-quoted sample-precision)
         'eta))
       (putnam-1986-a5-object-real-value-term
        (putnam-1986-a5-quoted base-output)
        (putnam-1986-a5-multiply-term
         (putnam-1986-a5-quoted sample-precision)
         'eta)))
      (putnam-1986-a5-quoted h)))))

(defun putnam-1986-a5-first-delta-row
    (function field i j x epsilon delta)
  (let ((quotient
         (list 'putnam-1986-a5-component-difference-quotient-name
               (putnam-1986-a5-quoted function)
               (putnam-1986-a5-quoted i)
               (putnam-1986-a5-quoted x)
               (putnam-1986-a5-quoted j)
               'h))
        (derivative
         (putnam-1986-a5-apply-term
          field
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted j)
                (putnam-1986-a5-quoted x)))))
    (list
     'lambda '(h)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-1986-a5-not-term
         (list 'equal 'h (putnam-1986-a5-quoted 0)))
        (putnam-1986-a5-less-equal-term
         (putnam-1986-a5-absolute-term 'h)
         (putnam-1986-a5-quoted delta))))
      (list 'putnam-1986-a5-real-distance-at-most-p
            quotient derivative
            (putnam-1986-a5-quoted epsilon))))))

(defun putnam-1986-a5-first-delta-p
    (function field i j x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-first-delta-row
     function field i j x epsilon delta)
    '(h))))

(defun putnam-1986-a5-first-radius-function
    (function field i j x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1986-a5-first-delta-p
         (putnam-1986-a5-quoted function)
         (putnam-1986-a5-quoted field)
         (putnam-1986-a5-quoted i)
         (putnam-1986-a5-quoted j)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted epsilon)
         'delta)))

(defun putnam-1986-a5-first-partial-row
    (n function field)
  (list
   'lambda '(i j x epsilon)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'i (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-index-p
            'j (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (putnam-1986-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1986-a5-exists-p
          (list 'putnam-1986-a5-first-radius-function
                (putnam-1986-a5-quoted function)
                (putnam-1986-a5-quoted field)
                'i 'j 'x 'epsilon)
          (putnam-1986-a5-quoted '(delta))))))

(defun putnam-1986-a5-first-partial-field-p
    (n function field)
  (and
   (putnam-1986-a5-component-function-p n function)
   (putnam-1986-a5-first-field-p n field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-first-partial-row
     n function field)
    '(i j x epsilon))))

(defun putnam-1986-a5-first-field-difference-quotient-name
    (field i j x k h)
  (let* ((shifted-x
          (putnam-1986-a5-vector-rational-shift
           x k h))
         (shifted-output
          (apply$ field (list i j shifted-x)))
         (base-output
          (apply$ field (list i j x)))
         (sample-precision
          (* (/ (abs h) 4) 1)))
    (list
     'lambda '(eta)
     (putnam-1986-a5-divide-term
      (putnam-1986-a5-subtract-term
       (putnam-1986-a5-object-real-value-term
        (putnam-1986-a5-quoted shifted-output)
        (putnam-1986-a5-multiply-term
         (putnam-1986-a5-quoted sample-precision)
         'eta))
       (putnam-1986-a5-object-real-value-term
        (putnam-1986-a5-quoted base-output)
        (putnam-1986-a5-multiply-term
         (putnam-1986-a5-quoted sample-precision)
         'eta)))
      (putnam-1986-a5-quoted h)))))

(defun putnam-1986-a5-second-delta-row
    (first second i j k x epsilon delta)
  (let ((quotient
         (list 'putnam-1986-a5-first-field-difference-quotient-name
               (putnam-1986-a5-quoted first)
               (putnam-1986-a5-quoted i)
               (putnam-1986-a5-quoted j)
               (putnam-1986-a5-quoted x)
               (putnam-1986-a5-quoted k)
               'h))
        (derivative
         (putnam-1986-a5-apply-term
          second
          (list (putnam-1986-a5-quoted i)
                (putnam-1986-a5-quoted j)
                (putnam-1986-a5-quoted k)
                (putnam-1986-a5-quoted x)))))
    (list
     'lambda '(h)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-1986-a5-not-term
         (list 'equal 'h (putnam-1986-a5-quoted 0)))
        (putnam-1986-a5-less-equal-term
         (putnam-1986-a5-absolute-term 'h)
         (putnam-1986-a5-quoted delta))))
      (list 'putnam-1986-a5-real-distance-at-most-p
            quotient derivative
            (putnam-1986-a5-quoted epsilon))))))

(defun putnam-1986-a5-second-delta-p
    (first second i j k x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-second-delta-row
     first second i j k x epsilon delta)
    '(h))))

(defun putnam-1986-a5-second-radius-function
    (first second i j k x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1986-a5-second-delta-p
         (putnam-1986-a5-quoted first)
         (putnam-1986-a5-quoted second)
         (putnam-1986-a5-quoted i)
         (putnam-1986-a5-quoted j)
         (putnam-1986-a5-quoted k)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted epsilon)
         'delta)))

(defun putnam-1986-a5-second-partial-row
    (n first second)
  (list
   'lambda '(i j k x epsilon)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'i (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-index-p
            'j (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-index-p
            'k (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (putnam-1986-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1986-a5-exists-p
          (list 'putnam-1986-a5-second-radius-function
                (putnam-1986-a5-quoted first)
                (putnam-1986-a5-quoted second)
                'i 'j 'k 'x 'epsilon)
          (putnam-1986-a5-quoted '(delta))))))

(defun putnam-1986-a5-second-partial-field-p
    (n first second)
  (and
   (putnam-1986-a5-first-field-p n first)
   (putnam-1986-a5-second-field-p n second)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-second-partial-row
     n first second)
    '(i j k x epsilon))))

(defun putnam-1986-a5-skew-row (n first constants)
  (let ((ij
         (putnam-1986-a5-apply-term
          first '(i j x)))
        (ji
         (putnam-1986-a5-apply-term
          first '(j i x)))
        (constant
         (putnam-1986-a5-apply-term
          constants '(i j))))
    (list
     'lambda '(i j x)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-index-p
              'i (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-index-p
              'j (putnam-1986-a5-quoted n))
        (list 'putnam-1986-a5-vector-p
              'x (putnam-1986-a5-quoted n))))
      (list 'putnam-1986-a5-real-equal-p
            (list 'putnam-1986-a5-real-subtract-name
                  ij ji)
            constant)))))

(defun putnam-1986-a5-constant-skew-p
    (n first constants)
  (putnam-1986-a5-universal-p
   (putnam-1986-a5-skew-row n first constants)
   '(i j x)))

(defun putnam-1986-a5-c2-witness-p
    (n function constants first second)
  (and
   (putnam-1986-a5-component-continuous-p
    n function)
   (putnam-1986-a5-first-continuous-p n first)
   (putnam-1986-a5-second-continuous-p n second)
   (putnam-1986-a5-first-partial-field-p
    n function first)
   (putnam-1986-a5-second-partial-field-p
    n first second)
   (putnam-1986-a5-constant-skew-p
    n first constants)))

(defun putnam-1986-a5-c2-witness-function
    (n function constants)
  (list
   'lambda '(first second)
   (list 'putnam-1986-a5-c2-witness-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted function)
         (putnam-1986-a5-quoted constants)
         'first 'second)))

(defun putnam-1986-a5-hypothesis-p
    (n function constants)
  (and
   (posp n)
   (putnam-1986-a5-component-function-p
    n function)
   (putnam-1986-a5-constant-field-p
    n constants)
   (putnam-1986-a5-exists-p
    (putnam-1986-a5-c2-witness-function
     n function constants)
    '(first second))))

;; Mathlib's FDERIV is zero when a full Frechet derivative does not exist.
;; In finite dimensions the sup norm is equivalent to the Euclidean norm.

(defun putnam-1986-a5-zero-vector (n)
  (if (zp n)
      nil
    (cons
     (putnam-1986-a5-constant-name 0)
     (putnam-1986-a5-zero-vector (- n 1)))))

(defun putnam-1986-a5-real-dot-name (left right)
  (if (and (consp left) (consp right))
      (putnam-1986-a5-real-add-name
       (putnam-1986-a5-real-product-name
        (car left) (car right))
       (putnam-1986-a5-real-dot-name
        (cdr left) (cdr right)))
    (putnam-1986-a5-constant-name 0)))

(defun putnam-1986-a5-frechet-delta-row
    (n function x gradient epsilon delta)
  (let* ((shifted-x
          (list 'putnam-1986-a5-vector-add
                (putnam-1986-a5-quoted x)
                'increment))
         (change
          (list 'putnam-1986-a5-real-subtract-name
                (putnam-1986-a5-apply-term
                 function (list shifted-x))
                (putnam-1986-a5-apply-term
                 function
                 (list (putnam-1986-a5-quoted x)))))
         (linear-change
          (list 'putnam-1986-a5-real-dot-name
                (putnam-1986-a5-quoted gradient)
                'increment)))
    (list
     'lambda '(increment radius)
     (putnam-1986-a5-implies-term
      (putnam-1986-a5-and-terms
       (list
        (list 'putnam-1986-a5-vector-p
              'increment
              (putnam-1986-a5-quoted n))
        (putnam-1986-a5-positive-rational-term
         'radius)
        (putnam-1986-a5-less-equal-term
         'radius
         (putnam-1986-a5-quoted delta))
        (list 'putnam-1986-a5-vector-close-p
              'increment
              (list 'putnam-1986-a5-zero-vector
                    (putnam-1986-a5-quoted n))
              'radius)))
      (list 'putnam-1986-a5-real-distance-at-most-p
            change
            linear-change
            (list 'binary-*
                  (putnam-1986-a5-quoted epsilon)
                  'radius))))))

(defun putnam-1986-a5-frechet-delta-p
    (n function x gradient epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-frechet-delta-row
     n function x gradient epsilon delta)
    '(increment radius))))

(defun putnam-1986-a5-frechet-radius-function
    (n function x gradient epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1986-a5-frechet-delta-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted function)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted gradient)
         (putnam-1986-a5-quoted epsilon)
         'delta)))

(defun putnam-1986-a5-has-frechet-row
    (n function x gradient)
  (list
   'lambda '(epsilon)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-positive-rational-term
     'epsilon)
    (list 'putnam-1986-a5-exists-p
          (list 'putnam-1986-a5-frechet-radius-function
                (putnam-1986-a5-quoted n)
                (putnam-1986-a5-quoted function)
                (putnam-1986-a5-quoted x)
                (putnam-1986-a5-quoted gradient)
                'epsilon)
          (putnam-1986-a5-quoted '(delta))))))

(defun putnam-1986-a5-has-frechet-p
    (n function x gradient)
  (and
   (putnam-1986-a5-vector-p gradient n)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-has-frechet-row
     n function x gradient)
    '(epsilon))))

(defun putnam-1986-a5-frechet-witness-function
    (n function x)
  (list
   'lambda '(gradient)
   (list 'putnam-1986-a5-has-frechet-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted function)
         (putnam-1986-a5-quoted x)
         'gradient)))

(defun putnam-1986-a5-frechet-exists-p
    (n function x)
  (putnam-1986-a5-exists-p
   (putnam-1986-a5-frechet-witness-function
    n function x)
   '(gradient)))

(defun putnam-1986-a5-total-value-witness-p
    (n function x j value gradient)
  (and
   (putnam-1986-a5-has-frechet-p
    n function x gradient)
   (putnam-1986-a5-real-equal-p
    value (nth j gradient))))

(defun putnam-1986-a5-total-value-witness-function
    (n function x j value)
  (list
   'lambda '(gradient)
   (list 'putnam-1986-a5-total-value-witness-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted function)
         (putnam-1986-a5-quoted x)
         (putnam-1986-a5-quoted j)
         (putnam-1986-a5-quoted value)
         'gradient)))

(defun putnam-1986-a5-total-partial-value-p
    (n function x j value)
  (if (putnam-1986-a5-frechet-exists-p
       n function x)
      (putnam-1986-a5-exists-p
       (putnam-1986-a5-total-value-witness-function
        n function x j value)
       '(gradient))
    (putnam-1986-a5-real-equal-p
     value
     (putnam-1986-a5-constant-name 0))))

(defun putnam-1986-a5-total-field-row
    (n function field)
  (list
   'lambda '(j x)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'j (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))))
    (list 'putnam-1986-a5-total-partial-value-p
          (putnam-1986-a5-quoted n)
          (putnam-1986-a5-quoted function)
          'x 'j
          (putnam-1986-a5-apply-term
           field '(j x))))))

(defun putnam-1986-a5-total-field-p
    (n function field)
  (and
   (putnam-1986-a5-component-function-p n field)
   (putnam-1986-a5-universal-p
    (putnam-1986-a5-total-field-row
     n function field)
    '(j x))))

(defun putnam-1986-a5-adjusted-value
    (function total-field i x)
  (putnam-1986-a5-real-add-name
   (apply$ function (list i x))
   (apply$ total-field (list i x))))

(defun putnam-1986-a5-linearity-row
    (n function total-field)
  (list
   'lambda '(i x y scalar)
   (putnam-1986-a5-implies-term
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-index-p
            'i (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'x (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-vector-p
            'y (putnam-1986-a5-quoted n))
      (list 'putnam-1986-a5-real-name-p 'scalar)))
    (putnam-1986-a5-and-terms
     (list
      (list 'putnam-1986-a5-real-equal-p
            (list 'putnam-1986-a5-adjusted-value
                  (putnam-1986-a5-quoted function)
                  (putnam-1986-a5-quoted total-field)
                  'i
                  (list 'putnam-1986-a5-vector-add
                        'x 'y))
            (list 'putnam-1986-a5-real-add-name
                  (list 'putnam-1986-a5-adjusted-value
                        (putnam-1986-a5-quoted function)
                        (putnam-1986-a5-quoted total-field)
                        'i 'x)
                  (list 'putnam-1986-a5-adjusted-value
                        (putnam-1986-a5-quoted function)
                        (putnam-1986-a5-quoted total-field)
                        'i 'y)))
      (list 'putnam-1986-a5-real-equal-p
            (list 'putnam-1986-a5-adjusted-value
                  (putnam-1986-a5-quoted function)
                  (putnam-1986-a5-quoted total-field)
                  'i
                  (list 'putnam-1986-a5-vector-smul
                        'scalar 'x))
            (list 'putnam-1986-a5-real-product-name
                  'scalar
                  (list 'putnam-1986-a5-adjusted-value
                        (putnam-1986-a5-quoted function)
                        (putnam-1986-a5-quoted total-field)
                        'i 'x))))))))

(defun putnam-1986-a5-adjusted-linear-p
    (n function total-field)
  (putnam-1986-a5-universal-p
   (putnam-1986-a5-linearity-row
    n function total-field)
   '(i x y scalar)))

(defun putnam-1986-a5-solution-witness-p
    (n function scalar-function total-field)
  (and
   (putnam-1986-a5-scalar-function-p
    n scalar-function)
   (putnam-1986-a5-total-field-p
    n scalar-function total-field)
   (putnam-1986-a5-adjusted-linear-p
    n function total-field)))

(defun putnam-1986-a5-solution-witness-function
    (n function)
  (list
   'lambda '(scalar-function total-field)
   (list 'putnam-1986-a5-solution-witness-p
         (putnam-1986-a5-quoted n)
         (putnam-1986-a5-quoted function)
         'scalar-function
         'total-field)))

(defun putnam-1986-a5-conclusion-p (n function)
  (putnam-1986-a5-exists-p
   (putnam-1986-a5-solution-witness-function
    n function)
   '(scalar-function total-field)))

(defun putnambench-putnam-1986-a5-statement
    (n function constants)
  (implies
   (putnam-1986-a5-hypothesis-p
    n function constants)
   (putnam-1986-a5-conclusion-p
    n function)))

(value-triple :itpeval-statement-checked)
:q
