;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_a5:
;; no continuously differentiable real vector field on punctured real
;; three-space is curl-free there and restricts on z = 0 to
;; (-y/(x^2+4y^2), x/(x^2+4y^2), 0). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Reals are rational regular Cauchy names, vectors are length-three lists of
;; such names, and arbitrary extensional functions are tame APPLY$ objects.
;; FN-EQUAL supplies unbounded universal quantification; inequality with a
;; constant-false function supplies internal existential quantification.
;;
;; The vector field and its first-partial field are quantified together.
;; Coordinate difference quotients and joint continuity on the punctured
;; domain express the source C1 condition. The boundary equations multiply by
;; x^2+4y^2 away from the origin and explicitly use zero at the origin, exactly
;; matching the source provers' total real division.

(defun putnam-1987-a5-quoted (object)
  (list 'quote object))

(defun putnam-1987-a5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1987-a5-term-list (cdr terms)))
    nil))

(defun putnam-1987-a5-apply-term (function arguments)
  (list 'apply$
        (putnam-1987-a5-quoted function)
        (putnam-1987-a5-term-list arguments)))

(defun putnam-1987-a5-apply-object-term
    (function-term arguments)
  (list 'apply$
        function-term
        (putnam-1987-a5-term-list arguments)))

(defun putnam-1987-a5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-1987-a5-and-terms (cdr terms))
            (putnam-1987-a5-quoted nil))
    (putnam-1987-a5-quoted t)))

(defun putnam-1987-a5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1987-a5-quoted t)))

(defun putnam-1987-a5-not-term (term)
  (list 'if
        term
        (putnam-1987-a5-quoted nil)
        (putnam-1987-a5-quoted t)))

(defun putnam-1987-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1987-a5-negate-term (value)
  (list 'unary-- value))

(defun putnam-1987-a5-subtract-term (left right)
  (putnam-1987-a5-add-term
   left
   (putnam-1987-a5-negate-term right)))

(defun putnam-1987-a5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1987-a5-divide-term (numerator denominator)
  (putnam-1987-a5-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-1987-a5-absolute-term (value)
  (list 'if
        (list '< value (putnam-1987-a5-quoted 0))
        (putnam-1987-a5-negate-term value)
        value))

(defun putnam-1987-a5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-1987-a5-quoted nil)
        (putnam-1987-a5-quoted t)))

(defun putnam-1987-a5-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-1987-a5-positive-rational-term (value)
  (putnam-1987-a5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-1987-a5-quoted 0) value))))

(defun putnam-1987-a5-true-function (formals)
  (list 'lambda
        formals
        (putnam-1987-a5-quoted t)))

(defun putnam-1987-a5-real-value-term (name precision)
  (putnam-1987-a5-apply-term name (list precision)))

(defun putnam-1987-a5-object-real-value-term
    (name-term precision)
  (putnam-1987-a5-apply-object-term
   name-term
   (list precision)))

(defun putnam-1987-a5-real-cauchy-function (name)
  (let* ((left
          (putnam-1987-a5-real-value-term name 'epsilon))
         (right
          (putnam-1987-a5-real-value-term name 'eta))
         (distance
          (putnam-1987-a5-absolute-term
           (putnam-1987-a5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (putnam-1987-a5-positive-rational-term 'epsilon)
        (putnam-1987-a5-positive-rational-term 'eta)))
      (putnam-1987-a5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1987-a5-less-equal-term
         distance
         (putnam-1987-a5-add-term
          'epsilon 'eta))))))))

(defun putnam-1987-a5-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-1987-a5-real-cauchy-function name)
    (putnam-1987-a5-true-function
     '(epsilon eta)))))

;; Sampling both names at eta/4 makes the universal inequality equivalent to
;; the represented real distance being at most BOUND.
(defun putnam-1987-a5-real-distance-function
    (left-name right-name bound)
  (let* ((precision
          (putnam-1987-a5-multiply-term
           (putnam-1987-a5-quoted 1/4)
           'eta))
         (left
          (putnam-1987-a5-real-value-term
           left-name precision))
         (right
          (putnam-1987-a5-real-value-term
           right-name precision))
         (distance
          (putnam-1987-a5-absolute-term
           (putnam-1987-a5-subtract-term left right))))
    (list
     'lambda
     '(eta)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-positive-rational-term 'eta)
      (putnam-1987-a5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-1987-a5-less-equal-term
         distance
         (putnam-1987-a5-add-term
          (putnam-1987-a5-quoted bound)
          'eta))))))))

(defun putnam-1987-a5-real-distance-at-most-p
    (left-name right-name bound)
  (and
   (rationalp bound)
   (putnam-1987-a5-real-name-p left-name)
   (putnam-1987-a5-real-name-p right-name)
   (fn-equal
    (putnam-1987-a5-real-distance-function
     left-name right-name bound)
    (putnam-1987-a5-true-function '(eta)))))

(defun putnam-1987-a5-real-equal-p
    (left-name right-name)
  (putnam-1987-a5-real-distance-at-most-p
   left-name right-name 0))

(defun putnam-1987-a5-unary-output-function
    (function)
  (let ((output
         (putnam-1987-a5-apply-term function (list 'x))))
    (list
     'lambda
     '(x)
     (putnam-1987-a5-implies-term
      (list 'putnam-1987-a5-real-name-p 'x)
      (list 'putnam-1987-a5-real-name-p output)))))

(defun putnam-1987-a5-unary-extensional-function
    (function)
  (let ((left-output
         (putnam-1987-a5-apply-term
          function (list 'x-left)))
        (right-output
         (putnam-1987-a5-apply-term
          function (list 'x-right))))
    (list
     'lambda
     '(x-left x-right)
     (putnam-1987-a5-implies-term
      (list 'putnam-1987-a5-real-equal-p
            'x-left 'x-right)
      (list 'putnam-1987-a5-real-equal-p
            left-output right-output)))))

(defun putnam-1987-a5-real-function-p (function)
  (and
   (tamep-functionp function)
   (fn-equal
    (putnam-1987-a5-unary-output-function function)
    (putnam-1987-a5-true-function '(x)))
   (fn-equal
    (putnam-1987-a5-unary-extensional-function function)
    (putnam-1987-a5-true-function
     '(x-left x-right)))))

(defun putnam-1987-a5-rational-shift-name (name shift)
  (let ((value
         (putnam-1987-a5-object-real-value-term
          (putnam-1987-a5-quoted name)
          (putnam-1987-a5-multiply-term
           (putnam-1987-a5-quoted 1/2)
           'precision))))
    (list
     'lambda
     '(precision)
     (putnam-1987-a5-add-term
      value
      (putnam-1987-a5-quoted shift)))))

(defun putnam-1987-a5-constant-name (value)
  (list
   'lambda
   '(precision)
   (putnam-1987-a5-quoted value)))

(defun putnam-1987-a5-real-negate-name (name)
  (let ((value
         (putnam-1987-a5-object-real-value-term
          (putnam-1987-a5-quoted name)
          'precision)))
    (list
     'lambda
     '(precision)
     (putnam-1987-a5-negate-term value))))

(defun putnam-1987-a5-real-scale-name (name scalar)
  (let* ((sample-precision
          (putnam-1987-a5-divide-term
           'precision
           (putnam-1987-a5-add-term
            (putnam-1987-a5-quoted 1)
            (putnam-1987-a5-absolute-term
             (putnam-1987-a5-quoted scalar)))))
         (value
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-1987-a5-multiply-term
      (putnam-1987-a5-quoted scalar)
      value))))

(defun putnam-1987-a5-real-product-name (left-name right-name)
  (let* ((left-coarse
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted left-name)
           (putnam-1987-a5-quoted 1)))
         (right-coarse
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted right-name)
           (putnam-1987-a5-quoted 1)))
         (scale
          (putnam-1987-a5-multiply-term
           (putnam-1987-a5-quoted 64)
           (putnam-1987-a5-add-term
            (putnam-1987-a5-quoted 1)
            (putnam-1987-a5-add-term
             (putnam-1987-a5-absolute-term left-coarse)
             (putnam-1987-a5-absolute-term right-coarse)))))
         (sample-precision
          (putnam-1987-a5-minimum-term
           (putnam-1987-a5-quoted 1)
           (putnam-1987-a5-divide-term
            'precision scale)))
         (left-value
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted left-name)
           sample-precision))
         (right-value
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted right-name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-1987-a5-multiply-term
      left-value right-value))))

(defun putnam-1987-a5-real-absolute-name (name)
  (let ((value
         (putnam-1987-a5-object-real-value-term
          (putnam-1987-a5-quoted name)
          'precision)))
    (list
     'lambda
     '(precision)
     (putnam-1987-a5-absolute-term value))))

(defun putnam-1987-a5-real-less-equal-function
    (left-name right-name)
  (let* ((sample-precision
          (putnam-1987-a5-multiply-term
           (putnam-1987-a5-quoted 1/4)
           'eta))
         (left
          (putnam-1987-a5-real-value-term
           left-name sample-precision))
         (right
          (putnam-1987-a5-real-value-term
           right-name sample-precision)))
    (list
     'lambda
     '(eta)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-positive-rational-term 'eta)
      (putnam-1987-a5-less-equal-term
       left
       (putnam-1987-a5-add-term right 'eta))))))

(defun putnam-1987-a5-real-less-equal-p
    (left-name right-name)
  (and
   (putnam-1987-a5-real-name-p left-name)
   (putnam-1987-a5-real-name-p right-name)
   (fn-equal
    (putnam-1987-a5-real-less-equal-function
     left-name right-name)
    (putnam-1987-a5-true-function '(eta)))))

(defun putnam-1987-a5-positive-witness-p
    (epsilon name)
  (and
   (rationalp epsilon)
   (< 0 epsilon)
   (putnam-1987-a5-real-less-equal-p
    (putnam-1987-a5-constant-name epsilon)
    name)))

(defun putnam-1987-a5-positive-witness-failure-function
    (name)
  (list
   'lambda
   '(epsilon)
   (list
    'if
    (list 'putnam-1987-a5-positive-witness-p
          'epsilon
          (putnam-1987-a5-quoted name))
    (putnam-1987-a5-quoted nil)
    (putnam-1987-a5-quoted t))))

(defun putnam-1987-a5-real-positive-p (name)
  (let ((failure
         (putnam-1987-a5-positive-witness-failure-function
          name))
        (always-true
         (putnam-1987-a5-true-function '(epsilon))))
    (and
     (putnam-1987-a5-real-name-p name)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnam-1987-a5-real-add-name
    (left-name right-name)
  (let* ((sample-precision
          (putnam-1987-a5-multiply-term
           (putnam-1987-a5-quoted 1/4)
           'precision))
         (left
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted left-name)
           sample-precision))
         (right
          (putnam-1987-a5-object-real-value-term
           (putnam-1987-a5-quoted right-name)
           sample-precision)))
    (list
     'lambda
     '(precision)
     (putnam-1987-a5-add-term left right))))

(defun putnam-1987-a5-false-function (formals)
  (list 'lambda formals (putnam-1987-a5-quoted nil)))

(defun putnam-1987-a5-universal-p (function formals)
  (let ((always-true
         (putnam-1987-a5-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun putnam-1987-a5-exists-p (function formals)
  (let ((always-false
         (putnam-1987-a5-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun putnam-1987-a5-real-subtract-name
    (left-name right-name)
  (putnam-1987-a5-real-add-name
   left-name
   (putnam-1987-a5-real-negate-name right-name)))

;; Exact finite-dimensional real vectors.

(defun putnam-1987-a5-real-list-p (values)
  (if (consp values)
      (and
       (putnam-1987-a5-real-name-p (car values))
       (putnam-1987-a5-real-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1987-a5-vector-p (vector n)
  (and
   (natp n)
   (true-listp vector)
   (equal (len vector) n)
   (putnam-1987-a5-real-list-p vector)))

(defun putnam-1987-a5-vector-equal-p (left right)
  (if (consp left)
      (and
       (consp right)
       (putnam-1987-a5-real-equal-p
        (car left) (car right))
       (putnam-1987-a5-vector-equal-p
        (cdr left) (cdr right)))
    (equal right nil)))

(defun putnam-1987-a5-vector-zero-p (vector)
  (if (consp vector)
      (and
       (putnam-1987-a5-real-equal-p
        (car vector)
        (putnam-1987-a5-constant-name 0))
       (putnam-1987-a5-vector-zero-p (cdr vector)))
    (equal vector nil)))

(defun putnam-1987-a5-vector-nonzero-p (vector n)
  (and
   (putnam-1987-a5-vector-p vector n)
   (not (putnam-1987-a5-vector-zero-p vector))))

(defun putnam-1987-a5-vector-close-p
    (left right bound)
  (if (consp left)
      (and
       (consp right)
       (putnam-1987-a5-real-distance-at-most-p
        (car left) (car right) bound)
       (putnam-1987-a5-vector-close-p
        (cdr left) (cdr right) bound))
    (equal right nil)))

(defun putnam-1987-a5-vector-add (left right)
  (if (and (consp left) (consp right))
      (cons
       (putnam-1987-a5-real-add-name
        (car left) (car right))
       (putnam-1987-a5-vector-add
        (cdr left) (cdr right)))
    nil))

(defun putnam-1987-a5-vector-smul (scalar vector)
  (if (consp vector)
      (cons
       (putnam-1987-a5-real-product-name
        scalar (car vector))
       (putnam-1987-a5-vector-smul
        scalar (cdr vector)))
    nil))

(defun putnam-1987-a5-vector-rational-shift
    (vector index shift)
  (if (consp vector)
      (if (zp index)
          (cons
           (putnam-1987-a5-rational-shift-name
            (car vector) shift)
           (cdr vector))
        (cons
         (car vector)
         (putnam-1987-a5-vector-rational-shift
          (cdr vector) (- index 1) shift)))
    nil))

(defun putnam-1987-a5-index-p (index n)
  (and (natp index) (< index n)))

;; Extensional component families, scalar functions, and derivative fields.

(defun putnam-1987-a5-component-output-function
    (n function)
  (let ((output
         (putnam-1987-a5-apply-term function '(i x))))
    (list
     'lambda '(i x)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x (putnam-1987-a5-quoted n))))
      (list 'putnam-1987-a5-real-name-p output)))))

(defun putnam-1987-a5-component-extensional-function
    (n function)
  (let ((left
         (putnam-1987-a5-apply-term
          function '(i x-left)))
        (right
         (putnam-1987-a5-apply-term
          function '(i x-right))))
    (list
     'lambda '(i x-left x-right)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-left (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-right (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1987-a5-real-equal-p
            left right)))))

(defun putnam-1987-a5-component-function-p
    (n function)
  (and
   (tamep-functionp function)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-component-output-function
     n function)
    '(i x))
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-component-extensional-function
     n function)
    '(i x-left x-right))))

(defun putnam-1987-a5-scalar-output-function
    (n function)
  (let ((output
         (putnam-1987-a5-apply-term function '(x))))
    (list
     'lambda '(x)
     (putnam-1987-a5-implies-term
      (list 'putnam-1987-a5-vector-p
            'x (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-real-name-p output)))))

(defun putnam-1987-a5-scalar-extensional-function
    (n function)
  (let ((left
         (putnam-1987-a5-apply-term function '(x-left)))
        (right
         (putnam-1987-a5-apply-term function '(x-right))))
    (list
     'lambda '(x-left x-right)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-vector-p
              'x-left (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-right (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1987-a5-real-equal-p
            left right)))))

(defun putnam-1987-a5-scalar-function-p
    (n function)
  (and
   (tamep-functionp function)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-scalar-output-function
     n function)
    '(x))
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-scalar-extensional-function
     n function)
    '(x-left x-right))))

(defun putnam-1987-a5-first-field-output-function
    (n field)
  (let ((output
         (putnam-1987-a5-apply-term field '(i j x))))
    (list
     'lambda '(i j x)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'j (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x (putnam-1987-a5-quoted n))))
      (list 'putnam-1987-a5-real-name-p output)))))

(defun putnam-1987-a5-first-field-extensional-function
    (n field)
  (let ((left
         (putnam-1987-a5-apply-term
          field '(i j x-left)))
        (right
         (putnam-1987-a5-apply-term
          field '(i j x-right))))
    (list
     'lambda '(i j x-left x-right)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'j (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-left (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-right (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1987-a5-real-equal-p
            left right)))))

(defun putnam-1987-a5-first-field-p (n field)
  (and
   (tamep-functionp field)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-first-field-output-function
     n field)
    '(i j x))
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-first-field-extensional-function
     n field)
    '(i j x-left x-right))))

(defun putnam-1987-a5-second-field-output-function
    (n field)
  (let ((output
         (putnam-1987-a5-apply-term field '(i j k x))))
    (list
     'lambda '(i j k x)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'j (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'k (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x (putnam-1987-a5-quoted n))))
      (list 'putnam-1987-a5-real-name-p output)))))

(defun putnam-1987-a5-second-field-extensional-function
    (n field)
  (let ((left
         (putnam-1987-a5-apply-term
          field '(i j k x-left)))
        (right
         (putnam-1987-a5-apply-term
          field '(i j k x-right))))
    (list
     'lambda '(i j k x-left x-right)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'j (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'k (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-left (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-p
              'x-right (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-equal-p
              'x-left 'x-right)))
      (list 'putnam-1987-a5-real-equal-p
            left right)))))

(defun putnam-1987-a5-second-field-p (n field)
  (and
   (tamep-functionp field)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-second-field-output-function
     n field)
    '(i j k x))
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-second-field-extensional-function
     n field)
    '(i j k x-left x-right))))

(defun putnam-1987-a5-constant-field-output-function
    (n field)
  (let ((output
         (putnam-1987-a5-apply-term field '(i j))))
    (list
     'lambda '(i j)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-index-p
              'i (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-index-p
              'j (putnam-1987-a5-quoted n))))
      (list 'putnam-1987-a5-real-name-p output)))))

(defun putnam-1987-a5-constant-field-p (n field)
  (and
   (tamep-functionp field)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-constant-field-output-function
     n field)
    '(i j))))

;; Joint continuity on punctured R^3, expressed with the sup metric.

(defun putnam-1987-a5-component-continuity-delta-row
    (n function i x epsilon delta)
  (let ((at-x
         (putnam-1987-a5-apply-term
          function
          (list (putnam-1987-a5-quoted i)
                (putnam-1987-a5-quoted x))))
        (at-y
         (putnam-1987-a5-apply-term
          function
          (list (putnam-1987-a5-quoted i) 'y))))
    (list
     'lambda '(y)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-vector-p
              'y (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-nonzero-p
              'y (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-close-p
              (putnam-1987-a5-quoted x)
              'y
              (putnam-1987-a5-quoted delta))))
      (list 'putnam-1987-a5-real-distance-at-most-p
            at-x at-y
            (putnam-1987-a5-quoted epsilon))))))

(defun putnam-1987-a5-component-continuity-delta-p
    (n function i x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-component-continuity-delta-row
     n function i x epsilon delta)
    '(y))))

(defun putnam-1987-a5-component-continuity-radius-function
    (n function i x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1987-a5-component-continuity-delta-p
         (putnam-1987-a5-quoted n)
         (putnam-1987-a5-quoted function)
         (putnam-1987-a5-quoted i)
         (putnam-1987-a5-quoted x)
         (putnam-1987-a5-quoted epsilon)
         'delta)))

(defun putnam-1987-a5-component-continuity-row
    (n function)
  (list
   'lambda '(i x epsilon)
   (putnam-1987-a5-implies-term
    (putnam-1987-a5-and-terms
     (list
      (list 'putnam-1987-a5-index-p
            'i (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-p
            'x (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-nonzero-p
            'x (putnam-1987-a5-quoted n))
      (putnam-1987-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1987-a5-exists-p
          (list
           'putnam-1987-a5-component-continuity-radius-function
           (putnam-1987-a5-quoted n)
           (putnam-1987-a5-quoted function)
           'i 'x 'epsilon)
          (putnam-1987-a5-quoted '(delta))))))

(defun putnam-1987-a5-component-continuous-p
    (n function)
  (and
   (putnam-1987-a5-component-function-p n function)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-component-continuity-row
     n function)
    '(i x epsilon))))

(defun putnam-1987-a5-first-continuity-delta-row
    (n field i j x epsilon delta)
  (let ((at-x
         (putnam-1987-a5-apply-term
          field
          (list (putnam-1987-a5-quoted i)
                (putnam-1987-a5-quoted j)
                (putnam-1987-a5-quoted x))))
        (at-y
         (putnam-1987-a5-apply-term
          field
          (list (putnam-1987-a5-quoted i)
                (putnam-1987-a5-quoted j)
                'y))))
    (list
     'lambda '(y)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-vector-p
              'y (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-nonzero-p
              'y (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-close-p
              (putnam-1987-a5-quoted x)
              'y
              (putnam-1987-a5-quoted delta))))
      (list 'putnam-1987-a5-real-distance-at-most-p
            at-x at-y
            (putnam-1987-a5-quoted epsilon))))))

(defun putnam-1987-a5-first-continuity-delta-p
    (n field i j x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-first-continuity-delta-row
     n field i j x epsilon delta)
    '(y))))

(defun putnam-1987-a5-first-continuity-radius-function
    (n field i j x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1987-a5-first-continuity-delta-p
         (putnam-1987-a5-quoted n)
         (putnam-1987-a5-quoted field)
         (putnam-1987-a5-quoted i)
         (putnam-1987-a5-quoted j)
         (putnam-1987-a5-quoted x)
         (putnam-1987-a5-quoted epsilon)
         'delta)))

(defun putnam-1987-a5-first-continuity-row
    (n field)
  (list
   'lambda '(i j x epsilon)
   (putnam-1987-a5-implies-term
    (putnam-1987-a5-and-terms
     (list
      (list 'putnam-1987-a5-index-p
            'i (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-index-p
            'j (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-p
            'x (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-nonzero-p
            'x (putnam-1987-a5-quoted n))
      (putnam-1987-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1987-a5-exists-p
          (list
           'putnam-1987-a5-first-continuity-radius-function
           (putnam-1987-a5-quoted n)
           (putnam-1987-a5-quoted field)
           'i 'j 'x 'epsilon)
          (putnam-1987-a5-quoted '(delta))))))

(defun putnam-1987-a5-first-continuous-p (n field)
  (and
   (putnam-1987-a5-first-field-p n field)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-first-continuity-row n field)
    '(i j x epsilon))))

(defun putnam-1987-a5-second-continuity-delta-row
    (n field i j k x epsilon delta)
  (let ((at-x
         (putnam-1987-a5-apply-term
          field
          (list (putnam-1987-a5-quoted i)
                (putnam-1987-a5-quoted j)
                (putnam-1987-a5-quoted k)
                (putnam-1987-a5-quoted x))))
        (at-y
         (putnam-1987-a5-apply-term
          field
          (list (putnam-1987-a5-quoted i)
                (putnam-1987-a5-quoted j)
                (putnam-1987-a5-quoted k)
                'y))))
    (list
     'lambda '(y)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'putnam-1987-a5-vector-p
              'y (putnam-1987-a5-quoted n))
        (list 'putnam-1987-a5-vector-close-p
              (putnam-1987-a5-quoted x)
              'y
              (putnam-1987-a5-quoted delta))))
      (list 'putnam-1987-a5-real-distance-at-most-p
            at-x at-y
            (putnam-1987-a5-quoted epsilon))))))

(defun putnam-1987-a5-second-continuity-delta-p
    (n field i j k x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-second-continuity-delta-row
     n field i j k x epsilon delta)
    '(y))))

(defun putnam-1987-a5-second-continuity-radius-function
    (n field i j k x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1987-a5-second-continuity-delta-p
         (putnam-1987-a5-quoted n)
         (putnam-1987-a5-quoted field)
         (putnam-1987-a5-quoted i)
         (putnam-1987-a5-quoted j)
         (putnam-1987-a5-quoted k)
         (putnam-1987-a5-quoted x)
         (putnam-1987-a5-quoted epsilon)
         'delta)))

(defun putnam-1987-a5-second-continuity-row
    (n field)
  (list
   'lambda '(i j k x epsilon)
   (putnam-1987-a5-implies-term
    (putnam-1987-a5-and-terms
     (list
      (list 'putnam-1987-a5-index-p
            'i (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-index-p
            'j (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-index-p
            'k (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-p
            'x (putnam-1987-a5-quoted n))
      (putnam-1987-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1987-a5-exists-p
          (list
           'putnam-1987-a5-second-continuity-radius-function
           (putnam-1987-a5-quoted n)
           (putnam-1987-a5-quoted field)
           'i 'j 'k 'x 'epsilon)
          (putnam-1987-a5-quoted '(delta))))))

(defun putnam-1987-a5-second-continuous-p (n field)
  (and
   (putnam-1987-a5-second-field-p n field)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-second-continuity-row n field)
    '(i j k x epsilon))))

;; Coordinate derivatives at punctured points from rational increments, which
;; are dense in R.

(defun putnam-1987-a5-component-difference-quotient-name
    (function i x j h)
  (let* ((shifted-x
          (putnam-1987-a5-vector-rational-shift
           x j h))
         (shifted-output
          (apply$ function (list i shifted-x)))
         (base-output
          (apply$ function (list i x)))
         (sample-precision
          (* (/ (abs h) 4) 1)))
    (list
     'lambda '(eta)
     (putnam-1987-a5-divide-term
      (putnam-1987-a5-subtract-term
       (putnam-1987-a5-object-real-value-term
        (putnam-1987-a5-quoted shifted-output)
        (putnam-1987-a5-multiply-term
         (putnam-1987-a5-quoted sample-precision)
         'eta))
       (putnam-1987-a5-object-real-value-term
        (putnam-1987-a5-quoted base-output)
        (putnam-1987-a5-multiply-term
         (putnam-1987-a5-quoted sample-precision)
         'eta)))
      (putnam-1987-a5-quoted h)))))

(defun putnam-1987-a5-first-delta-row
    (function field i j x epsilon delta)
  (let ((quotient
         (list 'putnam-1987-a5-component-difference-quotient-name
               (putnam-1987-a5-quoted function)
               (putnam-1987-a5-quoted i)
               (putnam-1987-a5-quoted x)
               (putnam-1987-a5-quoted j)
               'h))
        (derivative
         (putnam-1987-a5-apply-term
          field
          (list (putnam-1987-a5-quoted i)
                (putnam-1987-a5-quoted j)
                (putnam-1987-a5-quoted x)))))
    (list
     'lambda '(h)
     (putnam-1987-a5-implies-term
      (putnam-1987-a5-and-terms
       (list
        (list 'rationalp 'h)
        (putnam-1987-a5-not-term
         (list 'equal 'h (putnam-1987-a5-quoted 0)))
        (putnam-1987-a5-less-equal-term
         (putnam-1987-a5-absolute-term 'h)
         (putnam-1987-a5-quoted delta))))
      (list 'putnam-1987-a5-real-distance-at-most-p
            quotient derivative
            (putnam-1987-a5-quoted epsilon))))))

(defun putnam-1987-a5-first-delta-p
    (function field i j x epsilon delta)
  (and
   (rationalp delta)
   (< 0 delta)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-first-delta-row
     function field i j x epsilon delta)
    '(h))))

(defun putnam-1987-a5-first-radius-function
    (function field i j x epsilon)
  (list
   'lambda '(delta)
   (list 'putnam-1987-a5-first-delta-p
         (putnam-1987-a5-quoted function)
         (putnam-1987-a5-quoted field)
         (putnam-1987-a5-quoted i)
         (putnam-1987-a5-quoted j)
         (putnam-1987-a5-quoted x)
         (putnam-1987-a5-quoted epsilon)
         'delta)))

(defun putnam-1987-a5-first-partial-row
    (n function field)
  (list
   'lambda '(i j x epsilon)
   (putnam-1987-a5-implies-term
    (putnam-1987-a5-and-terms
     (list
      (list 'putnam-1987-a5-index-p
            'i (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-index-p
            'j (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-p
            'x (putnam-1987-a5-quoted n))
      (list 'putnam-1987-a5-vector-nonzero-p
            'x (putnam-1987-a5-quoted n))
      (putnam-1987-a5-positive-rational-term
       'epsilon)))
    (list 'putnam-1987-a5-exists-p
          (list 'putnam-1987-a5-first-radius-function
                (putnam-1987-a5-quoted function)
                (putnam-1987-a5-quoted field)
                'i 'j 'x 'epsilon)
          (putnam-1987-a5-quoted '(delta))))))

(defun putnam-1987-a5-first-partial-field-p
    (n function field)
  (and
   (putnam-1987-a5-component-function-p n function)
   (putnam-1987-a5-first-field-p n field)
   (putnam-1987-a5-universal-p
    (putnam-1987-a5-first-partial-row
     n function field)
    '(i j x epsilon))))

;; Curl F = 0 on punctured R^3. FIELD(i,j,x) is the j-th coordinate
;; derivative of the i-th component of F at x.

(defun putnam-1987-a5-curl-zero-point-p (field x)
  (let ((zero (putnam-1987-a5-constant-name 0)))
    (and
     (putnam-1987-a5-real-equal-p
      (putnam-1987-a5-real-subtract-name
       (apply$ field (list 2 1 x))
       (apply$ field (list 1 2 x)))
      zero)
     (putnam-1987-a5-real-equal-p
      (putnam-1987-a5-real-subtract-name
       (apply$ field (list 0 2 x))
       (apply$ field (list 2 0 x)))
      zero)
     (putnam-1987-a5-real-equal-p
      (putnam-1987-a5-real-subtract-name
       (apply$ field (list 1 0 x))
       (apply$ field (list 0 1 x)))
      zero))))

(defun putnam-1987-a5-curl-zero-row (field)
  (list
   'lambda '(x)
   (putnam-1987-a5-implies-term
    (list 'putnam-1987-a5-vector-nonzero-p
          'x (putnam-1987-a5-quoted 3))
    (list 'putnam-1987-a5-curl-zero-point-p
          (putnam-1987-a5-quoted field)
          'x))))

(defun putnam-1987-a5-curl-zero-p (field)
  (putnam-1987-a5-universal-p
   (putnam-1987-a5-curl-zero-row field)
   '(x)))

;; On z = 0 the field equals G. Away from (x,y) = (0,0), multiplying by
;; d = x^2+4y^2 gives d*M = -y and d*N = x. At the origin ACL2's explicit
;; zero clauses match total real division in the Lean and Isabelle sources.

(defun putnam-1987-a5-boundary-point-p
    (function x y)
  (let* ((zero (putnam-1987-a5-constant-name 0))
         (point (list x y zero))
         (m (apply$ function (list 0 point)))
         (n (apply$ function (list 1 point)))
         (p (apply$ function (list 2 point)))
         (x-squared
          (putnam-1987-a5-real-product-name x x))
         (y-squared
          (putnam-1987-a5-real-product-name y y))
         (denominator
          (putnam-1987-a5-real-add-name
           x-squared
           (putnam-1987-a5-real-scale-name
            y-squared 4))))
    (and
     (putnam-1987-a5-real-equal-p p zero)
     (if (and
          (putnam-1987-a5-real-equal-p x zero)
          (putnam-1987-a5-real-equal-p y zero))
         (and
          (putnam-1987-a5-real-equal-p m zero)
          (putnam-1987-a5-real-equal-p n zero))
       (and
        (putnam-1987-a5-real-equal-p
         (putnam-1987-a5-real-product-name
          denominator m)
         (putnam-1987-a5-real-negate-name y))
        (putnam-1987-a5-real-equal-p
         (putnam-1987-a5-real-product-name
          denominator n)
         x))))))

(defun putnam-1987-a5-boundary-row (function)
  (list
   'lambda '(x y)
   (putnam-1987-a5-implies-term
    (putnam-1987-a5-and-terms
     (list
      (list 'putnam-1987-a5-real-name-p 'x)
      (list 'putnam-1987-a5-real-name-p 'y)))
    (list 'putnam-1987-a5-boundary-point-p
          (putnam-1987-a5-quoted function)
          'x 'y))))

(defun putnam-1987-a5-boundary-p (function)
  (putnam-1987-a5-universal-p
   (putnam-1987-a5-boundary-row function)
   '(x y)))

(defun putnam-1987-a5-field-witness-p
    (function first)
  (and
   (putnam-1987-a5-component-continuous-p
    3 function)
   (putnam-1987-a5-first-continuous-p
    3 first)
   (putnam-1987-a5-first-partial-field-p
    3 function first)
   (putnam-1987-a5-curl-zero-p first)
   (putnam-1987-a5-boundary-p function)))

(defun putnam-1987-a5-field-witness-function ()
  (list
   'lambda '(function first)
   (list 'putnam-1987-a5-field-witness-p
         'function 'first)))

(defun putnam-1987-a5-field-exists-p ()
  (putnam-1987-a5-exists-p
   (putnam-1987-a5-field-witness-function)
   '(function first)))

;; The PutnamBench solution annotation is False, so the source biconditional
;; is exactly the negation of the internally quantified existence assertion.

(defun putnambench-putnam-1987-a5-statement ()
  (not (putnam-1987-a5-field-exists-p)))

(value-triple :itpeval-statement-checked)
:q
