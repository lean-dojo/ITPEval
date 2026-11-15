;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_b2:
;; every nonempty finite set of real numbers has a nonempty subset whose sum,
;; after adding an integer, has absolute value at most 1/(n+1). This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A real number is represented by a function object that maps every positive
;; rational precision to a rational approximation. The Cauchy condition below
;; makes the approximation at precision EPSILON lie within EPSILON of a unique
;; real limit. Conversely, every real number has such a rational Cauchy name,
;; so this does not restrict the source domain to rational values.

(defun putnam-2006-b2-quoted (object)
  (list 'quote object))

(defun putnam-2006-b2-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2006-b2-term-list (cdr terms)))
    nil))

(defun putnam-2006-b2-apply-term (function arguments)
  (list 'apply$
        (putnam-2006-b2-quoted function)
        (putnam-2006-b2-term-list arguments)))

(defun putnam-2006-b2-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2006-b2-and-terms (cdr terms))
            (putnam-2006-b2-quoted nil))
    (putnam-2006-b2-quoted t)))

(defun putnam-2006-b2-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2006-b2-quoted t)))

(defun putnam-2006-b2-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2006-b2-negate-term (value)
  (list 'unary-- value))

(defun putnam-2006-b2-subtract-term (left right)
  (putnam-2006-b2-add-term
   left
   (putnam-2006-b2-negate-term right)))

(defun putnam-2006-b2-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2006-b2-reciprocal-term (value)
  (list 'unary-/ value))

(defun putnam-2006-b2-divide-term (numerator denominator)
  (putnam-2006-b2-multiply-term
   numerator
   (putnam-2006-b2-reciprocal-term denominator)))

(defun putnam-2006-b2-absolute-term (value)
  (list 'if
        (list '<
              value
              (putnam-2006-b2-quoted 0))
        (putnam-2006-b2-negate-term value)
        value))

(defun putnam-2006-b2-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2006-b2-quoted nil)
        (putnam-2006-b2-quoted t)))

(defun putnam-2006-b2-positive-rational-term (value)
  (putnam-2006-b2-and-terms
   (list
    (list 'rationalp value)
    (list '<
          (putnam-2006-b2-quoted 0)
          value))))

(defun putnam-2006-b2-true-function (formals)
  (list 'lambda
        formals
        (putnam-2006-b2-quoted t)))

(defun putnam-2006-b2-cauchy-function (name)
  (let* ((at-epsilon
          (putnam-2006-b2-apply-term
           name
           (list 'epsilon)))
         (at-eta
          (putnam-2006-b2-apply-term
           name
           (list 'eta)))
         (distance
          (putnam-2006-b2-absolute-term
           (putnam-2006-b2-subtract-term
            at-epsilon at-eta))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2006-b2-implies-term
      (putnam-2006-b2-and-terms
       (list
        (putnam-2006-b2-positive-rational-term
         'epsilon)
        (putnam-2006-b2-positive-rational-term
         'eta)))
      (putnam-2006-b2-and-terms
       (list
        (list 'rationalp at-epsilon)
        (list 'rationalp at-eta)
        (putnam-2006-b2-less-equal-term
         distance
         (putnam-2006-b2-add-term
          'epsilon 'eta))))))))

(defun putnam-2006-b2-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2006-b2-cauchy-function name)
    (putnam-2006-b2-true-function
     '(epsilon eta)))))

;; Two valid Cauchy names denote the same real exactly when their values at
;; every positive rational EPSILON differ by at most 2*EPSILON.

(defun putnam-2006-b2-real-equality-function
    (left-name right-name)
  (let* ((left
          (putnam-2006-b2-apply-term
           left-name
           (list 'epsilon)))
         (right
          (putnam-2006-b2-apply-term
           right-name
           (list 'epsilon)))
         (distance
          (putnam-2006-b2-absolute-term
           (putnam-2006-b2-subtract-term
            left right))))
    (list
     'lambda
     '(epsilon)
     (putnam-2006-b2-implies-term
      (putnam-2006-b2-positive-rational-term
       'epsilon)
      (putnam-2006-b2-less-equal-term
       distance
       (putnam-2006-b2-multiply-term
        (putnam-2006-b2-quoted 2)
        'epsilon))))))

(defun putnam-2006-b2-real-equal-p
    (left-name right-name)
  (fn-equal
   (putnam-2006-b2-real-equality-function
    left-name right-name)
   (putnam-2006-b2-true-function
    '(epsilon))))

(defun putnam-2006-b2-distinct-from-list-p
    (name names)
  (if (consp names)
      (and
       (not
        (putnam-2006-b2-real-equal-p
         name (car names)))
       (putnam-2006-b2-distinct-from-list-p
        name (cdr names)))
    (equal names nil)))

(defun putnam-2006-b2-real-finset-list-p (names)
  (if (consp names)
      (and
       (putnam-2006-b2-real-name-p (car names))
       (putnam-2006-b2-distinct-from-list-p
        (car names) (cdr names))
       (putnam-2006-b2-real-finset-list-p
        (cdr names)))
    (equal names nil)))

;; A nonzero MASK below 2^(LEN NAMES) selects a nonempty subset of the
;; semantically distinct real values in NAMES. This is a bijective encoding of
;; the source subsets, not a finite restriction on the elements themselves.

(defun putnam-2006-b2-mask-cardinality (names mask)
  (if (consp names)
      (+ (mod mask 2)
         (putnam-2006-b2-mask-cardinality
          (cdr names)
          (floor mask 2)))
    0))

(defun putnam-2006-b2-selected-sum-term
    (names mask precision)
  (if (consp names)
      (let ((rest
             (putnam-2006-b2-selected-sum-term
              (cdr names)
              (floor mask 2)
              precision)))
        (if (equal (mod mask 2) 1)
            (putnam-2006-b2-add-term
             (putnam-2006-b2-apply-term
              (car names)
              (list precision))
             rest)
          rest))
    (putnam-2006-b2-quoted 0)))

;; If K elements are selected, each is sampled at EPSILON/K. The total
;; approximation error is at most EPSILON. Therefore the universal precision
;; inequality below is equivalent in both directions to
;;
;;   |M + sum(S)| <= 1/(N+1)
;;
;; for the represented real limits.

(defun putnam-2006-b2-subset-bound-function
    (names n mask m)
  (let* ((count
          (putnam-2006-b2-mask-cardinality
           names mask))
         (precision
          (putnam-2006-b2-divide-term
           'epsilon
           (putnam-2006-b2-quoted count)))
         (sum
          (putnam-2006-b2-selected-sum-term
           names mask precision))
         (absolute-total
          (putnam-2006-b2-absolute-term
           (putnam-2006-b2-add-term
            (putnam-2006-b2-quoted m)
            sum)))
         (bound
          (/ 1 (+ n 1))))
    (list
     'lambda
     '(epsilon)
     (putnam-2006-b2-implies-term
      (putnam-2006-b2-positive-rational-term
       'epsilon)
      (putnam-2006-b2-less-equal-term
       absolute-total
       (putnam-2006-b2-add-term
        (putnam-2006-b2-quoted bound)
        'epsilon))))))

(defun putnam-2006-b2-subset-bound-holds-p
    (names n mask m)
  (let ((bound-function
         (putnam-2006-b2-subset-bound-function
          names n mask m))
        (true-function
         (putnam-2006-b2-true-function
          '(epsilon))))
    (and
     (tamep-functionp bound-function)
     (tamep-functionp true-function)
     (fn-equal bound-function true-function))))

;; At precision 1, a valid Cauchy name differs from its represented real by at
;; most 1. Hence every subset sum has absolute value at most the sum below.
;; If an integer M satisfies the requested inequality, then
;;
;;   |M| <= 1 + sum_i (1 + |name_i(1)|).
;;
;; The numerator of this nonnegative rational is at least the rational itself.
;; Thus the integer search bound is complete, not an approximation. Together
;; with the finite mask search, this keeps both source witnesses internal
;; without placing an unbadged user function in a generated lambda.

(defun putnam-2006-b2-real-magnitude-bound (names)
  (if (consp names)
      (+ 1
         (abs
          (apply$ (car names) (list 1)))
         (putnam-2006-b2-real-magnitude-bound
          (cdr names)))
    0))

(defun putnam-2006-b2-integer-search-bound (names)
  (+ 1
     (numerator
      (putnam-2006-b2-real-magnitude-bound
       names))))

(defun putnam-2006-b2-integer-witness-in-list-p
    (names n mask integers)
  (if (consp integers)
      (let ((m (car integers)))
      (or
       (putnam-2006-b2-subset-bound-holds-p
        names n mask m)
       (putnam-2006-b2-integer-witness-in-list-p
        names n mask (cdr integers))))
    nil))

(defun putnam-2006-b2-subset-witness-in-list-p
    (names n integer-bound masks)
  (if (consp masks)
      (let ((mask (car masks)))
      (or
       (putnam-2006-b2-integer-witness-in-list-p
         names
         n
         mask
         (from-to-by
          (- integer-bound)
          integer-bound
          1))
       (putnam-2006-b2-subset-witness-in-list-p
        names n integer-bound (cdr masks))))
    nil))

(defun putnambench-putnam-2006-b2-statement
    (n names)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-2006-b2-real-finset-list-p names)
    (equal (len names) n))
   (let ((integer-bound
          (putnam-2006-b2-integer-search-bound
           names)))
     (putnam-2006-b2-subset-witness-in-list-p
      names
      n
      integer-bound
      (from-to-by
       1
       (- (expt 2 (len names)) 1)
       1)))))

(value-triple :itpeval-statement-checked)
:q
