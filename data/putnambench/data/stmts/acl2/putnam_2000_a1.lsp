;; Statement-only formalization of PutnamBench corpus artifact putnam_2000_a1:
;; for positive real A, the squared sums of positive real sequences summing
;; to A are exactly the real numbers strictly between 0 and A^2. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A real is represented by a rational regular Cauchy name: at each positive
;; rational precision it returns a rational approximation. A sequence name
;; returns a pair whose CAR is such an approximation to x_j and whose CDR at
;; precision 1 is a positive rational lower bound for x_j. These names retain
;; arbitrary real values and an arbitrary function on the naturals; they are
;; neither rational-valued restrictions nor finite tables.
;;
;; The source existential sequence stays internal. Its witness is a list of
;; three function objects: the sequence and convergence moduli for its sum and
;; squared sum. Negated FN-EQUAL quantifies over that complete witness object.
;; The two limit matrices are the Cauchy definitions of
;;
;;   sum_j x_j = A  and  sum_j x_j^2 = S.
;;
;; The final IFF is the pointwise form of the source set equality. Strict
;; positivity is represented by an internal positive rational margin. For
;; A^2-S the approximations use an adaptive precision bounded from a
;; precision-1 approximation to A, so no real input is narrowed to ACL2's
;; rational number domain.

(defun putnam-2000-a1-quoted (object)
  (list 'quote object))

(defun putnam-2000-a1-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2000-a1-term-list (cdr terms)))
    nil))

(defun putnam-2000-a1-apply-term (function arguments)
  (list 'apply$
        (putnam-2000-a1-quoted function)
        (putnam-2000-a1-term-list arguments)))

(defun putnam-2000-a1-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2000-a1-and-terms (cdr terms))
            (putnam-2000-a1-quoted nil))
    (putnam-2000-a1-quoted t)))

(defun putnam-2000-a1-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2000-a1-quoted t)))

(defun putnam-2000-a1-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2000-a1-negate-term (value)
  (list 'unary-- value))

(defun putnam-2000-a1-subtract-term (left right)
  (putnam-2000-a1-add-term
   left
   (putnam-2000-a1-negate-term right)))

(defun putnam-2000-a1-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2000-a1-divide-term (numerator denominator)
  (putnam-2000-a1-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2000-a1-absolute-term (value)
  (list 'if
        (list '< value 0)
        (putnam-2000-a1-negate-term value)
        value))

(defun putnam-2000-a1-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2000-a1-quoted nil)
        (putnam-2000-a1-quoted t)))

(defun putnam-2000-a1-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-2000-a1-positive-rational-term (value)
  (putnam-2000-a1-and-terms
   (list
    (list 'rationalp value)
    (list '< 0 value))))

(defun putnam-2000-a1-true-function (formals)
  (list 'lambda
        formals
        (putnam-2000-a1-quoted t)))

(defun putnam-2000-a1-real-value-term (name precision)
  (putnam-2000-a1-apply-term name (list precision)))

(defun putnam-2000-a1-real-cauchy-function (name)
  (let* ((left
          (putnam-2000-a1-real-value-term name 'epsilon))
         (right
          (putnam-2000-a1-real-value-term name 'eta))
         (distance
          (putnam-2000-a1-absolute-term
           (putnam-2000-a1-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-and-terms
       (list
        (putnam-2000-a1-positive-rational-term 'epsilon)
        (putnam-2000-a1-positive-rational-term 'eta)))
      (putnam-2000-a1-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2000-a1-less-equal-term
         distance
         (putnam-2000-a1-add-term
          'epsilon 'eta))))))))

(defun putnam-2000-a1-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2000-a1-real-cauchy-function name)
    (putnam-2000-a1-true-function
     '(epsilon eta)))))

;; LOWER is a strict positive margin for the real denoted by NAME.
(defun putnam-2000-a1-positive-margin-function (name lower)
  (let ((value
         (putnam-2000-a1-real-value-term name 'epsilon)))
    (list
     'lambda
     '(epsilon)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-positive-rational-term 'epsilon)
      (putnam-2000-a1-and-terms
       (list
        (list 'rationalp value)
        (putnam-2000-a1-less-equal-term
         (putnam-2000-a1-quoted lower)
         (putnam-2000-a1-add-term
          value 'epsilon))))))))

(defun putnam-2000-a1-positive-margin-p (name lower)
  (and
   (rationalp lower)
   (< 0 lower)
   (fn-equal
    (putnam-2000-a1-positive-margin-function
     name lower)
    (putnam-2000-a1-true-function '(epsilon)))))

(defun putnam-2000-a1-positive-margin-failure-function (name)
  (list
   'lambda
   '(lower)
   (list
    'if
    (list
     'putnam-2000-a1-positive-margin-p
     (putnam-2000-a1-quoted name)
     'lower)
    (putnam-2000-a1-quoted nil)
    (putnam-2000-a1-quoted t))))

(defun putnam-2000-a1-positive-real-p (name)
  (let ((failure-function
         (putnam-2000-a1-positive-margin-failure-function
          name))
        (true-function
         (putnam-2000-a1-true-function '(lower))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

;; This matrix gives a strict positive margin for A^2-S. If a1 approximates A
;; at precision 1, then 2+|a1| bounds both A and every A-approximation taken
;; below at precision at most 1. The adaptive DELTA therefore controls the
;; squaring error uniformly.
(defun putnam-2000-a1-square-gap-margin-function
    (a s lower)
  (let* ((a-at-one
          (putnam-2000-a1-real-value-term a 1))
         (bound
          (putnam-2000-a1-add-term
           2
           (putnam-2000-a1-absolute-term a-at-one)))
         (candidate-delta
          (putnam-2000-a1-divide-term
           'epsilon
           (putnam-2000-a1-multiply-term 4 bound)))
         (delta
          (putnam-2000-a1-minimum-term
           1 candidate-delta))
         (a-value
          (putnam-2000-a1-real-value-term a delta))
         (s-value
          (putnam-2000-a1-real-value-term s 'epsilon))
         (gap-approximation
          (putnam-2000-a1-subtract-term
           (putnam-2000-a1-multiply-term
            a-value a-value)
           s-value)))
    (list
     'lambda
     '(epsilon)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-positive-rational-term 'epsilon)
      (putnam-2000-a1-and-terms
       (list
        (list 'rationalp a-at-one)
        (list 'rationalp a-value)
        (list 'rationalp s-value)
        (putnam-2000-a1-less-equal-term
         (putnam-2000-a1-quoted lower)
         (putnam-2000-a1-add-term
          gap-approximation
          (putnam-2000-a1-multiply-term
           2 'epsilon)))))))))

(defun putnam-2000-a1-square-gap-margin-p
    (a s lower)
  (and
   (rationalp lower)
   (< 0 lower)
   (fn-equal
    (putnam-2000-a1-square-gap-margin-function
     a s lower)
    (putnam-2000-a1-true-function '(epsilon)))))

(defun putnam-2000-a1-square-gap-failure-function (a s)
  (list
   'lambda
   '(lower)
   (list
    'if
    (list
     'putnam-2000-a1-square-gap-margin-p
     (putnam-2000-a1-quoted a)
     (putnam-2000-a1-quoted s)
     'lower)
    (putnam-2000-a1-quoted nil)
    (putnam-2000-a1-quoted t))))

(defun putnam-2000-a1-square-gap-positive-p (a s)
  (let ((failure-function
         (putnam-2000-a1-square-gap-failure-function
          a s))
        (true-function
         (putnam-2000-a1-true-function '(lower))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

(defun putnam-2000-a1-in-solution-interval-p (a s)
  (and
   (putnam-2000-a1-positive-real-p s)
   (putnam-2000-a1-square-gap-positive-p a s)))

(defun putnam-2000-a1-sequence-component-term
    (sequence component index precision)
  (list component
        (putnam-2000-a1-apply-term
         sequence
         (list index precision))))

(defun putnam-2000-a1-sequence-cauchy-function (sequence)
  (let* ((left
          (putnam-2000-a1-sequence-component-term
           sequence 'car 'n 'epsilon))
         (right
          (putnam-2000-a1-sequence-component-term
           sequence 'car 'n 'eta))
         (distance
          (putnam-2000-a1-absolute-term
           (putnam-2000-a1-subtract-term left right))))
    (list
     'lambda
     '(n epsilon eta)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-and-terms
       (list
        (list 'natp 'n)
        (putnam-2000-a1-positive-rational-term 'epsilon)
        (putnam-2000-a1-positive-rational-term 'eta)))
      (putnam-2000-a1-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2000-a1-less-equal-term
         distance
         (putnam-2000-a1-add-term
          'epsilon 'eta))))))))

(defun putnam-2000-a1-sequence-positive-function (sequence)
  (let ((lower
         (putnam-2000-a1-sequence-component-term
          sequence 'cdr 'n 1))
        (value
         (putnam-2000-a1-sequence-component-term
          sequence 'car 'n 'epsilon)))
    (list
     'lambda
     '(n epsilon)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-and-terms
       (list
        (list 'natp 'n)
        (putnam-2000-a1-positive-rational-term 'epsilon)))
      (putnam-2000-a1-and-terms
       (list
        (putnam-2000-a1-positive-rational-term lower)
        (list 'rationalp value)
        (putnam-2000-a1-less-equal-term
         lower
         (putnam-2000-a1-add-term
          value 'epsilon))))))))

(defun putnam-2000-a1-positive-sequence-p (sequence)
  (and
   (tamep-functionp sequence)
   (fn-equal
    (putnam-2000-a1-sequence-cauchy-function sequence)
    (putnam-2000-a1-true-function
     '(n epsilon eta)))
   (fn-equal
    (putnam-2000-a1-sequence-positive-function sequence)
    (putnam-2000-a1-true-function
     '(n epsilon)))))

(defun putnam-2000-a1-modulus-function (modulus)
  (let ((cutoff
         (putnam-2000-a1-apply-term modulus '(epsilon))))
    (list
     'lambda
     '(epsilon)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-positive-rational-term 'epsilon)
      (list 'natp cutoff)))))

(defun putnam-2000-a1-modulus-p (modulus)
  (and
   (tamep-functionp modulus)
   (fn-equal
    (putnam-2000-a1-modulus-function modulus)
    (putnam-2000-a1-true-function '(epsilon)))))

(defun putnam-2000-a1-sequence-value
    (sequence index precision)
  (car (apply$ sequence (list index precision))))

(defun putnam-2000-a1-partial-sum
    (sequence terms precision)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- (nfix terms) 1)))
      (+ (putnam-2000-a1-partial-sum
          sequence index precision)
         (putnam-2000-a1-sequence-value
          sequence index precision)))))

(defun putnam-2000-a1-square-precision
    (sequence index terms epsilon)
  (let* ((at-one
          (putnam-2000-a1-sequence-value
           sequence index 1))
         (bound (+ 2 (abs at-one)))
         (candidate
          (/ epsilon
             (* 4 (+ (nfix terms) 1) bound))))
    (if (< candidate 1)
        candidate
      1)))

(defun putnam-2000-a1-partial-square-sum
    (sequence remaining terms epsilon)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let* ((index (- (nfix remaining) 1))
           (precision
            (putnam-2000-a1-square-precision
             sequence index terms epsilon))
           (value
            (putnam-2000-a1-sequence-value
             sequence index precision)))
      (+ (putnam-2000-a1-partial-square-sum
          sequence index terms epsilon)
         (* value value)))))

(defun putnam-2000-a1-series-limit-function
    (sequence modulus target squaredp)
  (let* ((cutoff
          (putnam-2000-a1-apply-term
           modulus '(epsilon)))
         (target-value
          (putnam-2000-a1-real-value-term
           target 'epsilon))
         (term-precision
          (putnam-2000-a1-divide-term
           'epsilon
           (putnam-2000-a1-add-term 'terms 1)))
         (partial-sum
          (if squaredp
              (list
               'putnam-2000-a1-partial-square-sum
               (putnam-2000-a1-quoted sequence)
               'terms
               'terms
               'epsilon)
            (list
             'putnam-2000-a1-partial-sum
             (putnam-2000-a1-quoted sequence)
             'terms
             term-precision)))
         (distance
          (putnam-2000-a1-absolute-term
           (putnam-2000-a1-subtract-term
            partial-sum target-value))))
    (list
     'lambda
     '(epsilon terms)
     (putnam-2000-a1-implies-term
      (putnam-2000-a1-and-terms
       (list
        (putnam-2000-a1-positive-rational-term 'epsilon)
        (list 'natp 'terms)
        (putnam-2000-a1-less-equal-term
         cutoff 'terms)))
      (putnam-2000-a1-and-terms
       (list
        (list 'rationalp partial-sum)
        (list 'rationalp target-value)
        (putnam-2000-a1-less-equal-term
         distance
         (putnam-2000-a1-multiply-term
          4 'epsilon))))))))

(defun putnam-2000-a1-series-limit-p
    (sequence modulus target squaredp)
  (and
   (putnam-2000-a1-modulus-p modulus)
   (fn-equal
    (putnam-2000-a1-series-limit-function
     sequence modulus target squaredp)
    (putnam-2000-a1-true-function
     '(epsilon terms)))))

(defun putnam-2000-a1-attainment-witness-p
    (witness a s)
  (and
   (true-listp witness)
   (equal (len witness) 3)
   (let ((sequence (nth 0 witness))
         (sum-modulus (nth 1 witness))
         (square-modulus (nth 2 witness)))
     (and
      (putnam-2000-a1-positive-sequence-p sequence)
      (putnam-2000-a1-series-limit-p
       sequence sum-modulus a nil)
      (putnam-2000-a1-series-limit-p
       sequence square-modulus s t)))))

(defun putnam-2000-a1-attainment-failure-function (a s)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'putnam-2000-a1-attainment-witness-p
     'witness
     (putnam-2000-a1-quoted a)
     (putnam-2000-a1-quoted s))
    (putnam-2000-a1-quoted nil)
    (putnam-2000-a1-quoted t))))

(defun putnam-2000-a1-attainable-p (a s)
  (let ((failure-function
         (putnam-2000-a1-attainment-failure-function
          a s))
        (true-function
         (putnam-2000-a1-true-function '(witness))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2000-a1-statement (a s)
  (implies
   (and
    (putnam-2000-a1-real-name-p a)
    (putnam-2000-a1-real-name-p s)
    (putnam-2000-a1-positive-real-p a))
   (iff
    (putnam-2000-a1-attainable-p a s)
    (putnam-2000-a1-in-solution-interval-p a s))))

(value-triple :itpeval-statement-checked)
:q
