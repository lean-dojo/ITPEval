;; Statement-only formalization of PutnamBench corpus artifact putnam_2018_b4:
;; a real sequence with the stated third-order recurrence is periodic if one
;; of its terms is zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A real is represented by a rational regular Cauchy name. SEQUENCE maps a
;; natural index and a positive rational precision to a rational
;; approximation. FN-EQUAL supplies the unbounded universal quantifiers over
;; indices and precisions, so the values are genuine reals rather than a
;; rational-valued restriction or a finite table.
;;
;; The recurrence uniquely makes each term a nonzero integer polynomial in
;; a. Consequently, if any term is zero, then a is real algebraic, and the
;; entire recurrence-generated sequence has tame rational Cauchy names.
;; Conversely every accepted name denotes an actual real value. Hence every
;; possible source counterexample is represented even though ACL2 function
;; objects are syntactic.
;;
;; The recurrence comparison uses an adaptive precision. Approximations at
;; precision 1 bound the two factors, and the smaller precision then controls
;; the product error. Thus the rational inequalities below are equivalent to
;; the corresponding real equalities.
;;
;; A zero index and a positive period remain internal existential witnesses:
;; negated FN-EQUAL says that the associated failure predicate is not
;; identically true. Periodicity itself is checked at every natural index.

(defun putnam-2018-b4-quoted (object)
  (list 'quote object))

(defun putnam-2018-b4-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2018-b4-term-list (cdr terms)))
    nil))

(defun putnam-2018-b4-apply-term (function arguments)
  (list 'apply$
        (putnam-2018-b4-quoted function)
        (putnam-2018-b4-term-list arguments)))

(defun putnam-2018-b4-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2018-b4-and-terms (cdr terms))
            (putnam-2018-b4-quoted nil))
    (putnam-2018-b4-quoted t)))

(defun putnam-2018-b4-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2018-b4-quoted t)))

(defun putnam-2018-b4-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2018-b4-negate-term (value)
  (list 'unary-- value))

(defun putnam-2018-b4-subtract-term (left right)
  (putnam-2018-b4-add-term
   left
   (putnam-2018-b4-negate-term right)))

(defun putnam-2018-b4-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2018-b4-divide-term (numerator denominator)
  (putnam-2018-b4-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2018-b4-absolute-term (value)
  (list 'if
        (list '< value 0)
        (putnam-2018-b4-negate-term value)
        value))

(defun putnam-2018-b4-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2018-b4-quoted nil)
        (putnam-2018-b4-quoted t)))

(defun putnam-2018-b4-minimum-term (left right)
  (list 'if
        (list '< left right)
        left
        right))

(defun putnam-2018-b4-positive-rational-term (value)
  (putnam-2018-b4-and-terms
   (list
    (list 'rationalp value)
    (list '< 0 value))))

(defun putnam-2018-b4-true-function (formals)
  (list 'lambda
        formals
        (putnam-2018-b4-quoted t)))

(defun putnam-2018-b4-real-value-term (name precision)
  (putnam-2018-b4-apply-term name (list precision)))

(defun putnam-2018-b4-sequence-value-term
    (sequence index precision)
  (putnam-2018-b4-apply-term
   sequence
   (list index precision)))

(defun putnam-2018-b4-real-cauchy-function (name)
  (let* ((left
          (putnam-2018-b4-real-value-term
           name 'epsilon))
         (right
          (putnam-2018-b4-real-value-term
           name 'eta))
         (distance
          (putnam-2018-b4-absolute-term
           (putnam-2018-b4-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-and-terms
       (list
        (putnam-2018-b4-positive-rational-term
         'epsilon)
        (putnam-2018-b4-positive-rational-term
         'eta)))
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2018-b4-less-equal-term
         distance
         (putnam-2018-b4-add-term
          'epsilon 'eta))))))))

(defun putnam-2018-b4-real-name-p (name)
  (and
   (tamep-functionp name)
   (fn-equal
    (putnam-2018-b4-real-cauchy-function name)
    (putnam-2018-b4-true-function
     '(epsilon eta)))))

(defun putnam-2018-b4-sequence-cauchy-function
    (sequence)
  (let* ((left
          (putnam-2018-b4-sequence-value-term
           sequence 'n 'epsilon))
         (right
          (putnam-2018-b4-sequence-value-term
           sequence 'n 'eta))
         (distance
          (putnam-2018-b4-absolute-term
           (putnam-2018-b4-subtract-term left right))))
    (list
     'lambda
     '(n epsilon eta)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-and-terms
       (list
        (list 'natp 'n)
        (putnam-2018-b4-positive-rational-term
         'epsilon)
        (putnam-2018-b4-positive-rational-term
         'eta)))
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2018-b4-less-equal-term
         distance
         (putnam-2018-b4-add-term
          'epsilon 'eta))))))))

(defun putnam-2018-b4-sequence-name-p (sequence)
  (and
   (tamep-functionp sequence)
   (fn-equal
    (putnam-2018-b4-sequence-cauchy-function
     sequence)
    (putnam-2018-b4-true-function
     '(n epsilon eta)))))

(defun putnam-2018-b4-sequence-equals-constant-function
    (sequence index constant)
  (let* ((precision
          (putnam-2018-b4-multiply-term
           1/4 'epsilon))
         (value
          (putnam-2018-b4-sequence-value-term
           sequence
           (putnam-2018-b4-quoted index)
           precision))
         (distance
          (putnam-2018-b4-absolute-term
           (putnam-2018-b4-subtract-term
            value
            (putnam-2018-b4-quoted constant)))))
    (list
     'lambda
     '(epsilon)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-positive-rational-term
       'epsilon)
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp value)
        (putnam-2018-b4-less-equal-term
         distance 'epsilon)))))))

(defun putnam-2018-b4-sequence-equals-constant-p
    (sequence index constant)
  (fn-equal
   (putnam-2018-b4-sequence-equals-constant-function
    sequence index constant)
   (putnam-2018-b4-true-function '(epsilon))))

(defun putnam-2018-b4-sequence-equals-real-function
    (sequence index real-name)
  (let* ((precision
          (putnam-2018-b4-multiply-term
           1/4 'epsilon))
         (sequence-value
          (putnam-2018-b4-sequence-value-term
           sequence
           (putnam-2018-b4-quoted index)
           precision))
         (real-value
          (putnam-2018-b4-real-value-term
           real-name precision))
         (distance
          (putnam-2018-b4-absolute-term
           (putnam-2018-b4-subtract-term
            sequence-value real-value))))
    (list
     'lambda
     '(epsilon)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-positive-rational-term
       'epsilon)
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp sequence-value)
        (list 'rationalp real-value)
        (putnam-2018-b4-less-equal-term
         distance 'epsilon)))))))

(defun putnam-2018-b4-sequence-equals-real-p
    (sequence index real-name)
  (fn-equal
   (putnam-2018-b4-sequence-equals-real-function
    sequence index real-name)
   (putnam-2018-b4-true-function '(epsilon))))

(defun putnam-2018-b4-recurrence-function (sequence)
  (let* ((n-plus-1
          (putnam-2018-b4-add-term 'n 1))
         (n-plus-2
          (putnam-2018-b4-add-term 'n 2))
         (n-plus-3
          (putnam-2018-b4-add-term 'n 3))
         (factor-left-at-one
          (putnam-2018-b4-sequence-value-term
           sequence n-plus-2 1))
         (factor-right-at-one
          (putnam-2018-b4-sequence-value-term
           sequence n-plus-1 1))
         (factor-bound
          (putnam-2018-b4-add-term
           4
           (putnam-2018-b4-add-term
            (putnam-2018-b4-absolute-term
             factor-left-at-one)
            (putnam-2018-b4-absolute-term
             factor-right-at-one))))
         (precision-candidate
          (putnam-2018-b4-divide-term
           'epsilon
           (putnam-2018-b4-multiply-term
            16 factor-bound)))
         (precision
          (putnam-2018-b4-minimum-term
           1 precision-candidate))
         (next
          (putnam-2018-b4-sequence-value-term
           sequence n-plus-3 precision))
         (factor-left
          (putnam-2018-b4-sequence-value-term
           sequence n-plus-2 precision))
         (factor-right
          (putnam-2018-b4-sequence-value-term
           sequence n-plus-1 precision))
         (old
          (putnam-2018-b4-sequence-value-term
           sequence 'n precision))
         (right-hand-side
          (putnam-2018-b4-subtract-term
           (putnam-2018-b4-multiply-term
            2
            (putnam-2018-b4-multiply-term
             factor-left factor-right))
           old))
         (residual
          (putnam-2018-b4-absolute-term
           (putnam-2018-b4-subtract-term
            next right-hand-side))))
    (list
     'lambda
     '(n epsilon)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-and-terms
       (list
        (list 'natp 'n)
        (putnam-2018-b4-positive-rational-term
         'epsilon)))
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp factor-left-at-one)
        (list 'rationalp factor-right-at-one)
        (putnam-2018-b4-positive-rational-term
         precision)
        (list 'rationalp next)
        (list 'rationalp factor-left)
        (list 'rationalp factor-right)
        (list 'rationalp old)
        (putnam-2018-b4-less-equal-term
         residual 'epsilon)))))))

(defun putnam-2018-b4-recurrence-p (sequence)
  (fn-equal
   (putnam-2018-b4-recurrence-function sequence)
   (putnam-2018-b4-true-function '(n epsilon))))

(defun putnam-2018-b4-zero-function (sequence index)
  (let* ((precision
          (putnam-2018-b4-multiply-term
           1/2 'epsilon))
         (value
          (putnam-2018-b4-sequence-value-term
           sequence
           (putnam-2018-b4-quoted index)
           precision)))
    (list
     'lambda
     '(epsilon)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-positive-rational-term
       'epsilon)
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp value)
        (putnam-2018-b4-less-equal-term
         (putnam-2018-b4-absolute-term value)
         'epsilon)))))))

(defun putnam-2018-b4-zero-at-p (sequence index)
  (and
   (natp index)
   (fn-equal
    (putnam-2018-b4-zero-function sequence index)
    (putnam-2018-b4-true-function '(epsilon)))))

(defun-sk putnam-2018-b4-zero-exists-p (sequence)
  (exists (index)
    (putnam-2018-b4-zero-at-p sequence index)))

(defun putnam-2018-b4-periodicity-function
    (sequence period)
  (let* ((precision
          (putnam-2018-b4-multiply-term
           1/4 'epsilon))
         (shifted-index
          (putnam-2018-b4-add-term
           'n
           (putnam-2018-b4-quoted period)))
         (shifted-value
          (putnam-2018-b4-sequence-value-term
           sequence shifted-index precision))
         (value
          (putnam-2018-b4-sequence-value-term
           sequence 'n precision))
         (distance
          (putnam-2018-b4-absolute-term
           (putnam-2018-b4-subtract-term
            shifted-value value))))
    (list
     'lambda
     '(n epsilon)
     (putnam-2018-b4-implies-term
      (putnam-2018-b4-and-terms
       (list
        (list 'natp 'n)
        (putnam-2018-b4-positive-rational-term
         'epsilon)))
      (putnam-2018-b4-and-terms
       (list
        (list 'rationalp shifted-value)
        (list 'rationalp value)
        (putnam-2018-b4-less-equal-term
         distance 'epsilon)))))))

(defun putnam-2018-b4-period-witness-p
    (sequence period)
  (and
   (posp period)
   (fn-equal
    (putnam-2018-b4-periodicity-function
     sequence period)
    (putnam-2018-b4-true-function
     '(n epsilon)))))

(defun-sk putnam-2018-b4-period-exists-p (sequence)
  (exists (period)
    (putnam-2018-b4-period-witness-p sequence period)))

(defun putnambench-putnam-2018-b4-statement
    (a sequence)
  (implies
   (and
    (putnam-2018-b4-real-name-p a)
    (putnam-2018-b4-sequence-name-p sequence)
    (putnam-2018-b4-sequence-equals-constant-p
     sequence 0 1)
    (putnam-2018-b4-sequence-equals-real-p
     sequence 1 a)
    (putnam-2018-b4-sequence-equals-real-p
     sequence 2 a)
    (putnam-2018-b4-recurrence-p sequence)
    (putnam-2018-b4-zero-exists-p sequence))
   (putnam-2018-b4-period-exists-p sequence)))

(value-triple :itpeval-statement-checked)
:q
