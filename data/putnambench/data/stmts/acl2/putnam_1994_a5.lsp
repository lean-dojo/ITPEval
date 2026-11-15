;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_a5:
;; every nonempty real interval contains a nonempty subinterval avoiding all
;; sums of 1994 distinct terms of a positive null sequence. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; SEQUENCE is an ACL2 function object. At natural index N and positive
;; rational precision EPSILON, component 0 is a rational Cauchy approximation
;; to r_N, component 1 at precision 1 is a positive rational lower bound for
;; r_N, and component 2 at index 0 is a convergence cutoff. The matrices below
;; make this a name for an arbitrary positive real sequence tending to zero.
;;
;; The set parameter S is eliminated by substituting its defining equality.
;; It is equivalent to test rational A<B: every real interval contains a
;; rational subinterval, and a gap in that subinterval is a gap in the original
;; interval. The internal witness is (C D CUTOFF TAIL-BOUND PRECISION).
;; CUTOFF reduces each increasing 1994-tuple to its finite prefix below the
;; cutoff. The remaining terms are bounded by TAIL-BOUND, while rational
;; Cauchy approximations bound the prefix. The finite ALWAYS$+ check therefore
;; certifies that every represented sum is at most C or at least D.
;;
;; Conversely, the closure of the source sum set consists of sums of at most
;; 1994 terms with distinct indices, with missing terms equal to the sole limit
;; value 0. A closed rational subinterval of any source gap has positive
;; distance from this compact closure. Sufficiently small tail and Cauchy
;; bounds then give exactly such a finite certificate. Thus the certificate
;; formulation is bidirectionally equivalent and keeps C and D existential.

(defun putnam-1994-a5-quoted (object)
  (list 'quote object))

(defun putnam-1994-a5-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-1994-a5-term-list (cdr terms)))
    nil))

(defun putnam-1994-a5-apply-term (function arguments)
  (list
   'apply$
   (putnam-1994-a5-quoted function)
   (putnam-1994-a5-term-list arguments)))

(defun putnam-1994-a5-component-term
    (sequence component index precision)
  (list
   'nth
   (putnam-1994-a5-quoted component)
   (putnam-1994-a5-apply-term
    sequence
    (list index precision))))

(defun putnam-1994-a5-nth-term (index value)
  (list 'nth (putnam-1994-a5-quoted index) value))

(defun putnam-1994-a5-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-1994-a5-list-term (cdr terms)))
    (putnam-1994-a5-quoted nil)))

(defun putnam-1994-a5-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-1994-a5-and-terms (cdr terms))
       (putnam-1994-a5-quoted nil))
    (putnam-1994-a5-quoted t)))

(defun putnam-1994-a5-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-1994-a5-quoted t)
       (putnam-1994-a5-or-terms (cdr terms)))
    (putnam-1994-a5-quoted nil)))

(defun putnam-1994-a5-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (putnam-1994-a5-quoted t)))

(defun putnam-1994-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1994-a5-negate-term (value)
  (list 'unary-- value))

(defun putnam-1994-a5-subtract-term (left right)
  (putnam-1994-a5-add-term
   left
   (putnam-1994-a5-negate-term right)))

(defun putnam-1994-a5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1994-a5-divide-term (left right)
  (putnam-1994-a5-multiply-term
   left
   (list 'unary-/ right)))

(defun putnam-1994-a5-absolute-term (value)
  (list
   'if
   (list '< value (putnam-1994-a5-quoted 0))
   (putnam-1994-a5-negate-term value)
   value))

(defun putnam-1994-a5-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-1994-a5-quoted nil)
   (putnam-1994-a5-quoted t)))

(defun putnam-1994-a5-positive-rational-term (value)
  (putnam-1994-a5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-1994-a5-quoted 0) value))))

(defun putnam-1994-a5-range-term (upper)
  (list
   'from-to-by
   (putnam-1994-a5-quoted 0)
   upper
   (putnam-1994-a5-quoted 1)))

(defun putnam-1994-a5-true-function (formals)
  (list
   'lambda
   formals
   (putnam-1994-a5-quoted t)))

;; A regular rational Cauchy name determines one real at every natural index.
(defun putnam-1994-a5-cauchy-function (sequence)
  (let* ((at-epsilon
          (putnam-1994-a5-component-term
           sequence 0 'n 'epsilon))
         (at-eta
          (putnam-1994-a5-component-term
           sequence 0 'n 'eta))
         (distance
          (putnam-1994-a5-absolute-term
           (putnam-1994-a5-subtract-term
            at-epsilon at-eta))))
    (list
     'lambda
     '(n epsilon eta)
     (putnam-1994-a5-implies-term
      (putnam-1994-a5-and-terms
       (list
        (list 'natp 'n)
        (putnam-1994-a5-positive-rational-term 'epsilon)
        (putnam-1994-a5-positive-rational-term 'eta)))
      (putnam-1994-a5-and-terms
       (list
        (list 'rationalp at-epsilon)
        (list 'rationalp at-eta)
        (putnam-1994-a5-less-equal-term
         distance
         (putnam-1994-a5-add-term
          'epsilon 'eta))))))))

;; A positive rational lower bound valid at every precision is equivalent to
;; strict positivity of the represented real.
(defun putnam-1994-a5-positive-function (sequence)
  (let ((lower
         (putnam-1994-a5-component-term
          sequence 1 'n (putnam-1994-a5-quoted 1)))
        (value
         (putnam-1994-a5-component-term
          sequence 0 'n 'epsilon)))
    (list
     'lambda
     '(n epsilon)
     (putnam-1994-a5-implies-term
      (putnam-1994-a5-and-terms
       (list
        (list 'natp 'n)
        (putnam-1994-a5-positive-rational-term 'epsilon)))
      (putnam-1994-a5-and-terms
       (list
        (putnam-1994-a5-positive-rational-term lower)
        (list 'rationalp value)
        (putnam-1994-a5-less-equal-term
         lower
         (putnam-1994-a5-add-term
          value 'epsilon))))))))

;; For every positive tolerance, component 2 supplies an internal natural
;; cutoff after which the represented real values have absolute value below
;; that tolerance. The strict 3/4 approximation bound leaves 1/4 for the
;; Cauchy-name error and is equivalent to convergence to zero.
(defun putnam-1994-a5-zero-limit-function (sequence)
  (let* ((cutoff
          (putnam-1994-a5-component-term
           sequence 2
           (putnam-1994-a5-quoted 0)
           'epsilon))
         (quarter-epsilon
          (putnam-1994-a5-divide-term
           'epsilon
           (putnam-1994-a5-quoted 4)))
         (value
          (putnam-1994-a5-component-term
           sequence 0 'n quarter-epsilon))
         (three-quarters
          (putnam-1994-a5-multiply-term
           (putnam-1994-a5-quoted 3)
           quarter-epsilon)))
    (list
     'lambda
     '(epsilon n)
     (putnam-1994-a5-implies-term
      (putnam-1994-a5-positive-rational-term 'epsilon)
      (putnam-1994-a5-and-terms
       (list
        (list 'natp cutoff)
        (putnam-1994-a5-implies-term
         (putnam-1994-a5-and-terms
          (list
           (list 'natp 'n)
           (putnam-1994-a5-less-equal-term
            cutoff 'n)))
         (putnam-1994-a5-and-terms
          (list
           (list 'rationalp value)
           (list '<
                 (putnam-1994-a5-absolute-term value)
                 three-quarters))))))))))

;; CODE is the base-(CUTOFF+1) encoding of 1994 entries. A qualifying code is
;; a strictly increasing prefix below CUTOFF followed only by the sentinel
;; CUTOFF. It represents every possible finite prefix of an increasing source
;; index tuple.
(defun putnam-1994-a5-digit-term
    (code cutoff position)
  (let ((base
         (putnam-1994-a5-add-term
          cutoff
          (putnam-1994-a5-quoted 1))))
    (list
     'mod
     (list
      'floor
      code
      (list 'expt base position))
     base)))

(defun putnam-1994-a5-prefix-valid-function ()
  (let* ((cutoff
          (putnam-1994-a5-nth-term 0 'globals))
         (code
          (putnam-1994-a5-nth-term 1 'globals))
         (digit
          (putnam-1994-a5-digit-term
           code cutoff 'position))
         (previous-position
          (putnam-1994-a5-subtract-term
           'position
           (putnam-1994-a5-quoted 1)))
         (previous-digit
          (putnam-1994-a5-digit-term
           code cutoff previous-position)))
    (list
     'lambda
     '(globals position)
     (list
      'if
      (list '< digit cutoff)
      (putnam-1994-a5-or-terms
       (list
        (list 'equal
              'position
              (putnam-1994-a5-quoted 0))
        (list '< previous-digit digit)))
      (list 'equal digit cutoff)))))

(defun putnam-1994-a5-prefix-count-function ()
  (let* ((cutoff
          (putnam-1994-a5-nth-term 0 'globals))
         (code
          (putnam-1994-a5-nth-term 1 'globals))
         (digit
          (putnam-1994-a5-digit-term
           code cutoff 'position)))
    (list
     'lambda
     '(globals position)
     (list
      'if
      (list '< digit cutoff)
      (putnam-1994-a5-quoted 1)
      (putnam-1994-a5-quoted 0)))))

(defun putnam-1994-a5-prefix-sum-function (sequence)
  (let* ((cutoff
          (putnam-1994-a5-nth-term 0 'globals))
         (code
          (putnam-1994-a5-nth-term 1 'globals))
         (precision
          (putnam-1994-a5-nth-term 2 'globals))
         (digit
          (putnam-1994-a5-digit-term
           code cutoff 'position))
         (value
          (putnam-1994-a5-component-term
           sequence 0 digit precision)))
    (list
     'lambda
     '(globals position)
     (list
      'if
      (list '< digit cutoff)
      value
      (putnam-1994-a5-quoted 0)))))

(defun putnam-1994-a5-prefix-certificate-function
    (sequence)
  (let* ((cutoff
          (putnam-1994-a5-nth-term 0 'globals))
         (tail-bound
          (putnam-1994-a5-nth-term 1 'globals))
         (precision
          (putnam-1994-a5-nth-term 2 'globals))
         (c
          (putnam-1994-a5-nth-term 3 'globals))
         (d
          (putnam-1994-a5-nth-term 4 'globals))
         (position-upper
          (putnam-1994-a5-quoted 1993))
         (prefix-globals
          (putnam-1994-a5-list-term
           (list cutoff 'code)))
         (sum-globals
          (putnam-1994-a5-list-term
           (list cutoff 'code precision)))
         (valid-function
          (putnam-1994-a5-prefix-valid-function))
         (count-function
          (putnam-1994-a5-prefix-count-function))
         (sum-function
          (putnam-1994-a5-prefix-sum-function sequence))
         (valid
          (list
           'always$+
           (putnam-1994-a5-quoted valid-function)
           prefix-globals
           (putnam-1994-a5-range-term
            position-upper)))
         (prefix-count
          (list
           'sum$+
           (putnam-1994-a5-quoted count-function)
           prefix-globals
           (putnam-1994-a5-range-term
            position-upper)))
         (approximate-sum
          (list
           'sum$+
           (putnam-1994-a5-quoted sum-function)
           sum-globals
           (putnam-1994-a5-range-term
            position-upper)))
         (prefix-error
          (putnam-1994-a5-multiply-term
           prefix-count precision))
         (tail-count
          (putnam-1994-a5-subtract-term
           (putnam-1994-a5-quoted 1994)
           prefix-count))
         (tail-error
          (putnam-1994-a5-multiply-term
           tail-count tail-bound))
         (upper
          (putnam-1994-a5-add-term
           (putnam-1994-a5-add-term
            approximate-sum prefix-error)
           tail-error))
         (lower
          (putnam-1994-a5-subtract-term
           approximate-sum prefix-error)))
    (list
     'lambda
     '(globals code)
     (putnam-1994-a5-implies-term
      valid
      (putnam-1994-a5-or-terms
       (list
        (putnam-1994-a5-less-equal-term upper c)
        (putnam-1994-a5-less-equal-term d lower)))))))

(defun putnam-1994-a5-gap-witness-failure-function
    (sequence a b)
  (let* ((c
          (putnam-1994-a5-nth-term 0 'witness))
         (d
          (putnam-1994-a5-nth-term 1 'witness))
         (cutoff
          (putnam-1994-a5-nth-term 2 'witness))
         (tail-bound
          (putnam-1994-a5-nth-term 3 'witness))
         (precision
          (putnam-1994-a5-nth-term 4 'witness))
         (modulus
          (putnam-1994-a5-component-term
           sequence 2
           (putnam-1994-a5-quoted 0)
           tail-bound))
         (base
          (putnam-1994-a5-add-term
           cutoff
           (putnam-1994-a5-quoted 1)))
         (code-upper
          (putnam-1994-a5-subtract-term
           (list
            'expt
            base
            (putnam-1994-a5-quoted 1994))
           (putnam-1994-a5-quoted 1)))
         (certificate-function
          (putnam-1994-a5-prefix-certificate-function
           sequence))
         (certificate-globals
          (putnam-1994-a5-list-term
           (list
            cutoff tail-bound precision c d)))
         (qualification
          (putnam-1994-a5-and-terms
           (list
            (list 'true-listp 'witness)
            (list
             'equal
             (list 'len 'witness)
             (putnam-1994-a5-quoted 5))
            (list 'rationalp c)
            (list 'rationalp d)
            (putnam-1994-a5-less-equal-term
             (putnam-1994-a5-quoted a) c)
            (list '< c d)
            (putnam-1994-a5-less-equal-term
             d
             (putnam-1994-a5-quoted b))
            (list 'natp cutoff)
            (putnam-1994-a5-positive-rational-term
             tail-bound)
            (putnam-1994-a5-positive-rational-term
             precision)
            (list 'natp modulus)
            (putnam-1994-a5-less-equal-term
             modulus cutoff)
            (list
             'always$+
             (putnam-1994-a5-quoted
              certificate-function)
             certificate-globals
             (putnam-1994-a5-range-term
              code-upper))))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-1994-a5-quoted nil)
      (putnam-1994-a5-quoted t)))))

(defun putnam-1994-a5-gap-exists-p (sequence a b)
  (let ((failure-function
         (putnam-1994-a5-gap-witness-failure-function
          sequence a b))
        (true-function
         (putnam-1994-a5-true-function '(witness))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal
       failure-function
       true-function)))))

(defun putnambench-putnam-1994-a5-statement
    (sequence a b)
  (implies
   (and
    (tamep-functionp sequence)
    (fn-equal
     (putnam-1994-a5-cauchy-function sequence)
     (putnam-1994-a5-true-function
      '(n epsilon eta)))
    (fn-equal
     (putnam-1994-a5-positive-function sequence)
     (putnam-1994-a5-true-function
      '(n epsilon)))
    (fn-equal
     (putnam-1994-a5-zero-limit-function sequence)
     (putnam-1994-a5-true-function
      '(epsilon n)))
    (rationalp a)
    (rationalp b)
    (< a b))
   (putnam-1994-a5-gap-exists-p
    sequence a b)))

(value-triple :itpeval-statement-checked)
:q
