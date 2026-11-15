;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_a4:
;; the real-coefficient polynomials that map every base-10 repunit to a
;; repunit are exactly the stated family indexed by a natural degree and an
;; integer power of 10. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A coefficient is a rational regular-Cauchy name for an arbitrary real, and
;; a polynomial is its canonical finite coefficient list in ascending degree
;; order. Thus the representation neither restricts coefficients to rationals
;; nor replaces a polynomial by a finite table of sampled values.
;;
;; At each input repunit, a fixed 1/4-accurate polynomial approximation
;; uniquely identifies the only possible integral output. The preservation
;; matrix then checks, at every positive rational precision, exact equality
;; to that integer and checks its decimal digits with the tame ALWAYS$+ scion.
;; This is definitionally equivalent to the source's nested
;; forall-input/exists-output-repunit scope, without externalizing a witness.
;;
;; The solution-family predicate keeps the source's existential natural d and
;; integer c, including c >= 1-d, and checks coefficientwise equality with
;; (10^c*(9*x+1)^d-1)/9 over the represented reals. Every generated quantified
;; lambda contains only tame ACL2 primitives, APPLY$, and tame loop scions.

(defun putnam-2007-a4-quoted (object)
  (list 'quote object))

(defun putnam-2007-a4-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2007-a4-term-list (cdr terms)))
    nil))

(defun putnam-2007-a4-apply-term (function arguments)
  (list 'apply$
        (putnam-2007-a4-quoted function)
        (putnam-2007-a4-term-list arguments)))

(defun putnam-2007-a4-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2007-a4-and-terms (cdr terms))
            (putnam-2007-a4-quoted nil))
    (putnam-2007-a4-quoted t)))

(defun putnam-2007-a4-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2007-a4-quoted t)))

(defun putnam-2007-a4-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2007-a4-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2007-a4-negate-term (value)
  (list 'unary-- value))

(defun putnam-2007-a4-subtract-term (left right)
  (putnam-2007-a4-add-term
   left
   (putnam-2007-a4-negate-term right)))

(defun putnam-2007-a4-divide-term (numerator denominator)
  (putnam-2007-a4-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2007-a4-absolute-term (value)
  (list 'if
        (list '< value (putnam-2007-a4-quoted 0))
        (putnam-2007-a4-negate-term value)
        value))

(defun putnam-2007-a4-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2007-a4-quoted nil)
        (putnam-2007-a4-quoted t)))

(defun putnam-2007-a4-positive-rational-term (value)
  (putnam-2007-a4-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2007-a4-quoted 0) value))))

(defun putnam-2007-a4-true-function (formals)
  (list 'lambda
        formals
        (putnam-2007-a4-quoted t)))

(defun putnam-2007-a4-real-name-cauchy-function (name)
  (let* ((left
          (putnam-2007-a4-apply-term name '(epsilon)))
         (right
          (putnam-2007-a4-apply-term name '(eta)))
         (distance
          (putnam-2007-a4-absolute-term
           (putnam-2007-a4-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2007-a4-implies-term
      (putnam-2007-a4-and-terms
       (list
        (putnam-2007-a4-positive-rational-term 'epsilon)
        (putnam-2007-a4-positive-rational-term 'eta)))
      (putnam-2007-a4-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2007-a4-less-equal-term
         distance
         (putnam-2007-a4-add-term
          'epsilon 'eta))))))))

(defun putnam-2007-a4-real-name-p (name)
  (let ((matrix
         (putnam-2007-a4-real-name-cauchy-function name))
        (always-true
         (putnam-2007-a4-true-function
          '(epsilon eta))))
    (and
     (tamep-functionp name)
     (tamep-functionp matrix)
     (tamep-functionp always-true)
     (fn-equal matrix always-true))))

(defun putnam-2007-a4-real-equal-rational-function
    (name rational)
  (let* ((value
          (putnam-2007-a4-apply-term name '(epsilon)))
         (distance
          (putnam-2007-a4-absolute-term
           (putnam-2007-a4-subtract-term
            value
            (putnam-2007-a4-quoted rational)))))
    (list
     'lambda
     '(epsilon)
     (putnam-2007-a4-implies-term
      (putnam-2007-a4-positive-rational-term 'epsilon)
      (putnam-2007-a4-and-terms
       (list
        (list 'rationalp value)
        (putnam-2007-a4-less-equal-term
         distance 'epsilon)))))))

(defun putnam-2007-a4-real-equal-rational-p
    (name rational)
  (let ((matrix
         (putnam-2007-a4-real-equal-rational-function
          name rational))
        (always-true
         (putnam-2007-a4-true-function '(epsilon))))
    (and
     (rationalp rational)
     (tamep-functionp matrix)
     (tamep-functionp always-true)
     (fn-equal matrix always-true))))

(defun putnam-2007-a4-real-coefficient-list-p
    (polynomial)
  (if (consp polynomial)
      (and
       (putnam-2007-a4-real-name-p (car polynomial))
       (putnam-2007-a4-real-coefficient-list-p
        (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2007-a4-real-polynomial-p (polynomial)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-2007-a4-real-coefficient-list-p polynomial)
   (or
    (equal (len polynomial) 1)
    (not
     (putnam-2007-a4-real-equal-rational-p
      (car (last polynomial))
      0)))))

(defun putnam-2007-a4-rational-zero-list-p (values)
  (if (consp values)
      (and
       (equal (car values) 0)
       (putnam-2007-a4-rational-zero-list-p
        (cdr values)))
    (equal values nil)))

(defun putnam-2007-a4-polynomial-equal-rationals-p
    (polynomial rationals)
  (cond
   ((consp polynomial)
    (and
     (putnam-2007-a4-real-equal-rational-p
      (car polynomial)
      (if (consp rationals)
          (car rationals)
        0))
     (putnam-2007-a4-polynomial-equal-rationals-p
      (cdr polynomial)
      (if (consp rationals)
          (cdr rationals)
        nil))))
   ((consp rationals)
    (putnam-2007-a4-rational-zero-list-p rationals))
   (t
    (and
     (equal polynomial nil)
     (equal rationals nil)))))

(defun putnam-2007-a4-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (cond
   ((or (not (natp n))
        (not (natp k))
        (< n k))
    0)
   ((equal k 0)
    1)
   ((equal n 0)
    0)
   (t
    (+ (putnam-2007-a4-binomial (- n 1) (- k 1))
       (putnam-2007-a4-binomial (- n 1) k)))))

(defun putnam-2007-a4-integer-power-of-ten (c)
  (if (and (integerp c) (< c 0))
      (/ (expt 10 (- c)))
    (expt 10 (nfix c))))

(defun putnam-2007-a4-solution-coefficient (d c i)
  (let ((power-of-ten
         (putnam-2007-a4-integer-power-of-ten c)))
    (if (equal i 0)
        (/ (- power-of-ten 1) 9)
      (* power-of-ten
         (putnam-2007-a4-binomial d i)
         (expt 9 (- i 1))))))

(defun putnam-2007-a4-solution-coefficients-aux
    (d c i remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2007-a4-solution-coefficient d c i)
     (putnam-2007-a4-solution-coefficients-aux
      d c (+ i 1) (- remaining 1)))))

(defun putnam-2007-a4-solution-coefficients (d c)
  (putnam-2007-a4-solution-coefficients-aux
   d c 0 (+ 1 (nfix d))))

(defun-sk putnam-2007-a4-solution-p (polynomial)
  (exists
   (d c)
   (and
    (natp d)
    (integerp c)
    (<= (- 1 d) c)
    (putnam-2007-a4-polynomial-equal-rationals-p
     polynomial
     (putnam-2007-a4-solution-coefficients d c)))))

(defun putnam-2007-a4-repunit-term (index-term)
  (putnam-2007-a4-divide-term
   (putnam-2007-a4-subtract-term
    (list
     'expt
     (putnam-2007-a4-quoted 10)
     (putnam-2007-a4-add-term
      (putnam-2007-a4-quoted 1)
      index-term))
    (putnam-2007-a4-quoted 1))
   (putnam-2007-a4-quoted 9)))

(defun putnam-2007-a4-polynomial-weight-term
    (polynomial value-term)
  (if (consp polynomial)
      (putnam-2007-a4-add-term
       (putnam-2007-a4-quoted 1)
       (putnam-2007-a4-multiply-term
        (putnam-2007-a4-absolute-term value-term)
        (putnam-2007-a4-polynomial-weight-term
         (cdr polynomial) value-term)))
    (putnam-2007-a4-quoted 0)))

(defun putnam-2007-a4-evaluation-precision-term
    (polynomial value-term epsilon-term)
  (let ((weight
         (putnam-2007-a4-polynomial-weight-term
          polynomial value-term)))
    (putnam-2007-a4-divide-term
     epsilon-term
     (list
      'if
      (list '< (putnam-2007-a4-quoted 0) weight)
      weight
      (putnam-2007-a4-quoted 1)))))

(defun putnam-2007-a4-polynomial-approximation-term
    (polynomial value-term precision-term)
  (if (consp polynomial)
      (putnam-2007-a4-add-term
       (putnam-2007-a4-apply-term
        (car polynomial)
        (list precision-term))
       (putnam-2007-a4-multiply-term
        value-term
        (putnam-2007-a4-polynomial-approximation-term
         (cdr polynomial)
         value-term
         precision-term)))
    (putnam-2007-a4-quoted 0)))

(defun putnam-2007-a4-singleton-function ()
  (list
   'lambda
   '(value)
   (putnam-2007-a4-term-list (list 'value))))

(defun putnam-2007-a4-index-tuples-term (last-term)
  (list
   'collect$
   (putnam-2007-a4-quoted
    (putnam-2007-a4-singleton-function))
   (list
    'from-to-by
    (putnam-2007-a4-quoted 0)
    last-term
    (putnam-2007-a4-quoted 1))))

(defun putnam-2007-a4-digit-function ()
  (let* ((candidate
          (list 'car 'globals))
         (exponent
          (list 'car 'exponent-tuple))
         (place
          (list
           'expt
           (putnam-2007-a4-quoted 10)
           exponent))
         (digit
          (list
           'mod
           (list 'floor candidate place)
           (putnam-2007-a4-quoted 10))))
    (list
     'lambda
     '(globals exponent-tuple)
     (list
      'if
      (list '< candidate place)
      (putnam-2007-a4-quoted t)
      (list
       'equal
       digit
       (putnam-2007-a4-quoted 1))))))

(defun putnam-2007-a4-decimal-repunit-term
    (candidate-term)
  (putnam-2007-a4-and-terms
   (list
    (list 'integerp candidate-term)
    (list
     '<
     (putnam-2007-a4-quoted 0)
     candidate-term)
    (list
     'always$+
     (putnam-2007-a4-quoted
      (putnam-2007-a4-digit-function))
     (putnam-2007-a4-term-list
      (list candidate-term))
     (putnam-2007-a4-index-tuples-term
      candidate-term)))))

(defun putnam-2007-a4-preservation-function
    (polynomial)
  (let* ((input-index 'input-index)
         (epsilon 'epsilon)
         (input-value
          (putnam-2007-a4-repunit-term input-index))
         (fixed-precision
          (putnam-2007-a4-evaluation-precision-term
           polynomial
           input-value
           (putnam-2007-a4-quoted 1/4)))
         (fixed-approximation
          (putnam-2007-a4-polynomial-approximation-term
           polynomial
           input-value
           fixed-precision))
         (candidate
          (list
           'floor
           (putnam-2007-a4-add-term
            fixed-approximation
            (putnam-2007-a4-quoted 1/2))
           (putnam-2007-a4-quoted 1)))
         (precision
          (putnam-2007-a4-evaluation-precision-term
           polynomial input-value epsilon))
         (approximation
          (putnam-2007-a4-polynomial-approximation-term
           polynomial input-value precision))
         (distance
          (putnam-2007-a4-absolute-term
           (putnam-2007-a4-subtract-term
            approximation candidate)))
         (qualification
          (putnam-2007-a4-and-terms
           (list
            (list 'natp input-index)
            (putnam-2007-a4-positive-rational-term
             epsilon))))
         (conclusion
          (putnam-2007-a4-and-terms
           (list
            (list 'rationalp fixed-approximation)
            (putnam-2007-a4-decimal-repunit-term
             candidate)
            (list 'rationalp approximation)
            (putnam-2007-a4-less-equal-term
             distance epsilon)))))
    (list
     'lambda
     '(input-index epsilon)
     (putnam-2007-a4-implies-term
      qualification conclusion))))

(defun putnam-2007-a4-preserves-repunits-p
    (polynomial)
  (let ((matrix
         (putnam-2007-a4-preservation-function
          polynomial))
        (always-true
         (putnam-2007-a4-true-function
          '(input-index epsilon))))
    (and
     (tamep-functionp matrix)
     (tamep-functionp always-true)
     (fn-equal matrix always-true))))

(defun putnambench-putnam-2007-a4-statement
    (polynomial)
  (implies
   (putnam-2007-a4-real-polynomial-p polynomial)
   (iff
    (putnam-2007-a4-preserves-repunits-p polynomial)
    (putnam-2007-a4-solution-p polynomial))))

;; These evaluations ensure that every function object used by FN-EQUAL is
;; actually tame; they assert no theorem and admit no proof or axiom.
(value-triple
 (list
  :itpeval-tame-functions
  (tamep-functionp
   (putnam-2007-a4-real-name-cauchy-function
    '(lambda (epsilon) '0)))
  (tamep-functionp
   (putnam-2007-a4-real-equal-rational-function
    '(lambda (epsilon) '0)
    0))
  (tamep-functionp
   (putnam-2007-a4-digit-function))
  (tamep-functionp
   (putnam-2007-a4-preservation-function
    '((lambda (epsilon) '0))))))

(value-triple :itpeval-statement-checked)
:q
