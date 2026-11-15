;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_b3:
;; a power series with coefficients in {0,1} that equals 3/2 at 2/3 has an
;; irrational value at 1/2. This file contains no proof.

(in-package "ACL2")

;; The source function f is definitionally eliminated at its two used
;; arguments. For a binary prefix of length D with partial sums S23 and S12,
;; every infinite extension has its two series values in the exact intervals
;;
;;   [S23, S23 + 3*(2/3)^D]  and  [S12, S12 + 2*(1/2)^D].
;;
;; At depth D, integers 0 through 2^D-1 encode all binary prefixes by their
;; low-order D bits. The generated loop terms below examine every such prefix,
;; with no fixed depth bound. For an integer ratio R, the compatible prefixes
;; form a finitely branching prefix-closed tree. An infinite path is exactly a
;; binary coefficient sequence whose two series values are 3/2 and R.
;; Conversely, if every level is nonempty, finite branching supplies such an
;; infinite path. Thus absence of a counterexample sequence is equivalent to
;; an empty finite level.
;;
;; FN-EQUAL ranges over every natural depth; its negation keeps the empty-level
;; depth witness internal. The only tame function objects below are generated
;; depth and finite-loop predicates, not representations or restrictions of
;; source sequences.

(defun putnam-2017-b3-quoted (object)
  (list 'quote object))

(defun putnam-2017-b3-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2017-b3-list-term (cdr terms)))
    (putnam-2017-b3-quoted nil)))

(defun putnam-2017-b3-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2017-b3-and-terms (cdr terms))
       (putnam-2017-b3-quoted nil))
    (putnam-2017-b3-quoted t)))

(defun putnam-2017-b3-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2017-b3-negate-term (value)
  (list 'unary-- value))

(defun putnam-2017-b3-subtract-term (left right)
  (putnam-2017-b3-add-term
   left
   (putnam-2017-b3-negate-term right)))

(defun putnam-2017-b3-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2017-b3-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-2017-b3-quoted nil)
   (putnam-2017-b3-quoted t)))

(defun putnam-2017-b3-range-term (lower upper)
  (list
   'from-to-by
   lower
   upper
   (putnam-2017-b3-quoted 1)))

(defun putnam-2017-b3-singleton-function ()
  (list
   'lambda
   '(value)
   (list
    'cons
    'value
    (putnam-2017-b3-quoted nil))))

(defun putnam-2017-b3-singleton-range-term (lower upper)
  (list
   'collect$
   (putnam-2017-b3-quoted
    (putnam-2017-b3-singleton-function))
   (putnam-2017-b3-range-term lower upper)))

;; GLOBALS is (PREFIX-CODE BASE), and IVARS is (INDEX). The low-order bit
;; at INDEX is the corresponding coefficient.
(defun putnam-2017-b3-prefix-summand-function ()
  (let* ((code
          (list 'car 'globals))
         (base
          (list 'car (list 'cdr 'globals)))
         (index
          (list 'car 'ivars))
         (bit
          (list
           'mod
           (list
            'floor
            code
            (list
             'expt
             (putnam-2017-b3-quoted 2)
             index))
           (putnam-2017-b3-quoted 2))))
    (list
     'lambda
     '(globals ivars)
     (putnam-2017-b3-multiply-term
      bit
      (list 'expt base index)))))

(defun putnam-2017-b3-prefix-sum-term
    (code base depth)
  (list
   'if
   (list 'zp depth)
   (putnam-2017-b3-quoted 0)
   (list
    'sum$+
    (putnam-2017-b3-quoted
     (putnam-2017-b3-prefix-summand-function))
    (putnam-2017-b3-list-term
     (list code (putnam-2017-b3-quoted base)))
    (putnam-2017-b3-singleton-range-term
     (putnam-2017-b3-quoted 0)
     (putnam-2017-b3-subtract-term
      depth
      (putnam-2017-b3-quoted 1))))))

;; GLOBALS is (TARGET12 DEPTH), and IVARS is (CODE). CODE ranges over every
;; binary prefix at that depth. Both interval tests use exact rational
;; arithmetic.
(defun putnam-2017-b3-compatible-prefix-function ()
  (let* ((target12
          (list 'car 'globals))
         (depth
          (list 'car (list 'cdr 'globals)))
         (code
          (list 'car 'ivars))
         (sum23
          (putnam-2017-b3-prefix-sum-term
           code 2/3 depth))
         (sum12
          (putnam-2017-b3-prefix-sum-term
           code 1/2 depth))
         (tail23
          (putnam-2017-b3-multiply-term
           (putnam-2017-b3-quoted 3)
           (list
            'expt
            (putnam-2017-b3-quoted 2/3)
            depth)))
         (tail12
          (putnam-2017-b3-multiply-term
           (putnam-2017-b3-quoted 2)
           (list
            'expt
            (putnam-2017-b3-quoted 1/2)
            depth))))
    (list
     'lambda
     '(globals ivars)
     (putnam-2017-b3-and-terms
      (list
       (putnam-2017-b3-less-equal-term
        sum23
        (putnam-2017-b3-quoted 3/2))
       (putnam-2017-b3-less-equal-term
        (putnam-2017-b3-quoted 3/2)
        (putnam-2017-b3-add-term sum23 tail23))
       (putnam-2017-b3-less-equal-term
        sum12
        target12)
       (putnam-2017-b3-less-equal-term
        target12
        (putnam-2017-b3-add-term sum12 tail12)))))))

(defun putnam-2017-b3-nonempty-level-term
    (target12 depth)
  (let ((last-code
         (putnam-2017-b3-subtract-term
          (list
           'expt
           (putnam-2017-b3-quoted 2)
           depth)
          (putnam-2017-b3-quoted 1))))
    (list
     'thereis$+
     (putnam-2017-b3-quoted
      (putnam-2017-b3-compatible-prefix-function))
     (putnam-2017-b3-list-term
      (list
       (putnam-2017-b3-quoted target12)
       depth))
     (putnam-2017-b3-singleton-range-term
      (putnam-2017-b3-quoted 0)
      last-code))))

(defun putnam-2017-b3-nonempty-level-function (target12)
  (list
   'lambda
   '(depth)
   (list
    'if
    (list 'natp 'depth)
    (putnam-2017-b3-nonempty-level-term
     target12
     'depth)
    (putnam-2017-b3-quoted t))))

(defun putnam-2017-b3-true-depth-function ()
  '(lambda (depth) 't))

(defun putnam-2017-b3-empty-level-exists-p (target12)
  (let ((singleton
         (putnam-2017-b3-singleton-function))
        (prefix-summand
         (putnam-2017-b3-prefix-summand-function))
        (compatible-prefix
         (putnam-2017-b3-compatible-prefix-function))
        (nonempty-level
         (putnam-2017-b3-nonempty-level-function target12))
        (always-true
         (putnam-2017-b3-true-depth-function)))
    (and
     (rationalp target12)
     (tamep-functionp singleton)
     (tamep-functionp prefix-summand)
     (tamep-functionp compatible-prefix)
     (tamep-functionp nonempty-level)
     (tamep-functionp always-true)
     (not (fn-equal nonempty-level always-true)))))

;; NUMERATOR and DENOMINATOR are universally quantified by the ACL2
;; statement-corpus convention. The finite-tree equivalence above internalizes
;; both the arbitrary source coefficient sequence and the empty-level witness.
(defun putnambench-putnam-2017-b3-statement
    (numerator denominator)
  (implies
   (and
    (integerp numerator)
    (integerp denominator)
    (not (equal denominator 0)))
   (putnam-2017-b3-empty-level-exists-p
    (/ numerator denominator))))

(value-triple :itpeval-statement-checked)
:q
