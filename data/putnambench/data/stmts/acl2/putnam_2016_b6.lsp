;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_b6:
;; the nested real series sum over k >= 1 and n >= 0 of
;; ((-1)^(k-1)/k)/(k*2^n+1) has value 1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Every finite partial sum below is rational.  For fixed K, letting N tend
;; to infinity gives the first K terms of the source outer series.  Therefore
;; the source equality is equivalent to
;;
;;   for every epsilon > 0, eventually in K, eventually in N,
;;   |partial-sum(K,N) - 1| <= epsilon.
;;
;; MODULUS is internally existentially quantified below.  At (EPSILON, 0)
;; its car is the outer cutoff, and at (EPSILON, K) its cdr is the inner
;; cutoff.  The enclosing negated FN-EQUAL keeps this witness internal.

(defun putnam-2016-b6-inner-sum (k term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (+ (putnam-2016-b6-inner-sum
        k (- term-count 1))
       (/ (+ (* k (expt 2 (- term-count 1)))
             1)))))

(defun putnam-2016-b6-partial-sum
    (outer-term-count inner-term-count)
  (declare (xargs :measure (nfix outer-term-count)))
  (if (zp outer-term-count)
      0
    (+ (putnam-2016-b6-partial-sum
        (- outer-term-count 1)
        inner-term-count)
       (* (/ (expt -1 (- outer-term-count 1))
             outer-term-count)
          (putnam-2016-b6-inner-sum
           outer-term-count inner-term-count)))))

(defun putnam-2016-b6-quoted (object)
  (list 'quote object))

(defun putnam-2016-b6-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2016-b6-term-list (cdr terms)))
    nil))

(defun putnam-2016-b6-apply-term (function arguments)
  (list 'apply$
        (putnam-2016-b6-quoted function)
        (putnam-2016-b6-term-list arguments)))

(defun putnam-2016-b6-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2016-b6-and-terms (cdr terms))
            (putnam-2016-b6-quoted nil))
    (putnam-2016-b6-quoted t)))

(defun putnam-2016-b6-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2016-b6-quoted t)))

(defun putnam-2016-b6-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2016-b6-negate-term (value)
  (list 'unary-- value))

(defun putnam-2016-b6-subtract-term (left right)
  (putnam-2016-b6-add-term
   left
   (putnam-2016-b6-negate-term right)))

(defun putnam-2016-b6-absolute-term (value)
  (list 'if
        (list '< value 0)
        (putnam-2016-b6-negate-term value)
        value))

(defun putnam-2016-b6-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2016-b6-quoted nil)
        (putnam-2016-b6-quoted t)))

(defun putnam-2016-b6-positive-rational-term (value)
  (putnam-2016-b6-and-terms
   (list
    (list 'rationalp value)
    (list '< 0 value))))

(defun putnam-2016-b6-true-function (formals)
  (list 'lambda
        formals
        (putnam-2016-b6-quoted t)))

(defun putnam-2016-b6-limit-function (modulus)
  (let* ((outer-data
          (putnam-2016-b6-apply-term
           modulus '(epsilon 0)))
         (inner-data
          (putnam-2016-b6-apply-term
           modulus '(epsilon k)))
         (outer-cutoff
          (list 'car outer-data))
         (inner-cutoff
          (list 'cdr inner-data))
         (partial-sum
          (list 'putnam-2016-b6-partial-sum
                'k 'n))
         (error
          (putnam-2016-b6-absolute-term
           (putnam-2016-b6-subtract-term
            partial-sum 1))))
    (list
     'lambda
     '(epsilon k n)
     (putnam-2016-b6-implies-term
      (putnam-2016-b6-positive-rational-term
       'epsilon)
      (putnam-2016-b6-and-terms
       (list
        (list 'consp outer-data)
        (list 'natp outer-cutoff)
        (putnam-2016-b6-implies-term
         (putnam-2016-b6-and-terms
          (list
           (list 'natp 'k)
           (putnam-2016-b6-less-equal-term
            outer-cutoff 'k)))
         (putnam-2016-b6-and-terms
          (list
           (list 'consp inner-data)
           (list 'natp inner-cutoff)
           (putnam-2016-b6-implies-term
            (putnam-2016-b6-and-terms
             (list
              (list 'natp 'n)
              (putnam-2016-b6-less-equal-term
               inner-cutoff 'n)))
            (putnam-2016-b6-and-terms
             (list
              (list 'rationalp partial-sum)
              (putnam-2016-b6-less-equal-term
               error 'epsilon)))))))))))))

(defun putnam-2016-b6-limit-witness-p (modulus)
  (and
   (tamep-functionp modulus)
   (fn-equal
    (putnam-2016-b6-limit-function modulus)
    (putnam-2016-b6-true-function
     '(epsilon k n)))))

(defun putnam-2016-b6-limit-failure-function ()
  (list
   'lambda
   '(modulus)
   (list
    'if
    (list 'putnam-2016-b6-limit-witness-p
          'modulus)
    (putnam-2016-b6-quoted nil)
    (putnam-2016-b6-quoted t))))

(defun putnambench-putnam-2016-b6-statement ()
  (let ((failure
         (putnam-2016-b6-limit-failure-function))
        (always-true
         (putnam-2016-b6-true-function '(modulus))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(value-triple :itpeval-statement-checked)
:q
