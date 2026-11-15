;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_b6:
;; the alternating real series whose kth coefficient counts odd divisors of k
;; below sqrt(2k) converges to pi^2 / 16. This file contains no proof.

(in-package "ACL2")

;; The terms placed under FN-EQUAL below use only ACL2 primitives and the
;; warranted SUM$+ scion. For positive k and natural j,
;; j < sqrt(2k) is equivalent to j*j < 2*k. Summing the corresponding
;; indicator for j=1,...,k therefore gives exactly the source value A(k).
;; Since the source hypothesis uniquely fixes every A(k) used by the series,
;; eliminating A is definitionally equivalent to retaining that function and
;; its defining hypothesis.
;;
;; Machin's identity
;;
;;   pi = 16*arctan(1/5) - 4*arctan(1/239)
;;
;; and exact rational Taylor prefixes give a Cauchy name for pi^2/16. A direct
;; rearrangement by odd divisors proves convergence of the series, while the
;; alternating Taylor bounds prove convergence of the Machin prefixes.
;; Positive rational tolerances are cofinal in the positive reals, so asking
;; for an existential common cutoff for every such tolerance states equality
;; of the two represented real limits exactly.

(defun putnam-2015-b6-quoted (object)
  (list 'quote object))

(defun putnam-2015-b6-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2015-b6-list-term (cdr terms)))
    (putnam-2015-b6-quoted nil)))

(defun putnam-2015-b6-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2015-b6-and-terms (cdr terms))
            (putnam-2015-b6-quoted nil))
    (putnam-2015-b6-quoted t)))

(defun putnam-2015-b6-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2015-b6-quoted t)))

(defun putnam-2015-b6-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2015-b6-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2015-b6-negate-term (value)
  (list 'unary-- value))

(defun putnam-2015-b6-subtract-term (left right)
  (putnam-2015-b6-add-term
   left
   (putnam-2015-b6-negate-term right)))

(defun putnam-2015-b6-divide-term (numerator denominator)
  (putnam-2015-b6-multiply-term
   numerator
   (list 'unary-/ denominator)))

(defun putnam-2015-b6-absolute-term (value)
  (list 'if
        (list '< value (putnam-2015-b6-quoted 0))
        (putnam-2015-b6-negate-term value)
        value))

(defun putnam-2015-b6-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2015-b6-quoted nil)
        (putnam-2015-b6-quoted t)))

(defun putnam-2015-b6-range-term (lower upper)
  (list
   'from-to-by
   lower
   upper
   (putnam-2015-b6-quoted 1)))

(defun putnam-2015-b6-true-function (formals)
  (list 'lambda
        formals
        (putnam-2015-b6-quoted t)))

(defun putnam-2015-b6-divisor-indicator-function ()
  '(lambda (globals candidate)
     (if (equal (mod candidate '2) '1)
         (if (equal (mod (car globals) candidate) '0)
             (if (< (binary-* candidate candidate)
                    (binary-* '2 (car globals)))
                 '1
               '0)
           '0)
       '0)))

(defun putnam-2015-b6-divisor-count-term (k)
  (list
   'sum$+
   (putnam-2015-b6-quoted
    (putnam-2015-b6-divisor-indicator-function))
   (putnam-2015-b6-list-term (list k))
   (putnam-2015-b6-range-term
    (putnam-2015-b6-quoted 1)
    k)))

(defun putnam-2015-b6-series-summand-function ()
  (let* ((k 'index)
         (sign
          (list
           'if
           (list
            'equal
            (list 'mod k (putnam-2015-b6-quoted 2))
            (putnam-2015-b6-quoted 1))
           (putnam-2015-b6-quoted 1)
           (putnam-2015-b6-quoted -1))))
    (list
     'lambda
     '(globals index)
     (putnam-2015-b6-divide-term
      (putnam-2015-b6-multiply-term
       sign
       (putnam-2015-b6-divisor-count-term k))
      k))))

(defun putnam-2015-b6-series-prefix-term (terms)
  (list
   'sum$+
   (putnam-2015-b6-quoted
    (putnam-2015-b6-series-summand-function))
   (putnam-2015-b6-quoted nil)
   (putnam-2015-b6-range-term
    (putnam-2015-b6-quoted 1)
    terms)))

(defun putnam-2015-b6-arctan-summand-function ()
  (let* ((index 'index)
         (exponent
          (putnam-2015-b6-add-term
           (putnam-2015-b6-multiply-term
            (putnam-2015-b6-quoted 2)
            index)
           (putnam-2015-b6-quoted 1)))
         (sign
          (list
           'if
           (list
            'equal
            (list
             'mod
             index
             (putnam-2015-b6-quoted 2))
            (putnam-2015-b6-quoted 0))
           (putnam-2015-b6-quoted 1)
           (putnam-2015-b6-quoted -1))))
    (list
     'lambda
     '(globals index)
     (putnam-2015-b6-divide-term
      (putnam-2015-b6-multiply-term
       sign
       (list
        'expt
        (list 'car 'globals)
        exponent))
      exponent))))

(defun putnam-2015-b6-arctan-prefix-term (z terms)
  (list
   'sum$+
   (putnam-2015-b6-quoted
    (putnam-2015-b6-arctan-summand-function))
   (putnam-2015-b6-list-term (list z))
   (putnam-2015-b6-range-term
    (putnam-2015-b6-quoted 0)
    (putnam-2015-b6-subtract-term
     terms
     (putnam-2015-b6-quoted 1)))))

(defun putnam-2015-b6-solution-prefix-term (terms)
  (let* ((pi-prefix
          (putnam-2015-b6-subtract-term
           (putnam-2015-b6-multiply-term
            (putnam-2015-b6-quoted 16)
            (putnam-2015-b6-arctan-prefix-term
             (putnam-2015-b6-quoted 1/5)
             terms))
           (putnam-2015-b6-multiply-term
            (putnam-2015-b6-quoted 4)
            (putnam-2015-b6-arctan-prefix-term
             (putnam-2015-b6-quoted 1/239)
             terms)))))
    (putnam-2015-b6-divide-term
     (putnam-2015-b6-multiply-term
      pi-prefix
      pi-prefix)
     (putnam-2015-b6-quoted 16))))

(defun putnam-2015-b6-eventual-function (epsilon cutoff)
  (let* ((series-value
          (putnam-2015-b6-series-prefix-term 'terms))
         (solution-value
          (putnam-2015-b6-solution-prefix-term 'pi-terms))
         (error
          (putnam-2015-b6-absolute-term
           (putnam-2015-b6-subtract-term
            series-value solution-value)))
         (hypothesis
          (putnam-2015-b6-and-terms
           (list
            (list 'natp 'terms)
            (putnam-2015-b6-less-equal-term
             (putnam-2015-b6-quoted cutoff)
             'terms)
            (list 'natp 'pi-terms)
            (putnam-2015-b6-less-equal-term
             (putnam-2015-b6-quoted cutoff)
             'pi-terms)))))
    (list
     'lambda
     '(terms pi-terms)
     (putnam-2015-b6-implies-term
      hypothesis
      (list '< error (putnam-2015-b6-quoted epsilon))))))

(defun putnam-2015-b6-eventually-close-p (epsilon cutoff)
  (let ((divisor-function
         (putnam-2015-b6-divisor-indicator-function))
        (series-function
         (putnam-2015-b6-series-summand-function))
        (arctan-function
         (putnam-2015-b6-arctan-summand-function))
        (eventual-function
         (putnam-2015-b6-eventual-function epsilon cutoff))
        (true-function
         (putnam-2015-b6-true-function '(terms pi-terms))))
    (and
     (tamep-functionp divisor-function)
     (tamep-functionp series-function)
     (tamep-functionp arctan-function)
     (tamep-functionp eventual-function)
     (tamep-functionp true-function)
     (fn-equal eventual-function true-function))))

(defun-sk putnam-2015-b6-common-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2015-b6-eventually-close-p
      epsilon cutoff))))

(defun putnambench-putnam-2015-b6-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-2015-b6-common-cutoff-exists-p
    epsilon)))

(value-triple :itpeval-statement-checked)
:q
