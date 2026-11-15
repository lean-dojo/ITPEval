;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_b3:
;; the least positive uniform bound for the minima of |c-d*sqrt(3)| over
;; nonnegative integers c,d with fixed positive sum. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A pair (a,b) denotes a+b*sqrt(3). All coefficients used below are rational.
;; Since sqrt(3) is irrational, its sign is decided exactly by comparing the
;; rational squares a^2 and 3*b^2.

(defun putnam-1988-b3-q3-positive-p (a b)
  (and
   (rationalp a)
   (rationalp b)
   (cond
    ((< b 0)
     (and
      (< 0 a)
      (< (* 3 b b) (* a a))))
    ((< 0 b)
     (or
      (<= 0 a)
      (< (* a a) (* 3 b b))))
    (t
     (< 0 a)))))

(defun putnam-1988-b3-quoted (object)
  (list 'quote object))

(defun putnam-1988-b3-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-1988-b3-and-terms (cdr terms))
       (putnam-1988-b3-quoted nil))
    (putnam-1988-b3-quoted t)))

(defun putnam-1988-b3-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (putnam-1988-b3-quoted t)))

(defun putnam-1988-b3-not-term (term)
  (list
   'if
   term
   (putnam-1988-b3-quoted nil)
   (putnam-1988-b3-quoted t)))

(defun putnam-1988-b3-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1988-b3-negate-term (value)
  (list 'unary-- value))

(defun putnam-1988-b3-subtract-term (left right)
  (putnam-1988-b3-add-term
   left
   (putnam-1988-b3-negate-term right)))

(defun putnam-1988-b3-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1988-b3-square-term (value)
  (putnam-1988-b3-multiply-term value value))

(defun putnam-1988-b3-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-1988-b3-quoted nil)
   (putnam-1988-b3-quoted t)))

;; This generated term is true exactly when a+b*sqrt(3) is nonnegative.
(defun putnam-1988-b3-q3-nonnegative-term (a b)
  (let ((zero
         (putnam-1988-b3-quoted 0))
        (a-square
         (putnam-1988-b3-square-term a))
        (three-b-square
         (putnam-1988-b3-multiply-term
          (putnam-1988-b3-quoted 3)
          (putnam-1988-b3-square-term b))))
    (list
     'if
     (list '< b zero)
     (list
      'if
      (list '< zero a)
      (list '< three-b-square a-square)
      (putnam-1988-b3-quoted nil))
     (list
      'if
      (list '< zero b)
      (list
       'if
       (list '< a zero)
       (list '< a-square three-b-square)
       (putnam-1988-b3-quoted t))
      (putnam-1988-b3-less-equal-term zero a)))))

(defun putnam-1988-b3-positive-integer-term (value)
  (putnam-1988-b3-and-terms
   (list
    (list 'integerp value)
    (putnam-1988-b3-less-equal-term
     (putnam-1988-b3-quoted 1)
     value))))

;; For x=c-d*sqrt(3), |x| <= a+b*sqrt(3) is the conjunction
;; x <= a+b*sqrt(3) and -x <= a+b*sqrt(3).
(defun putnam-1988-b3-absolute-bound-term
    (c d bound-a bound-b)
  (putnam-1988-b3-and-terms
   (list
    (putnam-1988-b3-q3-nonnegative-term
     (putnam-1988-b3-subtract-term bound-a c)
     (putnam-1988-b3-add-term bound-b d))
    (putnam-1988-b3-q3-nonnegative-term
     (putnam-1988-b3-add-term bound-a c)
     (putnam-1988-b3-subtract-term bound-b d)))))

(defun putnam-1988-b3-singleton-term (value)
  (list
   'cons
   value
   (putnam-1988-b3-quoted nil)))

(defun putnam-1988-b3-index-range-term (n)
  (list
   'from-to-by
   (putnam-1988-b3-quoted 0)
   n
   (putnam-1988-b3-quoted 1)))

(defun putnam-1988-b3-finite-exists-term
    (witness-function n)
  (list
   'thereis$+
   (putnam-1988-b3-quoted witness-function)
   (putnam-1988-b3-singleton-term n)
   (putnam-1988-b3-index-range-term n)))

(defun putnam-1988-b3-true-function ()
  (list
   'lambda
   '(n)
   (putnam-1988-b3-quoted t)))

(defun putnam-1988-b3-false-function ()
  (list
   'lambda
   '(n)
   (putnam-1988-b3-quoted nil)))

;; For positive n, FROM-TO-BY enumerates exactly d=0,...,n and c=n-d.
;; THEREIS$+ therefore retains the source's finite existential quantifier
;; without nesting an unbounded FN-EQUAL quantifier inside a generated lambda.
(defun putnam-1988-b3-solution-witness-function ()
  (let* ((n
          (list 'car 'globals))
         (c
          (putnam-1988-b3-subtract-term n 'd)))
    (list
     'lambda
     '(globals d)
     (putnam-1988-b3-absolute-bound-term
      c
      'd
      (putnam-1988-b3-quoted 1/2)
      (putnam-1988-b3-quoted 1/2)))))

(defun putnam-1988-b3-solution-upper-function ()
  (let ((witness-function
         (putnam-1988-b3-solution-witness-function)))
    (list
     'lambda
     '(n)
     (putnam-1988-b3-implies-term
      (putnam-1988-b3-positive-integer-term 'n)
      (putnam-1988-b3-finite-exists-term
       witness-function
       'n)))))

(defun putnam-1988-b3-solution-is-upper-p ()
  (let ((witness-function
         (putnam-1988-b3-solution-witness-function))
        (upper-function
         (putnam-1988-b3-solution-upper-function)))
    (and
     (tamep-functionp witness-function)
     (tamep-functionp upper-function)
     (fn-equal
      upper-function
      (putnam-1988-b3-true-function)))))

;; The source hypothesis uniquely determines r(n) as the finite minimum over
;; d=0,...,n. Thus r(n)>g exactly when no enumerated d has absolute value <=g.
(defun putnam-1988-b3-below-bound-witness-function (g)
  (let* ((n
          (list 'car 'globals))
         (c
          (putnam-1988-b3-subtract-term n 'd)))
    (list
     'lambda
     '(globals d)
     (putnam-1988-b3-absolute-bound-term
      c
      'd
      (putnam-1988-b3-quoted g)
      (putnam-1988-b3-quoted 0)))))

(defun putnam-1988-b3-lower-counterexample-function (g)
  (let ((witness-function
         (putnam-1988-b3-below-bound-witness-function g)))
    (list
     'lambda
     '(n)
     (putnam-1988-b3-and-terms
      (list
       (putnam-1988-b3-positive-integer-term 'n)
       (putnam-1988-b3-not-term
        (putnam-1988-b3-finite-exists-term
         witness-function
         'n)))))))

(defun putnam-1988-b3-lower-counterexample-exists-p (g)
  (let ((witness-function
         (putnam-1988-b3-below-bound-witness-function g))
        (counterexample-function
         (putnam-1988-b3-lower-counterexample-function g)))
    (and
     (tamep-functionp witness-function)
     (tamep-functionp counterexample-function)
     (not
      (fn-equal
       counterexample-function
       (putnam-1988-b3-false-function))))))

;; It is enough, and is equivalent, to test rational lower candidates g.
;; If a real g<(1+sqrt(3))/2 were an upper bound, rational density would give
;; a rational q strictly between g and the proposed least bound; q would also
;; be an upper bound. Conversely, every rational upper bound is a real one.
(defun putnambench-putnam-1988-b3-statement (g)
  (and
   (putnam-1988-b3-q3-positive-p 1/2 1/2)
   (putnam-1988-b3-solution-is-upper-p)
   (implies
    (and
     (rationalp g)
     (< 0 g)
     (putnam-1988-b3-q3-positive-p
      (- 1/2 g)
      1/2))
    (putnam-1988-b3-lower-counterexample-exists-p g))))

(value-triple :itpeval-statement-checked)
:q
