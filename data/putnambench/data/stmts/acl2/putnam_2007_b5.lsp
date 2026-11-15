;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_b5:
;; existence of k real polynomials expressing floor(n/k)^k as a polynomial
;; combination of its lower powers for every integer n. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A real coefficient is represented by a tame regular-Cauchy name over the
;; rationals. Finite coefficient lists in ascending degree order therefore
;; represent arbitrary real polynomials, including the zero polynomial.
;;
;; The outer DEFUN-SK keeps the source existential over a list of exactly k
;; polynomials. The identity predicate then universally quantifies every ACL2
;; integer n and every positive rational precision. Its approximation error is
;; divided by the sum of the absolute coefficient multipliers, so requiring
;; distance at most epsilon for every epsilon is exact equality over the
;; represented reals. No finite sampling or rational-coefficient reduction is
;; used.

(defun putnam-2007-b5-quoted (object)
  (list 'quote object))

(defun putnam-2007-b5-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2007-b5-term-list (cdr terms)))
    nil))

(defun putnam-2007-b5-apply-term (function arguments)
  (list 'apply$
        (putnam-2007-b5-quoted function)
        (putnam-2007-b5-term-list arguments)))

(defun putnam-2007-b5-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2007-b5-and-terms (cdr terms))
            (putnam-2007-b5-quoted nil))
    (putnam-2007-b5-quoted t)))

(defun putnam-2007-b5-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2007-b5-quoted t)))

(defun putnam-2007-b5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2007-b5-negate-term (value)
  (list 'unary-- value))

(defun putnam-2007-b5-subtract-term (left right)
  (putnam-2007-b5-add-term
   left
   (putnam-2007-b5-negate-term right)))

(defun putnam-2007-b5-absolute-term (value)
  (list 'if
        (list '< value (putnam-2007-b5-quoted 0))
        (putnam-2007-b5-negate-term value)
        value))

(defun putnam-2007-b5-less-equal-term (left right)
  (list 'if
        (list '< right left)
        (putnam-2007-b5-quoted nil)
        (putnam-2007-b5-quoted t)))

(defun putnam-2007-b5-positive-rational-term (value)
  (putnam-2007-b5-and-terms
   (list
    (list 'rationalp value)
    (list '< (putnam-2007-b5-quoted 0) value))))

(defun putnam-2007-b5-true-function (formals)
  (list 'lambda
        formals
        (putnam-2007-b5-quoted t)))

(defun putnam-2007-b5-real-name-cauchy-function (name)
  (let* ((left
          (putnam-2007-b5-apply-term name '(epsilon)))
         (right
          (putnam-2007-b5-apply-term name '(eta)))
         (distance
          (putnam-2007-b5-absolute-term
           (putnam-2007-b5-subtract-term left right))))
    (list
     'lambda
     '(epsilon eta)
     (putnam-2007-b5-implies-term
      (putnam-2007-b5-and-terms
       (list
        (putnam-2007-b5-positive-rational-term 'epsilon)
        (putnam-2007-b5-positive-rational-term 'eta)))
      (putnam-2007-b5-and-terms
       (list
        (list 'rationalp left)
        (list 'rationalp right)
        (putnam-2007-b5-less-equal-term
         distance
         (putnam-2007-b5-add-term
          'epsilon 'eta))))))))

(defun putnam-2007-b5-real-name-p (name)
  (let ((matrix
         (putnam-2007-b5-real-name-cauchy-function name))
        (always-true
         (putnam-2007-b5-true-function
          '(epsilon eta))))
    (and
     (tamep-functionp name)
     (tamep-functionp matrix)
     (tamep-functionp always-true)
     (fn-equal matrix always-true))))

(defun putnam-2007-b5-real-polynomial-p (polynomial)
  (if (consp polynomial)
      (and
       (putnam-2007-b5-real-name-p (car polynomial))
       (putnam-2007-b5-real-polynomial-p
        (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2007-b5-polynomial-family-p
    (polynomials k)
  (and
   (true-listp polynomials)
   (equal (len polynomials) (nfix k))
   (if (consp polynomials)
       (and
        (putnam-2007-b5-real-polynomial-p
         (car polynomials))
        (putnam-2007-b5-polynomial-family-p
         (cdr polynomials)
         (- (nfix k) 1)))
     (zp k))))

(defun putnam-2007-b5-polynomial-approximation
    (polynomial x precision)
  (if (consp polynomial)
      (+
       (apply$ (car polynomial) (list precision))
       (*
        x
        (putnam-2007-b5-polynomial-approximation
         (cdr polynomial) x precision)))
    0))

(defun putnam-2007-b5-polynomial-weight
    (polynomial x)
  (if (consp polynomial)
      (+
       1
       (*
        (abs x)
        (putnam-2007-b5-polynomial-weight
         (cdr polynomial) x)))
    0))

(defun putnam-2007-b5-family-approximation
    (polynomials n quotient precision index)
  (if (consp polynomials)
      (+
       (*
        (putnam-2007-b5-polynomial-approximation
         (car polynomials) n precision)
        (expt quotient (nfix index)))
       (putnam-2007-b5-family-approximation
        (cdr polynomials)
        n
        quotient
        precision
        (+ 1 (nfix index))))
    0))

(defun putnam-2007-b5-family-weight
    (polynomials n quotient index)
  (if (consp polynomials)
      (+
       (*
        (putnam-2007-b5-polynomial-weight
         (car polynomials) n)
        (abs
         (expt quotient (nfix index))))
       (putnam-2007-b5-family-weight
        (cdr polynomials)
        n
        quotient
        (+ 1 (nfix index))))
    0))

(defun-sk putnam-2007-b5-identity-at-integer-p
    (polynomials k n)
  (forall
   (epsilon)
   (implies
    (and
     (rationalp epsilon)
     (< 0 epsilon))
    (let* ((quotient (floor n k))
           (weight
            (putnam-2007-b5-family-weight
             polynomials n quotient 0))
           (precision
            (/ epsilon
               (if (< 0 weight) weight 1)))
           (approximation
            (putnam-2007-b5-family-approximation
             polynomials n quotient precision 0))
           (target (expt quotient k)))
      (and
       (rationalp approximation)
       (<=
        (abs (- approximation target))
        epsilon))))))

(defun-sk putnam-2007-b5-identity-for-all-integers-p
    (polynomials k)
  (forall
   (n)
   (implies
    (integerp n)
    (putnam-2007-b5-identity-at-integer-p
     polynomials k n))))

(defun-sk putnam-2007-b5-witness-exists-p (k)
  (exists
   (polynomials)
   (and
    (putnam-2007-b5-polynomial-family-p
     polynomials k)
    (putnam-2007-b5-identity-for-all-integers-p
     polynomials k))))

(defun putnambench-putnam-2007-b5-statement (k)
  (implies
   (posp k)
   (putnam-2007-b5-witness-exists-p k)))

;; This evaluation checks the function objects used by the real-name
;; representation; it asserts no theorem and admits no proof or axiom.
(value-triple
 (list
  :itpeval-tame-functions
  (tamep-functionp
   (putnam-2007-b5-real-name-cauchy-function
    '(lambda (epsilon) '0)))))

(value-triple :itpeval-statement-checked)
:q
