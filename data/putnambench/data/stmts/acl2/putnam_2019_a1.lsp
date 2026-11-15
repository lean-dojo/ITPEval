;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_a1:
;; the values of A^3+B^3+C^3-3ABC for nonnegative integers A, B, and C
;; are exactly the nonnegative integers not congruent to 3 or 6 modulo 9.
;; This file contains no proof.

(in-package "ACL2")

;; FN-EQUAL to a constant-true function expresses universal quantification
;; over ACL2 objects. Therefore its negation for the failure function below
;; is exactly the source's internal existential quantifier over A, B, and C.
;; The quoted failure lambda contains only tame ACL2 primitives.

(defun putnam-2019-a1-quoted (object)
  (list 'quote object))

(defun putnam-2019-a1-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2019-a1-and-terms (cdr terms))
            (putnam-2019-a1-quoted nil))
    (putnam-2019-a1-quoted t)))

(defun putnam-2019-a1-true-function (formals)
  (list 'lambda
        formals
        (putnam-2019-a1-quoted t)))

(defun putnam-2019-a1-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2019-a1-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2019-a1-negate-term (value)
  (list 'unary-- value))

(defun putnam-2019-a1-nonnegative-integer-term (value)
  (putnam-2019-a1-and-terms
   (list
    (list 'integerp value)
    (list 'if
          (list '< value (putnam-2019-a1-quoted 0))
          (putnam-2019-a1-quoted nil)
          (putnam-2019-a1-quoted t)))))

(defun putnam-2019-a1-attainment-failure-function (n)
  (let* ((a-cube
          (list 'expt 'a (putnam-2019-a1-quoted 3)))
         (b-cube
          (list 'expt 'b (putnam-2019-a1-quoted 3)))
         (c-cube
          (list 'expt 'c (putnam-2019-a1-quoted 3)))
         (cube-sum
          (putnam-2019-a1-add-term
           a-cube
           (putnam-2019-a1-add-term b-cube c-cube)))
         (triple-product
          (putnam-2019-a1-multiply-term
           (putnam-2019-a1-quoted 3)
           (putnam-2019-a1-multiply-term
            'a
            (putnam-2019-a1-multiply-term 'b 'c))))
         (expression
          (putnam-2019-a1-add-term
           cube-sum
           (putnam-2019-a1-negate-term triple-product)))
         (qualification
          (putnam-2019-a1-and-terms
           (list
            (putnam-2019-a1-nonnegative-integer-term 'a)
            (putnam-2019-a1-nonnegative-integer-term 'b)
            (putnam-2019-a1-nonnegative-integer-term 'c)
            (list 'equal
                  expression
                  (putnam-2019-a1-quoted n))))))
    (list
     'lambda
     '(a b c)
     (list
      'if
      qualification
      (putnam-2019-a1-quoted nil)
      (putnam-2019-a1-quoted t)))))

(defun putnam-2019-a1-attainable-p (n)
  (let ((failure-function
         (putnam-2019-a1-attainment-failure-function n))
        (true-function
         (putnam-2019-a1-true-function '(a b c))))
    (and
     (integerp n)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

(defun putnam-2019-a1-solution-member-p (n)
  (and
   (integerp n)
   (<= 0 n)
   (not (equal (mod n 9) 3))
   (not (equal (mod n 9) 6))))

;; ACL2 universally closes N. This pointwise IFF is the source set equality.
(defun putnambench-putnam-2019-a1-statement (n)
  (implies
   (integerp n)
   (iff
    (putnam-2019-a1-attainable-p n)
    (putnam-2019-a1-solution-member-p n))))

(value-triple :itpeval-statement-checked)
:q
