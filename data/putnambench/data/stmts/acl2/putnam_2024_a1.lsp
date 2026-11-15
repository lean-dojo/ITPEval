;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_a1:
;; the positive integers n admitting positive integers a, b, and c with
;; 2*a^n + 3*b^n = 4*c^n are exactly {1}. This file contains no proof.

(in-package "ACL2")

;; FN-EQUAL supplies universal quantification over ACL2 objects. Its
;; inequality with the constant-true function below is therefore exactly the
;; source's internal existential quantifier over positive natural a, b, and c.

(defun putnam-2024-a1-quoted (object)
  (list 'quote object))

(defun putnam-2024-a1-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2024-a1-and-terms (cdr terms))
            (putnam-2024-a1-quoted nil))
    (putnam-2024-a1-quoted t)))

(defun putnam-2024-a1-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2024-a1-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2024-a1-positive-natural-term (value)
  (putnam-2024-a1-and-terms
   (list
    (list 'natp value)
    (list '< (putnam-2024-a1-quoted 0) value))))

(defun putnam-2024-a1-true-function ()
  (list 'lambda
        '(a b c)
        (putnam-2024-a1-quoted t)))

(defun putnam-2024-a1-witness-failure-function (n)
  (let* ((exponent (putnam-2024-a1-quoted n))
         (a-power (list 'expt 'a exponent))
         (b-power (list 'expt 'b exponent))
         (c-power (list 'expt 'c exponent))
         (left
          (putnam-2024-a1-add-term
           (putnam-2024-a1-multiply-term
            (putnam-2024-a1-quoted 2)
            a-power)
           (putnam-2024-a1-multiply-term
            (putnam-2024-a1-quoted 3)
            b-power)))
         (right
          (putnam-2024-a1-multiply-term
           (putnam-2024-a1-quoted 4)
           c-power))
         (qualification
          (putnam-2024-a1-and-terms
           (list
            (putnam-2024-a1-positive-natural-term 'a)
            (putnam-2024-a1-positive-natural-term 'b)
            (putnam-2024-a1-positive-natural-term 'c)
            (list 'equal left right)))))
    (list
     'lambda
     '(a b c)
     (list
      'if
      qualification
      (putnam-2024-a1-quoted nil)
      (putnam-2024-a1-quoted t)))))

(defun putnam-2024-a1-witness-exists-p (n)
  (let ((failure-function
         (putnam-2024-a1-witness-failure-function n))
        (true-function
         (putnam-2024-a1-true-function)))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

;; ACL2 universally closes N. This pointwise IFF is the source set equality.
(defun putnambench-putnam-2024-a1-statement (n)
  (implies
   (natp n)
   (iff
    (and
     (< 0 n)
     (putnam-2024-a1-witness-exists-p n))
    (equal n 1))))

(value-triple :itpeval-statement-checked)
:q
