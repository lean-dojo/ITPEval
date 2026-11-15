;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_a1:
;; the function n |-> 1 - n is exactly the integer-valued function on the
;; integers satisfying the two given composition identities and f(0) = 1.
;; This file contains no proof.

(in-package "ACL2")

;; F is an ACL2 function object evaluated by APPLY$. This is the repository's
;; statement encoding for the arbitrary source function f : Z -> Z; it does
;; not replace the function by a finite table. FN-EQUAL against the constant
;; true function retains each universal quantifier over all integers.

(defun putnam-1992-a1-quoted (object)
  (list 'quote object))

(defun putnam-1992-a1-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-1992-a1-term-list (cdr terms)))
    nil))

(defun putnam-1992-a1-apply-term (function arguments)
  (list 'apply$
        (putnam-1992-a1-quoted function)
        (putnam-1992-a1-term-list arguments)))

(defun putnam-1992-a1-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-1992-a1-quoted t)))

(defun putnam-1992-a1-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1992-a1-negate-term (value)
  (list 'unary-- value))

(defun putnam-1992-a1-subtract-term (left right)
  (putnam-1992-a1-add-term
   left
   (putnam-1992-a1-negate-term right)))

(defun putnam-1992-a1-true-function ()
  (list 'lambda
        '(n)
        (putnam-1992-a1-quoted t)))

(defun putnam-1992-a1-universal-p (predicate)
  (and
   (tamep-functionp predicate)
   (fn-equal
    predicate
    (putnam-1992-a1-true-function))))

(defun putnam-1992-a1-integer-valued-function (f)
  (let ((value
         (putnam-1992-a1-apply-term f '(n))))
    (list
     'lambda
     '(n)
     (putnam-1992-a1-implies-term
      (list 'integerp 'n)
      (list 'integerp value)))))

(defun putnam-1992-a1-solution-equality-function (f)
  (let ((value
         (putnam-1992-a1-apply-term f '(n)))
        (solution-value
         (putnam-1992-a1-subtract-term
          (putnam-1992-a1-quoted 1)
          'n)))
    (list
     'lambda
     '(n)
     (putnam-1992-a1-implies-term
      (list 'integerp 'n)
      (list 'equal value solution-value)))))

(defun putnam-1992-a1-involution-function (f)
  (let* ((value
          (putnam-1992-a1-apply-term f '(n)))
         (value-of-value
          (putnam-1992-a1-apply-term f (list value))))
    (list
     'lambda
     '(n)
     (putnam-1992-a1-implies-term
      (list 'integerp 'n)
      (list 'equal value-of-value 'n)))))

(defun putnam-1992-a1-shifted-composition-function (f)
  (let* ((n-plus-two
          (putnam-1992-a1-add-term
           'n
           (putnam-1992-a1-quoted 2)))
         (value-at-n-plus-two
          (putnam-1992-a1-apply-term f (list n-plus-two)))
         (shifted-value
          (putnam-1992-a1-add-term
           value-at-n-plus-two
           (putnam-1992-a1-quoted 2)))
         (composed-value
          (putnam-1992-a1-apply-term f (list shifted-value))))
    (list
     'lambda
     '(n)
     (putnam-1992-a1-implies-term
      (list 'integerp 'n)
      (list 'equal composed-value 'n)))))

(defun putnam-1992-a1-integer-valued-p (f)
  (putnam-1992-a1-universal-p
   (putnam-1992-a1-integer-valued-function f)))

(defun putnam-1992-a1-equals-solution-p (f)
  (putnam-1992-a1-universal-p
   (putnam-1992-a1-solution-equality-function f)))

(defun putnam-1992-a1-involution-p (f)
  (putnam-1992-a1-universal-p
   (putnam-1992-a1-involution-function f)))

(defun putnam-1992-a1-shifted-composition-p (f)
  (putnam-1992-a1-universal-p
   (putnam-1992-a1-shifted-composition-function f)))

(defun putnambench-putnam-1992-a1-statement (f)
  (implies
   (and
    (tamep-functionp f)
    (putnam-1992-a1-integer-valued-p f))
   (iff
    (putnam-1992-a1-equals-solution-p f)
    (and
     (putnam-1992-a1-involution-p f)
     (putnam-1992-a1-shifted-composition-p f)
     (equal
      (apply$ f (list 0))
      1)))))

(value-triple :itpeval-statement-checked)
:q
