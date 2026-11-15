;; Statement-only formalization of PutnamBench corpus artifact putnam_2002_b5:
;; existence of a natural number that is a three-digit palindrome in at
;; least 2002 distinct natural-number bases. This file contains no proof.

(in-package "ACL2")

;; For b >= 2, write q1 = floor(n/b) and q2 = floor(q1/b). The source digit
;; list has length three exactly when q1 >= b and q2 < b, and then its first
;; and last digits are mod(n,b) and q2. For b = 1, the source definition gives
;; n copies of 1, so it is a three-digit palindrome exactly when n = 3.

(defun putnam-2002-b5-quoted (object)
  (list 'quote object))

(defun putnam-2002-b5-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2002-b5-and-terms (cdr terms))
       (putnam-2002-b5-quoted nil))
    (putnam-2002-b5-quoted t)))

(defun putnam-2002-b5-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2002-b5-quoted t)
       (putnam-2002-b5-or-terms (cdr terms)))
    (putnam-2002-b5-quoted nil)))

(defun putnam-2002-b5-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-2002-b5-quoted nil)
   (putnam-2002-b5-quoted t)))

(defun putnam-2002-b5-palindromic-base-function ()
  (let* ((n (list 'car 'globals))
         (q1
          (list
           'floor
           n
           'b))
         (q2
          (list
           'floor
           q1
           'b))
         (base-one-case
          (putnam-2002-b5-and-terms
           (list
            (list
             'equal
             'b
             (putnam-2002-b5-quoted 1))
            (list
             'equal
             n
             (putnam-2002-b5-quoted 3)))))
         (ordinary-base-case
          (putnam-2002-b5-and-terms
           (list
            (putnam-2002-b5-less-equal-term
             (putnam-2002-b5-quoted 2)
             'b)
            (putnam-2002-b5-less-equal-term
             'b
             q1)
            (list '< q2 'b)
            (list
             'equal
             (list 'mod n 'b)
             q2))))
         (qualification
          (putnam-2002-b5-or-terms
           (list base-one-case ordinary-base-case))))
    (list
     'lambda
     '(globals b)
     (list
      'if
      qualification
      (putnam-2002-b5-quoted 1)
      (putnam-2002-b5-quoted 0)))))

;; No base b > n can satisfy the ordinary-base case: its digit list is [n].
;; Hence this sum is exactly the cardinality of the source set of all natural
;; bases b >= 1, rather than a bounded approximation to that cardinality.
(defun putnam-2002-b5-palindromic-base-count-term (n)
  (list
   'sum$+
   (putnam-2002-b5-quoted
    (putnam-2002-b5-palindromic-base-function))
   (list
    'cons
    n
    (putnam-2002-b5-quoted nil))
   (list
    'from-to-by
    (putnam-2002-b5-quoted 1)
    n
    (putnam-2002-b5-quoted 1))))

;; This function is false exactly at natural witnesses having at least 2002
;; qualifying bases. Negated FN-EQUAL therefore expresses the source's
;; unbounded existential quantifier without making its witness a parameter.
(defun putnam-2002-b5-witness-failure-function ()
  (let ((qualification
         (putnam-2002-b5-and-terms
          (list
           (list 'natp 'n)
           (putnam-2002-b5-less-equal-term
            (putnam-2002-b5-quoted 2002)
            (putnam-2002-b5-palindromic-base-count-term
             'n))))))
    (list
     'lambda
     '(n)
     (list
      'if
      qualification
      (putnam-2002-b5-quoted nil)
      (putnam-2002-b5-quoted t)))))

(defun putnam-2002-b5-true-function ()
  '(lambda (n) 't))

(defun putnambench-putnam-2002-b5-statement ()
  (let ((base-function
         (putnam-2002-b5-palindromic-base-function))
        (failure-function
         (putnam-2002-b5-witness-failure-function))
        (true-function
         (putnam-2002-b5-true-function)))
    (and
     (tamep-functionp base-function)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(value-triple :itpeval-statement-checked)
:q
