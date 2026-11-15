;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_a5:
;; existence of square matrices A and B for which ABAB is zero but BABA is
;; nonzero, refuting the proposed implication. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source solution is False, so its equivalence is the negation of the
;; universal implication, namely the existence of a positive dimension and a
;; counterexample pair. An n-by-n matrix is represented exactly by its n^2
;; row-major entries; this is a finite presentation of the source's Fin n
;; matrix, not a restriction to a finite carrier.
;;
;; The target quantifies over rational entries. This is bidirectionally
;; equivalent for this closed existence statement: every rational matrix is a
;; real matrix (and a matrix over a ringType), while the failure already has
;; an integral 3-by-3 instance. NOT/FN-EQUAL supplies the internal existential
;; quantifier, so the dimension and both matrices are not statement parameters.

(defun putnam-1990-a5-quoted (object)
  (list 'quote object))

(defun putnam-1990-a5-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-1990-a5-and-terms (cdr terms))
       (putnam-1990-a5-quoted nil))
    (putnam-1990-a5-quoted t)))

(defun putnam-1990-a5-not-term (term)
  (list
   'if
   term
   (putnam-1990-a5-quoted nil)
   (putnam-1990-a5-quoted t)))

(defun putnam-1990-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-1990-a5-negate-term (value)
  (list 'unary-- value))

(defun putnam-1990-a5-subtract-term (left right)
  (putnam-1990-a5-add-term
   left
   (putnam-1990-a5-negate-term right)))

(defun putnam-1990-a5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-1990-a5-multiply-four-terms (a b c d)
  (putnam-1990-a5-multiply-term
   (putnam-1990-a5-multiply-term
    (putnam-1990-a5-multiply-term a b)
    c)
   d))

(defun putnam-1990-a5-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-1990-a5-list-term (cdr terms)))
    (putnam-1990-a5-quoted nil)))

(defun putnam-1990-a5-range-term (upper)
  (list
   'from-to-by
   (putnam-1990-a5-quoted 0)
   upper
   (putnam-1990-a5-quoted 1)))

(defun putnam-1990-a5-nth-term (index sequence)
  (list 'nth index sequence))

(defun putnam-1990-a5-matrix-entry-term
    (matrix n row column)
  (putnam-1990-a5-nth-term
   (putnam-1990-a5-add-term
    (putnam-1990-a5-multiply-term row n)
    column)
   matrix))

;; The summation index encodes (k,l,m) in base n. The returned summand is
;; first[i,k] * second[k,l] * first[l,m] * second[m,j].
(defun putnam-1990-a5-four-product-summand-function
    (first-is-a)
  (let* ((n
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 0)
           'globals))
         (a
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 1)
           'globals))
         (b
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 2)
           'globals))
         (entry-index
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 3)
           'globals))
         (n-squared
          (putnam-1990-a5-multiply-term n n))
         (i
          (list 'floor entry-index n))
         (j
          (list 'mod entry-index n))
         (k
          (list 'floor 'triple-index n-squared))
         (remainder
          (list 'mod 'triple-index n-squared))
         (l
          (list 'floor remainder n))
         (m
          (list 'mod remainder n))
         (first
          (if first-is-a a b))
         (second
          (if first-is-a b a)))
    (list
     'lambda
     '(globals triple-index)
     (putnam-1990-a5-multiply-four-terms
      (putnam-1990-a5-matrix-entry-term first n i k)
      (putnam-1990-a5-matrix-entry-term second n k l)
      (putnam-1990-a5-matrix-entry-term first n l m)
      (putnam-1990-a5-matrix-entry-term second n m j)))))

(defun putnam-1990-a5-four-product-entry-function
    (first-is-a require-zero)
  (let* ((n
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 0)
           'globals))
         (a
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 1)
           'globals))
         (b
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 2)
           'globals))
         (n-cubed
          (putnam-1990-a5-multiply-term
           (putnam-1990-a5-multiply-term n n)
           n))
         (summand-function
          (putnam-1990-a5-four-product-summand-function
           first-is-a))
         (entry-sum
          (list
           'sum$+
           (putnam-1990-a5-quoted summand-function)
           (putnam-1990-a5-list-term
            (list n a b 'entry-index))
           (putnam-1990-a5-range-term
            (putnam-1990-a5-subtract-term
             n-cubed
             (putnam-1990-a5-quoted 1)))))
         (entry-is-zero
          (list
           'equal
           entry-sum
           (putnam-1990-a5-quoted 0))))
    (list
     'lambda
     '(globals entry-index)
     (if require-zero
         entry-is-zero
       (putnam-1990-a5-not-term entry-is-zero)))))

(defun putnam-1990-a5-rational-function ()
  '(lambda (entry)
     (rationalp entry)))

(defun putnam-1990-a5-counterexample-failure-function ()
  (let* ((n
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 0)
           'witness))
         (a
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 1)
           'witness))
         (b
          (putnam-1990-a5-nth-term
           (putnam-1990-a5-quoted 2)
           'witness))
         (n-squared
          (putnam-1990-a5-multiply-term n n))
         (entry-range
          (putnam-1990-a5-range-term
           (putnam-1990-a5-subtract-term
            n-squared
            (putnam-1990-a5-quoted 1))))
         (matrix-globals
          (putnam-1990-a5-list-term
           (list n a b)))
         (abab-entry-zero-function
          (putnam-1990-a5-four-product-entry-function
           t t))
         (baba-entry-nonzero-function
          (putnam-1990-a5-four-product-entry-function
           nil nil))
         (qualification
          (putnam-1990-a5-and-terms
           (list
            '(true-listp witness)
            '(equal (len witness) '3)
            (list 'natp n)
            (list
             '<
             (putnam-1990-a5-quoted 0)
             n)
            (list 'true-listp a)
            (list 'equal (list 'len a) n-squared)
            (list
             'always$
             (putnam-1990-a5-quoted
              (putnam-1990-a5-rational-function))
             a)
            (list 'true-listp b)
            (list 'equal (list 'len b) n-squared)
            (list
             'always$
             (putnam-1990-a5-quoted
              (putnam-1990-a5-rational-function))
             b)
            (list
             'always$+
             (putnam-1990-a5-quoted
              abab-entry-zero-function)
             matrix-globals
             entry-range)
            (list
             'thereis$+
             (putnam-1990-a5-quoted
              baba-entry-nonzero-function)
             matrix-globals
             entry-range)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-1990-a5-quoted nil)
      (putnam-1990-a5-quoted t)))))

(defun putnam-1990-a5-true-function ()
  '(lambda (witness)
     't))

(defun putnambench-putnam-1990-a5-statement ()
  (let ((failure-function
         (putnam-1990-a5-counterexample-failure-function))
        (true-function
         (putnam-1990-a5-true-function)))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(value-triple :itpeval-statement-checked)
:q
