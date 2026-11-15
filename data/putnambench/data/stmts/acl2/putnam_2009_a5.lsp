;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_a5:
;; no finite abelian group has product of all element orders equal to
;; 2^2009. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A group of cardinality N is transported along a bijection to the canonical
;; carrier {0,...,N-1}. Its complete Cayley table is represented by the N^2
;; base-N digits of CODE, with entry (X,Y) in position X*N+Y. Every finite
;; group has such a code, and every qualifying code determines an isomorphic
;; finite group.
;;
;; The internal witness also contains an inverse for every element, a power
;; trace and claimed order for every element, and prefix products of those
;; orders. These are certificates only: the primitive-only APPLY$ functions
;; below check all group laws, every trace transition, leastness of every
;; positive order, and the final product. No user-defined predicate occurs in
;; the function compared by FN-EQUAL.

(defun putnam-2009-a5-quoted (object)
  (list 'quote object))

(defun putnam-2009-a5-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2009-a5-list-term (cdr terms)))
    (putnam-2009-a5-quoted nil)))

(defun putnam-2009-a5-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2009-a5-and-terms (cdr terms))
       (putnam-2009-a5-quoted nil))
    (putnam-2009-a5-quoted t)))

(defun putnam-2009-a5-not-term (term)
  (list
   'if
   term
   (putnam-2009-a5-quoted nil)
   (putnam-2009-a5-quoted t)))

(defun putnam-2009-a5-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2009-a5-negate-term (value)
  (list 'unary-- value))

(defun putnam-2009-a5-subtract-term (left right)
  (putnam-2009-a5-add-term
   left
   (putnam-2009-a5-negate-term right)))

(defun putnam-2009-a5-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2009-a5-less-equal-term (left right)
  (list
   'if
   (list '< right left)
   (putnam-2009-a5-quoted nil)
   (putnam-2009-a5-quoted t)))

(defun putnam-2009-a5-nth-term (index values)
  (list 'nth index values))

(defun putnam-2009-a5-range-term (upper)
  (list
   'from-to-by
   (putnam-2009-a5-quoted 0)
   upper
   (putnam-2009-a5-quoted 1)))

(defun putnam-2009-a5-iteration-term (carriers)
  (list
   'loop$-as
   (putnam-2009-a5-list-term carriers)))

(defun putnam-2009-a5-operation-term
    (n code x y)
  (list
   'mod
   (list
    'floor
    code
    (list
     'expt
     n
     (putnam-2009-a5-add-term
      (putnam-2009-a5-multiply-term x n)
      y)))
   n))

(defun putnam-2009-a5-identity-entry-function ()
  (let* ((n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (identity
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 2)
           'globals))
         (x (list 'car 'entry)))
    (list
     'lambda
     '(globals entry)
     (putnam-2009-a5-and-terms
      (list
       (list
        'equal
        (putnam-2009-a5-operation-term
         n code identity x)
        x)
       (list
        'equal
        (putnam-2009-a5-operation-term
         n code x identity)
        x))))))

(defun putnam-2009-a5-commutative-entry-function ()
  (let* ((n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (x (list 'floor 'index n))
         (y (list 'mod 'index n)))
    (list
     'lambda
     '(globals index)
     (list
      'equal
      (putnam-2009-a5-operation-term n code x y)
      (putnam-2009-a5-operation-term n code y x)))))

(defun putnam-2009-a5-associative-entry-function ()
  (let* ((n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (n-squared
          (putnam-2009-a5-multiply-term n n))
         (x (list 'floor 'index n-squared))
         (remainder (list 'mod 'index n-squared))
         (y (list 'floor remainder n))
         (z (list 'mod remainder n)))
    (list
     'lambda
     '(globals index)
     (list
      'equal
      (putnam-2009-a5-operation-term
       n code
       (putnam-2009-a5-operation-term n code x y)
       z)
      (putnam-2009-a5-operation-term
       n code
       x
       (putnam-2009-a5-operation-term n code y z))))))

(defun putnam-2009-a5-inverse-entry-function ()
  (let* ((n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (identity
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 2)
           'globals))
         (x (list 'car 'entry))
         (inverse
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'entry)))
    (list
     'lambda
     '(globals entry)
     (putnam-2009-a5-and-terms
      (list
       (list 'natp inverse)
       (list '< inverse n)
       (list
        'equal
        (putnam-2009-a5-operation-term
         n code x inverse)
        identity)
       (list
        'equal
        (putnam-2009-a5-operation-term
         n code inverse x)
        identity))))))

(defun putnam-2009-a5-power-transition-function ()
  (let* ((n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (identity
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 2)
           'globals))
         (x
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 3)
           'globals))
         (trace
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 4)
           'globals))
         (order
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 5)
           'globals))
         (next-index
          (putnam-2009-a5-add-term
           'index
           (putnam-2009-a5-quoted 1)))
         (current
          (putnam-2009-a5-nth-term
           'index trace))
         (next
          (putnam-2009-a5-nth-term
           next-index trace))
         (leastness
          (list
           'if
           (list '< next-index order)
           (putnam-2009-a5-not-term
            (list 'equal next identity))
           (putnam-2009-a5-quoted t))))
    (list
     'lambda
     '(globals index)
     (putnam-2009-a5-and-terms
      (list
       (list
        'equal
        next
        (putnam-2009-a5-operation-term
         n code current x))
       leastness)))))

(defun putnam-2009-a5-order-entry-function ()
  (let* ((transition-function
          (putnam-2009-a5-power-transition-function))
         (n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (identity
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 2)
           'globals))
         (x (list 'car 'entry))
         (trace
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'entry))
         (order
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 2)
           'entry)))
    (list
     'lambda
     '(globals entry)
     (putnam-2009-a5-and-terms
      (list
       (list 'natp order)
       (list 'posp order)
       (putnam-2009-a5-less-equal-term order n)
       (list 'true-listp trace)
       (list
        'equal
        (list 'len trace)
        (putnam-2009-a5-add-term
         order
         (putnam-2009-a5-quoted 1)))
       (list
        'equal
        (putnam-2009-a5-nth-term
         (putnam-2009-a5-quoted 0)
         trace)
        identity)
       (list
        'equal
        (putnam-2009-a5-nth-term order trace)
        identity)
       (list
        'always$+
        (putnam-2009-a5-quoted transition-function)
        (putnam-2009-a5-list-term
         (list n code identity x trace order))
        (putnam-2009-a5-range-term
         (putnam-2009-a5-subtract-term
          order
          (putnam-2009-a5-quoted 1)))))))))

(defun putnam-2009-a5-product-entry-function ()
  (let* ((orders
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'globals))
         (products
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'globals))
         (next-index
          (putnam-2009-a5-add-term
           'index
           (putnam-2009-a5-quoted 1))))
    (list
     'lambda
     '(globals index)
     (list
      'equal
      (putnam-2009-a5-nth-term
       next-index products)
      (putnam-2009-a5-multiply-term
       (putnam-2009-a5-nth-term
        'index products)
       (putnam-2009-a5-nth-term
        'index orders))))))

(defun putnam-2009-a5-witness-failure-function ()
  (let* ((identity-function
          (putnam-2009-a5-identity-entry-function))
         (commutative-function
          (putnam-2009-a5-commutative-entry-function))
         (associative-function
          (putnam-2009-a5-associative-entry-function))
         (inverse-function
          (putnam-2009-a5-inverse-entry-function))
         (order-function
          (putnam-2009-a5-order-entry-function))
         (product-function
          (putnam-2009-a5-product-entry-function))
         (n
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 0)
           'witness))
         (identity
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 1)
           'witness))
         (code
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 2)
           'witness))
         (inverses
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 3)
           'witness))
         (traces
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 4)
           'witness))
         (orders
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 5)
           'witness))
         (products
          (putnam-2009-a5-nth-term
           (putnam-2009-a5-quoted 6)
           'witness))
         (carrier
          (putnam-2009-a5-range-term
           (putnam-2009-a5-subtract-term
            n
            (putnam-2009-a5-quoted 1))))
         (qualification
          (putnam-2009-a5-and-terms
           (list
            (list 'true-listp 'witness)
            (list
             'equal
             (list 'len 'witness)
             (putnam-2009-a5-quoted 7))
            (list 'posp n)
            (list 'natp identity)
            (list '< identity n)
            (list 'natp code)
            (list
             '<
             code
             (list
              'expt
              n
              (putnam-2009-a5-multiply-term n n)))
            (list 'true-listp inverses)
            (list 'equal (list 'len inverses) n)
            (list 'true-listp traces)
            (list 'equal (list 'len traces) n)
            (list 'true-listp orders)
            (list 'equal (list 'len orders) n)
            (list 'true-listp products)
            (list
             'equal
             (list 'len products)
             (putnam-2009-a5-add-term
              n
              (putnam-2009-a5-quoted 1)))
            (list
             'equal
             (putnam-2009-a5-nth-term
              (putnam-2009-a5-quoted 0)
              products)
             (putnam-2009-a5-quoted 1))
            (list
             'equal
             (putnam-2009-a5-nth-term n products)
             (list
              'expt
              (putnam-2009-a5-quoted 2)
              (putnam-2009-a5-quoted 2009)))
            (list
             'always$+
             (putnam-2009-a5-quoted identity-function)
             (putnam-2009-a5-list-term
              (list n code identity))
             (putnam-2009-a5-iteration-term
              (list carrier)))
            (list
             'always$+
             (putnam-2009-a5-quoted commutative-function)
             (putnam-2009-a5-list-term
              (list n code))
             (putnam-2009-a5-range-term
              (putnam-2009-a5-subtract-term
               (putnam-2009-a5-multiply-term n n)
               (putnam-2009-a5-quoted 1))))
            (list
             'always$+
             (putnam-2009-a5-quoted associative-function)
             (putnam-2009-a5-list-term
              (list n code))
             (putnam-2009-a5-range-term
              (putnam-2009-a5-subtract-term
               (putnam-2009-a5-multiply-term
                (putnam-2009-a5-multiply-term n n)
                n)
               (putnam-2009-a5-quoted 1))))
            (list
             'always$+
             (putnam-2009-a5-quoted inverse-function)
             (putnam-2009-a5-list-term
              (list n code identity))
             (putnam-2009-a5-iteration-term
              (list carrier inverses)))
            (list
             'always$+
             (putnam-2009-a5-quoted order-function)
             (putnam-2009-a5-list-term
              (list n code identity))
             (putnam-2009-a5-iteration-term
              (list carrier traces orders)))
            (list
             'always$+
             (putnam-2009-a5-quoted product-function)
             (putnam-2009-a5-list-term
              (list orders products))
             carrier)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2009-a5-quoted nil)
      (putnam-2009-a5-quoted t)))))

(defun putnam-2009-a5-true-function ()
  '(lambda (witness) 't))

;; A witness qualifies exactly when the primitive-only checker returns NIL.
;; DEFUN-SK then states the source existential explicitly. Transporting a
;; finite abelian group to {0,...,N-1} supplies such a table and certificates;
;; conversely, the checked table and laws construct a finite abelian group.

(defun putnam-2009-a5-finite-abelian-witness-p
    (witness)
  (let ((failure-function
         (putnam-2009-a5-witness-failure-function)))
    (and
     (tamep-functionp failure-function)
     (not
      (apply$ failure-function (list witness))))))

(defun-sk putnam-2009-a5-group-exists-p ()
  (exists
   (witness)
   (putnam-2009-a5-finite-abelian-witness-p
    witness)))

;; The supplied PutnamBench answer is False.
(defun putnam-2009-a5-solution-p ()
  nil)

(defun putnambench-putnam-2009-a5-statement ()
  (let ((identity-function
         (putnam-2009-a5-identity-entry-function))
        (commutative-function
         (putnam-2009-a5-commutative-entry-function))
        (associative-function
         (putnam-2009-a5-associative-entry-function))
        (inverse-function
         (putnam-2009-a5-inverse-entry-function))
        (transition-function
         (putnam-2009-a5-power-transition-function))
        (order-function
         (putnam-2009-a5-order-entry-function))
        (product-function
         (putnam-2009-a5-product-entry-function))
        (failure-function
         (putnam-2009-a5-witness-failure-function))
        (true-function
         (putnam-2009-a5-true-function)))
    (and
     (tamep-functionp identity-function)
     (tamep-functionp commutative-function)
     (tamep-functionp associative-function)
     (tamep-functionp inverse-function)
     (tamep-functionp transition-function)
     (tamep-functionp order-function)
     (tamep-functionp product-function)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (iff
      (putnam-2009-a5-group-exists-p)
      (putnam-2009-a5-solution-p)))))

(value-triple :itpeval-statement-checked)
:q
