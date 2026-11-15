;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_a4:
;; a positive integer n admits an n by n integer matrix with even row
;; self-dot-products and odd dot products between distinct rows exactly when
;; n is odd. This file contains no proof.

(in-package "ACL2")

;; A matrix is represented by its row-major list of exactly n^2 integer
;; entries. This is a bijective encoding of Matrix (Fin n) (Fin n) Z.
;; Negated FN-EQUAL retains the matrix as an internal existential witness.
;; The tame row-pair predicate ranges over every ordered pair of row indices;
;; SUM$+ computes the corresponding finite integer dot product exactly.

(defun putnam-2011-a4-quoted (object)
  (list 'quote object))

(defun putnam-2011-a4-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2011-a4-list-term (cdr terms)))
    (putnam-2011-a4-quoted nil)))

(defun putnam-2011-a4-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2011-a4-and-terms (cdr terms))
       (putnam-2011-a4-quoted nil))
    (putnam-2011-a4-quoted t)))

(defun putnam-2011-a4-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2011-a4-multiply-term (left right)
  (list 'binary-* left right))

(defun putnam-2011-a4-range-term (upper)
  (list
   'from-to-by
   (putnam-2011-a4-quoted 0)
   upper
   (putnam-2011-a4-quoted 1)))

(defun putnam-2011-a4-iteration-term (values)
  (list
   'loop$-as
   (putnam-2011-a4-list-term
    (list values))))

(defun putnam-2011-a4-integer-entry-function ()
  '(lambda (globals entry)
     (integerp (car entry))))

(defun putnam-2011-a4-dot-summand-function ()
  (let* ((matrix (list 'car 'globals))
         (n (list 'nth
                  (putnam-2011-a4-quoted 1)
                  'globals))
         (left-row (list 'nth
                         (putnam-2011-a4-quoted 2)
                         'globals))
         (right-row (list 'nth
                          (putnam-2011-a4-quoted 3)
                          'globals))
         (column (list 'car 'entry))
         (left-index
          (putnam-2011-a4-add-term
           (putnam-2011-a4-multiply-term left-row n)
           column))
         (right-index
          (putnam-2011-a4-add-term
           (putnam-2011-a4-multiply-term right-row n)
           column)))
    (list
     'lambda
     '(globals entry)
     (putnam-2011-a4-multiply-term
      (list 'nth left-index matrix)
      (list 'nth right-index matrix)))))

(defun putnam-2011-a4-dot-product-term
    (matrix n left-row right-row)
  (let ((summand-function
         (putnam-2011-a4-dot-summand-function)))
    (list
     'sum$+
     (putnam-2011-a4-quoted summand-function)
     (putnam-2011-a4-list-term
      (list matrix n left-row right-row))
     (putnam-2011-a4-iteration-term
      (putnam-2011-a4-range-term
       (putnam-2011-a4-add-term
        n
        (putnam-2011-a4-quoted -1)))))))

(defun putnam-2011-a4-row-pair-function ()
  (let* ((matrix (list 'car 'globals))
         (n (list 'nth
                  (putnam-2011-a4-quoted 1)
                  'globals))
         (pair-index (list 'car 'entry))
         (left-row (list 'floor pair-index n))
         (right-row (list 'mod pair-index n))
         (dot-product
          (putnam-2011-a4-dot-product-term
           matrix n left-row right-row)))
    (list
     'lambda
     '(globals entry)
     (list
      'if
      (list 'equal left-row right-row)
      (list 'evenp dot-product)
      (list 'oddp dot-product)))))

(defun putnam-2011-a4-witness-failure-function (n)
  (let* ((integer-entry-function
          (putnam-2011-a4-integer-entry-function))
         (row-pair-function
          (putnam-2011-a4-row-pair-function))
         (quoted-n (putnam-2011-a4-quoted n))
         (entry-count
          (putnam-2011-a4-multiply-term quoted-n quoted-n))
         (last-index
          (putnam-2011-a4-add-term
           entry-count
           (putnam-2011-a4-quoted -1)))
         (qualification
          (putnam-2011-a4-and-terms
           (list
            (list 'true-listp 'matrix)
            (list 'equal
                  (list 'len 'matrix)
                  entry-count)
            (list
             'always$+
             (putnam-2011-a4-quoted integer-entry-function)
             (putnam-2011-a4-quoted nil)
             (putnam-2011-a4-iteration-term 'matrix))
            (list
             'always$+
             (putnam-2011-a4-quoted row-pair-function)
             (putnam-2011-a4-list-term
              (list 'matrix quoted-n))
             (putnam-2011-a4-iteration-term
              (putnam-2011-a4-range-term last-index)))))))
    (list
     'lambda
     '(matrix)
     (list
      'if
      qualification
      (putnam-2011-a4-quoted nil)
      (putnam-2011-a4-quoted t)))))

(defun putnam-2011-a4-true-function ()
  '(lambda (matrix) 't))

(defun putnam-2011-a4-matrix-exists-p (n)
  (let* ((integer-entry-function
          (putnam-2011-a4-integer-entry-function))
         (dot-summand-function
          (putnam-2011-a4-dot-summand-function))
         (row-pair-function
          (putnam-2011-a4-row-pair-function))
         (failure-function
          (putnam-2011-a4-witness-failure-function n))
         (true-function
          (putnam-2011-a4-true-function)))
    (and
     (tamep-functionp integer-entry-function)
     (tamep-functionp dot-summand-function)
     (tamep-functionp row-pair-function)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2011-a4-statement (n)
  (implies
   (posp n)
   (iff
    (putnam-2011-a4-matrix-exists-p n)
    (oddp n))))

(value-triple :itpeval-statement-checked)
:q
