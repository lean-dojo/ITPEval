;; Statement-only formalization of Thousand Theorems artifact Q1243340
;; (thousand-theorems__acl2__Q1243340), "Birkhoff–Von Neumann theorem": over
;; any linearly ordered field, the set of finite doubly stochastic matrices is
;; exactly the convex hull of the permutation matrices. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite index type is transported along a bijection to 0,...,n-1.
;; Matrices are exact n-by-n tables, extensionally equivalent to functions on
;; the source finite type. Field carriers and operations are tame APPLY$
;; functions with all ordered-field laws stated below. FN-EQUAL supplies
;; unbounded universal quantification, and inequality with a constant-false
;; function supplies the internal convex weights.
;;
;; The statement's free MATRIX formal supplies the outer universal
;; quantification. Every reified matrix or weight predicate is a
;; primitive-only ACL2 lambda. Its finitely many matrix entries and
;; permutations are unrolled when the function object is constructed. Thus
;; no helper call hidden in a reified lambda can make the statement vacuous.

(defun q1243340-quoted (object)
  (list 'quote object))

(defun q1243340-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1243340-term-list (cdr terms)))
    (q1243340-quoted nil)))

(defun q1243340-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1243340-term-list arguments)))

(defun q1243340-static-apply-term (function arguments)
  (q1243340-apply-term
   (q1243340-quoted function)
   arguments))

(defun q1243340-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1243340-and-terms (cdr terms))
       (q1243340-quoted nil))
    (q1243340-quoted t)))

(defun q1243340-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1243340-quoted t)
       (q1243340-or-terms (cdr terms)))
    (q1243340-quoted nil)))

(defun q1243340-not-term (term)
  (list
   'if
   term
   (q1243340-quoted nil)
   (q1243340-quoted t)))

(defun q1243340-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1243340-quoted t)))

(defun q1243340-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1243340-quoted t)
    (q1243340-quoted nil))
   (list
    'if
    right
    (q1243340-quoted nil)
    (q1243340-quoted t))))

(defun q1243340-nth-term (index tuple)
  (list 'nth (q1243340-quoted index) tuple))

(defun q1243340-true-function (formals)
  (list 'lambda formals (q1243340-quoted t)))

(defun q1243340-false-function (formals)
  (list 'lambda formals (q1243340-quoted nil)))

(defun q1243340-universal-p (function formals)
  (let ((always-true
         (q1243340-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q1243340-member-p (carrier object)
  (if (apply$ carrier (list object))
      t
    nil))

;; Exact first-order laws of a nontrivial linearly ordered field.

(defun q1243340-field-laws-function
    (carrier zero one add multiply negate inverse less)
  (let* ((xy-add
          (q1243340-static-apply-term add '(x y)))
         (yz-add
          (q1243340-static-apply-term add '(y z)))
         (xy-mul
          (q1243340-static-apply-term multiply '(x y)))
         (yz-mul
          (q1243340-static-apply-term multiply '(y z)))
         (neg-x
          (q1243340-static-apply-term negate '(x)))
         (inv-x
          (q1243340-static-apply-term inverse '(x))))
    (list
     'lambda
     '(x y z)
     (q1243340-implies-term
      (q1243340-and-terms
       (list
        (q1243340-static-apply-term carrier '(x))
        (q1243340-static-apply-term carrier '(y))
        (q1243340-static-apply-term carrier '(z))))
      (q1243340-and-terms
       (list
        (q1243340-static-apply-term carrier (list xy-add))
        (q1243340-static-apply-term carrier (list xy-mul))
        (q1243340-static-apply-term carrier (list neg-x))
        (q1243340-static-apply-term carrier (list inv-x))
        (list
         'equal
         (q1243340-static-apply-term add (list xy-add 'z))
         (q1243340-static-apply-term add (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q1243340-static-apply-term add '(y x)))
        (list
         'equal
         (q1243340-static-apply-term
          add
          (list 'x (q1243340-quoted zero)))
         'x)
        (list
         'equal
         (q1243340-static-apply-term add (list 'x neg-x))
         (q1243340-quoted zero))
        (list
         'equal
         (q1243340-static-apply-term multiply (list xy-mul 'z))
         (q1243340-static-apply-term multiply (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (q1243340-static-apply-term multiply '(y x)))
        (list
         'equal
         (q1243340-static-apply-term
          multiply
          (list 'x (q1243340-quoted one)))
         'x)
        (list
         'equal
         (q1243340-static-apply-term multiply (list 'x yz-add))
         (q1243340-static-apply-term
          add
          (list
           (q1243340-static-apply-term multiply '(x y))
           (q1243340-static-apply-term multiply '(x z)))))
        (q1243340-implies-term
         (list 'equal 'x (q1243340-quoted zero))
         (list 'equal inv-x (q1243340-quoted zero)))
        (q1243340-implies-term
         (q1243340-not-term
          (list 'equal 'x (q1243340-quoted zero)))
         (list
          'equal
          (q1243340-static-apply-term multiply (list 'x inv-x))
          (q1243340-quoted one)))
        (q1243340-not-term
         (q1243340-static-apply-term less '(x x)))
        (q1243340-implies-term
         (q1243340-and-terms
          (list
           (q1243340-static-apply-term less '(x y))
           (q1243340-static-apply-term less '(y z))))
         (q1243340-static-apply-term less '(x z)))
        (q1243340-or-terms
         (list
          (q1243340-static-apply-term less '(x y))
          (list 'equal 'x 'y)
          (q1243340-static-apply-term less '(y x))))
        (q1243340-implies-term
         (q1243340-static-apply-term less '(x y))
         (q1243340-static-apply-term
          less
          (list
           (q1243340-static-apply-term add '(x z))
           (q1243340-static-apply-term add '(y z)))))
        (q1243340-implies-term
         (q1243340-and-terms
          (list
           (q1243340-static-apply-term
            less
            (list (q1243340-quoted zero) 'x))
           (q1243340-static-apply-term
            less
            (list (q1243340-quoted zero) 'y))))
         (q1243340-static-apply-term
          less
          (list
           (q1243340-quoted zero)
           xy-mul)))))))))

(defun q1243340-linearly-ordered-field-p
    (carrier zero one add multiply negate inverse less)
  (let ((laws
         (q1243340-field-laws-function
          carrier zero one add multiply negate inverse less)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp multiply)
     (tamep-functionp negate)
     (tamep-functionp inverse)
     (tamep-functionp less)
     (q1243340-member-p carrier zero)
     (q1243340-member-p carrier one)
     (not (equal zero one))
     (tamep-functionp laws)
     (q1243340-universal-p laws '(x y z)))))

;; Finite indices and the complete permutation enumeration.

(defun q1243340-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     start
     (q1243340-range-from (+ 1 start) (- count 1)))))

(defun q1243340-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons
     (cons item (car lists))
     (q1243340-prefix-each item (cdr lists)))))

(defun q1243340-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (q1243340-prefix-each
      (car list)
      (q1243340-insert-everywhere item (cdr list))))))

(defun q1243340-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (q1243340-insert-everywhere item (car lists))
     (q1243340-insert-into-each item (cdr lists)))))

(defun q1243340-permutations (list)
  (if (endp list)
      (list nil)
    (q1243340-insert-into-each
     (car list)
     (q1243340-permutations (cdr list)))))

;; Primitive term generators for typed matrices and field expressions.

(defun q1243340-row-entry-valid-terms
    (carrier row-term columns)
  (if (endp columns)
      nil
    (cons
     (q1243340-static-apply-term
      carrier
      (list (q1243340-nth-term (car columns) row-term)))
     (q1243340-row-entry-valid-terms
      carrier row-term (cdr columns)))))

(defun q1243340-matrix-row-valid-terms
    (carrier n matrix-term rows columns)
  (if (endp rows)
      nil
    (let ((row-term
           (q1243340-nth-term (car rows) matrix-term)))
      (append
       (list
        (list 'true-listp row-term)
        (list
         'equal
         (list 'len row-term)
         (q1243340-quoted n)))
       (q1243340-row-entry-valid-terms
        carrier row-term columns)
       (q1243340-matrix-row-valid-terms
        carrier n matrix-term (cdr rows) columns)))))

(defun q1243340-matrix-valid-term
    (carrier n matrix-term rows columns)
  (q1243340-and-terms
   (append
    (list
     (list 'true-listp matrix-term)
     (list
      'equal
      (list 'len matrix-term)
      (q1243340-quoted n)))
    (q1243340-matrix-row-valid-terms
     carrier n matrix-term rows columns))))

(defun q1243340-field-sum-term (add zero values)
  (if (endp values)
      (q1243340-quoted zero)
    (q1243340-static-apply-term
     add
     (list
      (car values)
      (q1243340-field-sum-term add zero (cdr values))))))

(defun q1243340-row-entry-terms (row-term columns)
  (if (endp columns)
      nil
    (cons
     (q1243340-nth-term (car columns) row-term)
     (q1243340-row-entry-terms row-term (cdr columns)))))

(defun q1243340-row-nonnegative-terms
    (less zero row-term columns)
  (if (endp columns)
      nil
    (cons
     (q1243340-not-term
      (q1243340-static-apply-term
       less
       (list
        (q1243340-nth-term (car columns) row-term)
        (q1243340-quoted zero))))
     (q1243340-row-nonnegative-terms
      less zero row-term (cdr columns)))))

(defun q1243340-matrix-nonnegative-terms
    (less zero matrix-term rows columns)
  (if (endp rows)
      nil
    (append
     (q1243340-row-nonnegative-terms
      less zero
      (q1243340-nth-term (car rows) matrix-term)
      columns)
     (q1243340-matrix-nonnegative-terms
      less zero matrix-term (cdr rows) columns))))

(defun q1243340-row-sum-one-terms
    (add zero one matrix-term rows columns)
  (if (endp rows)
      nil
    (let ((row-term
           (q1243340-nth-term (car rows) matrix-term)))
      (cons
       (list
        'equal
        (q1243340-field-sum-term
         add zero
         (q1243340-row-entry-terms row-term columns))
        (q1243340-quoted one))
       (q1243340-row-sum-one-terms
        add zero one matrix-term (cdr rows) columns)))))

(defun q1243340-column-entry-terms
    (matrix-term rows column)
  (if (endp rows)
      nil
    (cons
     (q1243340-nth-term
      column
      (q1243340-nth-term (car rows) matrix-term))
     (q1243340-column-entry-terms
      matrix-term (cdr rows) column))))

(defun q1243340-column-sum-one-terms
    (add zero one matrix-term rows columns)
  (if (endp columns)
      nil
    (cons
     (list
      'equal
      (q1243340-field-sum-term
       add zero
       (q1243340-column-entry-terms
        matrix-term rows (car columns)))
      (q1243340-quoted one))
     (q1243340-column-sum-one-terms
      add zero one matrix-term rows (cdr columns)))))

(defun q1243340-doubly-stochastic-term
    (add zero one less matrix-term rows columns)
  (q1243340-and-terms
   (append
    (q1243340-matrix-nonnegative-terms
     less zero matrix-term rows columns)
    (q1243340-row-sum-one-terms
     add zero one matrix-term rows columns)
    (q1243340-column-sum-one-terms
     add zero one matrix-term rows columns))))

;; Primitive terms for a convex weighting of every permutation matrix.

(defun q1243340-values-at-indices (tuple indices)
  (if (endp indices)
      nil
    (cons
     (q1243340-nth-term (car indices) tuple)
     (q1243340-values-at-indices tuple (cdr indices)))))

(defun q1243340-weight-entry-valid-terms
    (carrier less zero weights indices)
  (if (endp indices)
      nil
    (let ((weight
           (q1243340-nth-term (car indices) weights)))
      (cons
       (q1243340-static-apply-term carrier (list weight))
       (cons
        (q1243340-not-term
         (q1243340-static-apply-term
          less
          (list weight (q1243340-quoted zero))))
        (q1243340-weight-entry-valid-terms
         carrier less zero weights (cdr indices)))))))

(defun q1243340-weighted-entry-term
    (add multiply zero one weights permutations
     weight-index row column)
  (if (endp permutations)
      (q1243340-quoted zero)
    (q1243340-static-apply-term
     add
     (list
      (q1243340-static-apply-term
       multiply
       (list
        (q1243340-nth-term weight-index weights)
        (q1243340-quoted
         (if (equal column (nth row (car permutations)))
             one
           zero))))
      (q1243340-weighted-entry-term
       add multiply zero one weights
       (cdr permutations) (+ 1 weight-index)
       row column)))))

(defun q1243340-weighted-row-equality-terms
    (add multiply zero one weights permutations matrix-term
     row columns)
  (if (endp columns)
      nil
    (cons
     (list
      'equal
      (q1243340-nth-term
       (car columns)
       (q1243340-nth-term row matrix-term))
      (q1243340-weighted-entry-term
       add multiply zero one weights permutations
       0 row (car columns)))
     (q1243340-weighted-row-equality-terms
      add multiply zero one weights permutations matrix-term
      row (cdr columns)))))

(defun q1243340-weighted-matrix-equality-terms
    (add multiply zero one weights permutations matrix-term
     rows columns)
  (if (endp rows)
      nil
    (append
     (q1243340-weighted-row-equality-terms
      add multiply zero one weights permutations matrix-term
      (car rows) columns)
     (q1243340-weighted-matrix-equality-terms
      add multiply zero one weights permutations matrix-term
      (cdr rows) columns))))

(defun q1243340-convex-witness-template
    (carrier add multiply zero one less
     permutations rows columns matrix-term)
  (let* ((weight-count (len permutations))
         (weight-indices
          (q1243340-range-from 0 weight-count)))
    (list
     'lambda
     '(weights)
     (q1243340-and-terms
      (append
       (list
        (list 'true-listp 'weights)
        (list
         'equal
         (list 'len 'weights)
         (q1243340-quoted weight-count)))
       (q1243340-weight-entry-valid-terms
        carrier less zero 'weights weight-indices)
       (list
        (list
         'equal
         (q1243340-field-sum-term
          add zero
          (q1243340-values-at-indices
           'weights weight-indices))
         (q1243340-quoted one)))
       (q1243340-weighted-matrix-equality-terms
        add multiply zero one 'weights permutations matrix-term
        rows columns))))))

(defun q1243340-matrix-valid-function (carrier n indices)
  (list
   'lambda
   '(matrix)
   (q1243340-matrix-valid-term
    carrier n 'matrix indices indices)))

(defun q1243340-doubly-stochastic-function
    (add zero one less indices)
  (list
   'lambda
   '(matrix)
   (q1243340-doubly-stochastic-term
    add zero one less 'matrix indices indices)))

(defun q1243340-convex-witness-function
    (carrier add multiply zero one less
     permutations indices matrix)
  (q1243340-convex-witness-template
   carrier add multiply zero one less
   permutations indices indices
   (q1243340-quoted matrix)))

(defun q1243340-convex-combination-witness-p
    (carrier add multiply zero one less
     permutations indices matrix weights)
  (let ((witness
         (q1243340-convex-witness-function
          carrier add multiply zero one less
          permutations indices matrix)))
    (and
     (tamep-functionp witness)
     (apply$ witness (list weights)))))

(defun-sk q1243340-convex-combination-p
    (carrier add multiply zero one less
     permutations indices matrix)
  (exists (weights)
    (q1243340-convex-combination-witness-p
     carrier add multiply zero one less
     permutations indices matrix weights)))

;; Pointwise extensional equality of the two sets. ACL2 universally closes
;; the free MATRIX formal of this statement predicate. The only internal
;; quantifier is the existential choice of convex weights.

(defun thousand-theorems-q1243340-birkhoff-von-neumann-statement
    (carrier zero one add multiply negate inverse less n matrix)
  (let* ((indices
          (q1243340-range-from 0 n))
         (permutations
          (q1243340-permutations indices))
         (matrix-valid
          (q1243340-matrix-valid-function carrier n indices))
         (doubly-stochastic
          (q1243340-doubly-stochastic-function
           add zero one less indices)))
    (implies
     (and
      (natp n)
      (q1243340-linearly-ordered-field-p
       carrier zero one add multiply negate inverse less))
     (and
      (tamep-functionp matrix-valid)
      (tamep-functionp doubly-stochastic)
      (implies
       (apply$ matrix-valid (list matrix))
       (iff
        (apply$ doubly-stochastic (list matrix))
        (q1243340-convex-combination-p
         carrier add multiply zero one less
         permutations indices matrix)))))))

;; Non-proof tameness diagnostic. These sample operation objects are chosen
;; only to exercise every generated lambda family.
(value-triple
 (let* ((carrier '(lambda (x) (rationalp x)))
        (add '(lambda (x y) (binary-+ x y)))
        (multiply '(lambda (x y) (binary-* x y)))
        (negate '(lambda (x) (unary-- x)))
        (inverse '(lambda (x) x))
        (less '(lambda (x y) (< x y)))
        (indices-0 (q1243340-range-from 0 0))
        (indices-1 (q1243340-range-from 0 1))
        (indices-2 (q1243340-range-from 0 2))
        (permutations-0 (q1243340-permutations indices-0))
        (permutations-1 (q1243340-permutations indices-1))
        (permutations-2 (q1243340-permutations indices-2))
        (matrix-0 nil)
        (matrix-1 '((1)))
        (matrix-2 '((1 0) (0 1))))
   (list
    :carrier
    (tamep-functionp carrier)
    :add
    (tamep-functionp add)
    :multiply
    (tamep-functionp multiply)
    :negate
    (tamep-functionp negate)
    :inverse
    (tamep-functionp inverse)
    :less
    (tamep-functionp less)
    :field
    (tamep-functionp
     (q1243340-field-laws-function
      carrier 0 1 add multiply negate inverse less))
    :matrix-valid-0
    (tamep-functionp
     (q1243340-matrix-valid-function carrier 0 indices-0))
    :matrix-valid-1
    (tamep-functionp
     (q1243340-matrix-valid-function carrier 1 indices-1))
    :matrix-valid-2
    (tamep-functionp
     (q1243340-matrix-valid-function carrier 2 indices-2))
    :doubly-stochastic-0
    (tamep-functionp
     (q1243340-doubly-stochastic-function
      add 0 1 less indices-0))
    :doubly-stochastic-1
    (tamep-functionp
     (q1243340-doubly-stochastic-function
      add 0 1 less indices-1))
    :doubly-stochastic-2
    (tamep-functionp
     (q1243340-doubly-stochastic-function
      add 0 1 less indices-2))
    :witness-0
    (tamep-functionp
     (q1243340-convex-witness-function
      carrier add multiply 0 1 less
      permutations-0 indices-0 matrix-0))
    :witness-1
    (tamep-functionp
     (q1243340-convex-witness-function
      carrier add multiply 0 1 less
      permutations-1 indices-1 matrix-1))
    :witness-2
    (tamep-functionp
     (q1243340-convex-witness-function
      carrier add multiply 0 1 less
      permutations-2 indices-2 matrix-2)))))

(value-triple :itpeval-statement-checked)
:q
