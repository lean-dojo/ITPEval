;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_a6:
;; determinant equality for intertwined real square matrices with equal
;; characteristic polynomials. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real scalar domain is presented as an arbitrary real closed ordered
;; field.  Real closed fields have the same first-order theory as the reals,
;; and the matrix assertion below is first-order for each positive dimension.
;; Thus this presentation is bidirectionally equivalent to the source
;; statement over R.
;;
;; An n by n matrix is represented exactly by a row-major list of length n^2
;; over the field carrier. The determinant is the full Leibniz sum. Equality
;; of characteristic polynomials is encoded by equality of det(tI-A) and
;; det(tI-B) for every field element t; over an infinite real closed field
;; this is equivalent to coefficient equality. FN-EQUAL also keeps the source
;; universal quantifier over every n by n matrix X internal to the predicate.

(defun putnam-2015-a6-quoted (object)
  (list 'quote object))

(defun putnam-2015-a6-apply1-term (function argument)
  (list
   'apply$
   (putnam-2015-a6-quoted function)
   (list 'cons argument nil)))

(defun putnam-2015-a6-apply2-term (function left right)
  (list
   'apply$
   (putnam-2015-a6-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2015-a6-and-term (terms)
  (if (endp terms)
      (putnam-2015-a6-quoted t)
    (list
     'if
     (car terms)
     (putnam-2015-a6-and-term (cdr terms))
     (putnam-2015-a6-quoted nil))))

(defun putnam-2015-a6-or-term (terms)
  (if (endp terms)
      (putnam-2015-a6-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2015-a6-quoted t)
     (putnam-2015-a6-or-term (cdr terms)))))

(defun putnam-2015-a6-not-term (term)
  (list
   'if
   term
   (putnam-2015-a6-quoted nil)
   (putnam-2015-a6-quoted t)))

(defun putnam-2015-a6-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2015-a6-quoted t)))

(defun putnam-2015-a6-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2015-a6-quoted t)))

(defun putnam-2015-a6-carrier-term (carrier element)
  (putnam-2015-a6-apply1-term carrier element))

(defun putnam-2015-a6-operation-term (operation left right)
  (putnam-2015-a6-apply2-term operation left right))

(defun putnam-2015-a6-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2015-a6-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2015-a6-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2015-a6-quoted
    (putnam-2015-a6-all-coefficients-function
     carrier))
   (putnam-2015-a6-quoted nil)
   coefficients))

(defun putnam-2015-a6-polynomial-term
    (carrier zero coefficients)
  (putnam-2015-a6-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2015-a6-all-coefficients-term
     carrier coefficients)
    (putnam-2015-a6-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2015-a6-quoted 1))
      (putnam-2015-a6-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2015-a6-quoted zero))))))))

(defun putnam-2015-a6-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2015-a6-quoted zero))
         (qone (putnam-2015-a6-quoted one))
         (add-xy
          (putnam-2015-a6-operation-term add x y))
         (add-yz
          (putnam-2015-a6-operation-term add y z))
         (mul-xy
          (putnam-2015-a6-operation-term mul x y))
         (mul-yz
          (putnam-2015-a6-operation-term mul y z))
         (neg-x
          (putnam-2015-a6-apply1-term neg x))
         (inv-x
          (putnam-2015-a6-apply1-term inv x))
         (domain
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term carrier x)
            (putnam-2015-a6-carrier-term carrier y)
            (putnam-2015-a6-carrier-term carrier z))))
         (laws
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term carrier add-xy)
            (putnam-2015-a6-carrier-term carrier mul-xy)
            (putnam-2015-a6-carrier-term carrier neg-x)
            (putnam-2015-a6-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2015-a6-operation-term add add-xy z)
             (putnam-2015-a6-operation-term add x add-yz))
            (list
             'equal
             (putnam-2015-a6-operation-term mul mul-xy z)
             (putnam-2015-a6-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2015-a6-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2015-a6-operation-term mul y x))
            (list
             'equal
             (putnam-2015-a6-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2015-a6-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2015-a6-operation-term mul x qone)
             x)
            (putnam-2015-a6-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2015-a6-implies-term
             (putnam-2015-a6-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2015-a6-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2015-a6-operation-term mul x add-yz)
             (putnam-2015-a6-operation-term
              add
              (putnam-2015-a6-operation-term mul x y)
              (putnam-2015-a6-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2015-a6-implies-term domain laws))))

(defun putnam-2015-a6-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2015-a6-quoted zero))
         (lt-xy
          (putnam-2015-a6-operation-term lt x y))
         (lt-yx
          (putnam-2015-a6-operation-term lt y x))
         (lt-yz
          (putnam-2015-a6-operation-term lt y z))
         (lt-xz
          (putnam-2015-a6-operation-term lt x z))
         (domain
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term carrier x)
            (putnam-2015-a6-carrier-term carrier y)
            (putnam-2015-a6-carrier-term carrier z))))
         (laws
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-not-term
             (putnam-2015-a6-operation-term lt x x))
            (putnam-2015-a6-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2015-a6-implies-term
             (putnam-2015-a6-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2015-a6-implies-term
             lt-xy
             (putnam-2015-a6-operation-term
              lt
              (putnam-2015-a6-operation-term add x z)
              (putnam-2015-a6-operation-term add y z)))
            (putnam-2015-a6-implies-term
             (putnam-2015-a6-and-term
              (list
               (putnam-2015-a6-operation-term lt qzero x)
               (putnam-2015-a6-operation-term lt qzero y)))
             (putnam-2015-a6-operation-term
              lt
              qzero
              (putnam-2015-a6-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2015-a6-implies-term domain laws))))

(defun putnam-2015-a6-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2015-a6-quoted zero))
         (root
          (putnam-2015-a6-apply1-term square-root x))
         (domain
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term carrier x)
            (putnam-2015-a6-not-term
             (putnam-2015-a6-operation-term lt x qzero)))))
         (laws
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term carrier root)
            (putnam-2015-a6-not-term
             (putnam-2015-a6-operation-term lt root qzero))
            (list
             'equal
             (putnam-2015-a6-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2015-a6-implies-term domain laws))))

(defun putnam-2015-a6-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2015-a6-quoted zero))
         (domain
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2015-a6-all-coefficients-term
             carrier rest)
            (putnam-2015-a6-carrier-term carrier x))))
         (empty-law
          (putnam-2015-a6-implies-term
           (putnam-2015-a6-carrier-term carrier x)
           (list
            'equal
            (putnam-2015-a6-operation-term
             evaluate
             (putnam-2015-a6-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2015-a6-operation-term
           add
           coefficient
           (putnam-2015-a6-operation-term
            mul
            x
            (putnam-2015-a6-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2015-a6-implies-term
           domain
           (putnam-2015-a6-and-term
            (list
             (putnam-2015-a6-carrier-term
              carrier
              (putnam-2015-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2015-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2015-a6-and-term
      (list empty-law recursive-law)))))

(defun putnam-2015-a6-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2015-a6-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2015-a6-and-term
           (list
            (putnam-2015-a6-carrier-term carrier root)
            (list
             'equal
             (putnam-2015-a6-operation-term
              evaluate coefficients root)
             (putnam-2015-a6-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2015-a6-implies-term domain laws))))

(defun putnam-2015-a6-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root evaluate)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (tamep-functionp lt)
   (tamep-functionp square-root)
   (tamep-functionp odd-root)
   (tamep-functionp evaluate)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (fn-equal
    (putnam-2015-a6-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-2015-a6-true-function '(x y z)))
   (fn-equal
    (putnam-2015-a6-order-laws-function
     carrier zero add mul lt)
    (putnam-2015-a6-true-function '(x y z)))
   (fn-equal
    (putnam-2015-a6-square-root-laws-function
     carrier zero mul lt square-root)
    (putnam-2015-a6-true-function '(x)))
   (fn-equal
    (putnam-2015-a6-evaluation-laws-function
     carrier zero add mul evaluate)
    (putnam-2015-a6-true-function
     '(coefficient rest x)))
   (fn-equal
    (putnam-2015-a6-odd-root-laws-function
     carrier zero evaluate odd-root)
    (putnam-2015-a6-true-function
     '(coefficients)))))

(defun putnam-2015-a6-carrier-list-p (values carrier)
  (if (endp values)
      (equal values nil)
    (and
     (apply$ carrier (list (car values)))
     (putnam-2015-a6-carrier-list-p
      (cdr values) carrier))))

(defun putnam-2015-a6-matrix-p (matrix n carrier)
  (and
   (natp n)
   (true-listp matrix)
   (equal (len matrix) (* n n))
   (putnam-2015-a6-carrier-list-p matrix carrier)))

(defun putnam-2015-a6-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2015-a6-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2015-a6-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2015-a6-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2015-a6-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2015-a6-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons
     (cons item (car lists))
     (putnam-2015-a6-prefix-each item (cdr lists)))))

(defun putnam-2015-a6-insert-everywhere (item values)
  (if (endp values)
      (list (list item))
    (cons
     (cons item values)
     (putnam-2015-a6-prefix-each
      (car values)
      (putnam-2015-a6-insert-everywhere
       item (cdr values))))))

(defun putnam-2015-a6-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2015-a6-insert-everywhere item (car lists))
     (putnam-2015-a6-insert-into-each item (cdr lists)))))

(defun putnam-2015-a6-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-2015-a6-insert-into-each
     (car values)
     (putnam-2015-a6-permutations (cdr values)))))

(defun putnam-2015-a6-count-greater (item values)
  (if (endp values)
      0
    (+ (if (> item (car values)) 1 0)
       (putnam-2015-a6-count-greater item (cdr values)))))

(defun putnam-2015-a6-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-2015-a6-count-greater
        (car permutation) (cdr permutation))
       (putnam-2015-a6-inversion-count
        (cdr permutation)))))

(defun putnam-2015-a6-nth-term (index sequence)
  (list
   'nth
   (putnam-2015-a6-quoted index)
   sequence))

(defun putnam-2015-a6-matrix-value-terms
    (sequence index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2015-a6-nth-term index sequence)
     (putnam-2015-a6-matrix-value-terms
      sequence (+ index 1) (- remaining 1)))))

(defun putnam-2015-a6-matrix-entry-domain-terms
    (matrix carrier index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2015-a6-carrier-term
      carrier
      (putnam-2015-a6-nth-term index matrix))
     (putnam-2015-a6-matrix-entry-domain-terms
      matrix carrier (+ index 1) (- remaining 1)))))

(defun putnam-2015-a6-matrix-domain-term
    (matrix n carrier)
  (putnam-2015-a6-and-term
   (cons
    (list 'true-listp matrix)
    (cons
     (list
      'equal
      (list 'len matrix)
      (putnam-2015-a6-quoted (* n n)))
     (putnam-2015-a6-matrix-entry-domain-terms
      matrix carrier 0 (* n n))))))

(defun putnam-2015-a6-diagonal-product-term
    (matrix n permutation row one mul)
  (if (endp permutation)
      (putnam-2015-a6-quoted one)
    (putnam-2015-a6-operation-term
     mul
     (nth (+ (* row n) (car permutation)) matrix)
     (putnam-2015-a6-diagonal-product-term
      matrix n (cdr permutation) (+ row 1) one mul))))

(defun putnam-2015-a6-determinant-sum-term
    (matrix n permutations zero one add mul neg)
  (if (endp permutations)
      (putnam-2015-a6-quoted zero)
    (let* ((permutation (car permutations))
           (product
            (putnam-2015-a6-diagonal-product-term
             matrix n permutation 0 one mul))
           (signed-product
            (if (evenp
                 (putnam-2015-a6-inversion-count permutation))
                product
              (putnam-2015-a6-apply1-term neg product))))
      (putnam-2015-a6-operation-term
       add
       signed-product
       (putnam-2015-a6-determinant-sum-term
        matrix n (cdr permutations)
        zero one add mul neg)))))

(defun putnam-2015-a6-determinant-term
    (matrix n zero one add mul neg)
  (putnam-2015-a6-determinant-sum-term
   matrix
   n
   (putnam-2015-a6-permutations
    (putnam-2015-a6-range-from 0 n))
   zero one add mul neg))

(defun putnam-2015-a6-dot-term
    (left right n row column count remaining zero add mul)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2015-a6-quoted zero)
    (putnam-2015-a6-operation-term
     add
     (putnam-2015-a6-operation-term
      mul
      (nth (+ (* row n) count) left)
      (nth (+ (* count n) column) right))
     (putnam-2015-a6-dot-term
      left right n row column (+ count 1) (- remaining 1)
      zero add mul))))

(defun putnam-2015-a6-matrix-multiply-terms
    (left right n index remaining zero add mul)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let ((row (floor index n))
          (column (mod index n)))
      (cons
       (putnam-2015-a6-dot-term
        left right n row column 0 n zero add mul)
       (putnam-2015-a6-matrix-multiply-terms
        left right n (+ index 1) (- remaining 1)
        zero add mul)))))

(defun putnam-2015-a6-matrix-subtract-terms
    (left right add neg)
  (if (endp left)
      nil
    (cons
     (putnam-2015-a6-operation-term
      add
      (car left)
      (putnam-2015-a6-apply1-term neg (car right)))
     (putnam-2015-a6-matrix-subtract-terms
      (cdr left) (cdr right) add neg))))

(defun putnam-2015-a6-shift-matrix-terms
    (matrix n scalar index remaining add neg)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let* ((row (floor index n))
           (column (mod index n))
           (negative-entry
            (putnam-2015-a6-apply1-term neg (car matrix)))
           (entry
            (if (equal row column)
                (putnam-2015-a6-operation-term
                 add scalar negative-entry)
              negative-entry)))
      (cons
       entry
       (putnam-2015-a6-shift-matrix-terms
        (cdr matrix) n scalar (+ index 1) (- remaining 1)
        add neg)))))

(defun putnam-2015-a6-charpoly-term
    (matrix n scalar zero one add mul neg)
  (putnam-2015-a6-determinant-term
   (putnam-2015-a6-shift-matrix-terms
    matrix n scalar 0 (* n n) add neg)
   n zero one add mul neg))

(defun putnam-2015-a6-diagonal-product
    (matrix n permutation row one mul)
  (if (endp permutation)
      one
    (putnam-2015-a6-mul
     mul
     (nth (+ (* row n) (car permutation)) matrix)
     (putnam-2015-a6-diagonal-product
      matrix n (cdr permutation) (+ row 1) one mul))))

(defun putnam-2015-a6-determinant-sum
    (matrix n permutations zero one add mul neg)
  (if (endp permutations)
      zero
    (let* ((permutation (car permutations))
           (product
            (putnam-2015-a6-diagonal-product
             matrix n permutation 0 one mul))
           (signed-product
            (if (evenp
                 (putnam-2015-a6-inversion-count permutation))
                product
              (putnam-2015-a6-neg neg product))))
      (putnam-2015-a6-add
       add
       signed-product
       (putnam-2015-a6-determinant-sum
        matrix n (cdr permutations)
        zero one add mul neg)))))

(defun putnam-2015-a6-determinant
    (matrix n zero one add mul neg)
  (putnam-2015-a6-determinant-sum
   matrix
   n
   (putnam-2015-a6-permutations
    (putnam-2015-a6-range-from 0 n))
   zero one add mul neg))

(defun putnam-2015-a6-dot
    (left right n row column count remaining zero add mul)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      zero
    (putnam-2015-a6-add
     add
     (putnam-2015-a6-mul
      mul
      (nth (+ (* row n) count) left)
     (nth (+ (* count n) column) right))
     (putnam-2015-a6-dot
      left right n row column (+ count 1) (- remaining 1)
      zero add mul))))

(defun putnam-2015-a6-matrix-multiply-entries
    (left right n index remaining zero add mul)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let ((row (floor index n))
          (column (mod index n)))
      (cons
       (putnam-2015-a6-dot
        left right n row column 0 n zero add mul)
       (putnam-2015-a6-matrix-multiply-entries
        left right n (+ index 1) (- remaining 1)
        zero add mul)))))

(defun putnam-2015-a6-matrix-multiply
    (left right n zero add mul)
  (putnam-2015-a6-matrix-multiply-entries
   left right n 0 (* n n) zero add mul))

(defun putnam-2015-a6-matrix-subtract
    (left right add neg)
  (if (endp left)
      nil
    (cons
     (putnam-2015-a6-add
      add (car left) (putnam-2015-a6-neg neg (car right)))
     (putnam-2015-a6-matrix-subtract
      (cdr left) (cdr right) add neg))))

(defun putnam-2015-a6-shift-matrix
    (matrix n scalar index remaining add neg)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let* ((row (floor index n))
           (column (mod index n))
           (negative-entry
            (putnam-2015-a6-neg neg (car matrix)))
           (entry
            (if (equal row column)
                (putnam-2015-a6-add add scalar negative-entry)
              negative-entry)))
      (cons
       entry
       (putnam-2015-a6-shift-matrix
        (cdr matrix) n scalar (+ index 1) (- remaining 1)
        add neg)))))

(defun putnam-2015-a6-charpoly-equality-function
    (a b n carrier zero one add mul neg)
  (let ((a-terms
         (putnam-2015-a6-matrix-value-terms
          (putnam-2015-a6-quoted a) 0 (* n n)))
        (b-terms
         (putnam-2015-a6-matrix-value-terms
          (putnam-2015-a6-quoted b) 0 (* n n))))
    (list
     'lambda
     '(scalar)
     (putnam-2015-a6-implies-term
      (putnam-2015-a6-carrier-term carrier 'scalar)
      (list
       'equal
       (putnam-2015-a6-charpoly-term
        a-terms n 'scalar zero one add mul neg)
       (putnam-2015-a6-charpoly-term
        b-terms n 'scalar zero one add mul neg))))))

(defun putnam-2015-a6-charpoly-equal-p
    (a b n carrier zero one add mul neg)
  (let ((condition
         (putnam-2015-a6-charpoly-equality-function
          a b n carrier zero one add mul neg))
        (always-true
         (putnam-2015-a6-true-function '(scalar))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnam-2015-a6-conclusion-function
    (a b m n carrier zero one add mul neg)
  (let* ((a-terms
          (putnam-2015-a6-matrix-value-terms
           (putnam-2015-a6-quoted a) 0 (* n n)))
         (b-terms
          (putnam-2015-a6-matrix-value-terms
           (putnam-2015-a6-quoted b) 0 (* n n)))
         (m-terms
          (putnam-2015-a6-matrix-value-terms
           (putnam-2015-a6-quoted m) 0 (* n n)))
         (x-terms
          (putnam-2015-a6-matrix-value-terms
           'x 0 (* n n)))
         (mx-terms
          (putnam-2015-a6-matrix-multiply-terms
           m-terms x-terms n 0 (* n n) zero add mul))
         (xm-terms
          (putnam-2015-a6-matrix-multiply-terms
           x-terms m-terms n 0 (* n n) zero add mul))
         (left-terms
          (putnam-2015-a6-matrix-subtract-terms
           a-terms mx-terms add neg))
         (right-terms
          (putnam-2015-a6-matrix-subtract-terms
           b-terms xm-terms add neg)))
    (list
     'lambda
     '(x)
     (putnam-2015-a6-implies-term
      (putnam-2015-a6-matrix-domain-term
       'x n carrier)
      (list
       'equal
       (putnam-2015-a6-determinant-term
        left-terms n zero one add mul neg)
       (putnam-2015-a6-determinant-term
        right-terms n zero one add mul neg))))))

(defun putnam-2015-a6-all-x-p
    (a b m n carrier zero one add mul neg)
  (let ((condition
         (putnam-2015-a6-conclusion-function
          a b m n carrier zero one add mul neg))
        (always-true
         (putnam-2015-a6-true-function '(x))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun putnambench-putnam-2015-a6-statement
    (n a b m
       carrier zero one add mul neg inv lt
       square-root odd-root evaluate)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-2015-a6-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate)
    (putnam-2015-a6-matrix-p a n carrier)
    (putnam-2015-a6-matrix-p b n carrier)
    (putnam-2015-a6-matrix-p m n carrier)
    (equal
     (putnam-2015-a6-matrix-multiply
      a m n zero add mul)
     (putnam-2015-a6-matrix-multiply
      m b n zero add mul))
    (putnam-2015-a6-charpoly-equal-p
     a b n carrier zero one add mul neg))
   (putnam-2015-a6-all-x-p
    a b m n carrier zero one add mul neg)))

(value-triple :itpeval-statement-checked)
:q
