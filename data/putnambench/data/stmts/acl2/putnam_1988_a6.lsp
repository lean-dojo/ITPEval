;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_a6:
;; an endomorphism of an n-dimensional vector space with n+1 eigenvectors,
;; every n of which are linearly independent, is scalar. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Choosing a basis identifies every n-dimensional space over F with F^n.
;; Under this identification the endomorphism is an n by n matrix. A finite
;; list exactly represents the source's finite eigenvector set. Every n-element
;; subset is obtained by deleting one entry, and it is independent exactly
;; when its determinant is nonzero.
;;
;; For a nonzero vector v, Av is a scalar multiple of v exactly when, at the
;; first nonzero coordinate j, Av equals ((Av)_j / v_j) v. Thus the source's
;; eigenvalue witnesses remain internal. Likewise, a matrix is a scalar
;; multiple of the identity exactly when its off-diagonal entries are zero and
;; all diagonal entries equal its first diagonal entry. These equivalences
;; eliminate both existential scalar quantifiers without exposing witnesses.
;;
;; CARRIER and the field operations are ACL2 function objects. FN-EQUAL
;; against a constant-T lambda expresses the field laws over the entire
;; represented carrier; the carrier is not enumerated or restricted to be
;; finite. This presentation is counterexample-equivalent to the arbitrary
;; source field quantifier. Any failure uses only the finitely many entries of
;; the matrix and eigenvectors, so it descends to their finitely generated
;; subfield, which has a tame effective ACL2 presentation. Conversely, every
;; represented field is a source field.

(defun putnam-1988-a6-quoted (object)
  (list 'quote object))

(defun putnam-1988-a6-apply1-term (function argument)
  (list
   'apply$
   (putnam-1988-a6-quoted function)
   (list 'cons argument nil)))

(defun putnam-1988-a6-apply2-term (function left right)
  (list
   'apply$
   (putnam-1988-a6-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-1988-a6-carrier-term (carrier element)
  (putnam-1988-a6-apply1-term carrier element))

(defun putnam-1988-a6-operation-term
    (operation left right)
  (putnam-1988-a6-apply2-term operation left right))

(defun putnam-1988-a6-and-term (terms)
  (if (endp terms)
      (putnam-1988-a6-quoted t)
    (list
     'if
     (car terms)
     (putnam-1988-a6-and-term (cdr terms))
     (putnam-1988-a6-quoted nil))))

(defun putnam-1988-a6-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-1988-a6-quoted t)))

(defun putnam-1988-a6-true-function (formals)
  (list
   'lambda
   formals
   (putnam-1988-a6-quoted t)))

(defun putnam-1988-a6-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-1988-a6-quoted zero))
         (qone (putnam-1988-a6-quoted one))
         (add-xy
          (putnam-1988-a6-operation-term add x y))
         (add-yz
          (putnam-1988-a6-operation-term add y z))
         (mul-xy
          (putnam-1988-a6-operation-term mul x y))
         (mul-yz
          (putnam-1988-a6-operation-term mul y z))
         (neg-x
          (putnam-1988-a6-apply1-term neg x))
         (inv-x
          (putnam-1988-a6-apply1-term inv x))
         (all-in-carrier
          (putnam-1988-a6-and-term
           (list
            (putnam-1988-a6-carrier-term carrier x)
            (putnam-1988-a6-carrier-term carrier y)
            (putnam-1988-a6-carrier-term carrier z))))
         (laws
          (putnam-1988-a6-and-term
           (list
            (putnam-1988-a6-carrier-term carrier add-xy)
            (putnam-1988-a6-carrier-term carrier mul-xy)
            (putnam-1988-a6-carrier-term carrier neg-x)
            (putnam-1988-a6-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-1988-a6-operation-term add add-xy z)
             (putnam-1988-a6-operation-term add x add-yz))
            (list
             'equal
             (putnam-1988-a6-operation-term mul mul-xy z)
             (putnam-1988-a6-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-1988-a6-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-1988-a6-operation-term mul y x))
            (list
             'equal
             (putnam-1988-a6-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-1988-a6-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-1988-a6-operation-term mul x qone)
             x)
            (putnam-1988-a6-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-1988-a6-implies-term
             (list 'if
                   (list 'equal x qzero)
                   (putnam-1988-a6-quoted nil)
                   (putnam-1988-a6-quoted t))
             (list
              'equal
              (putnam-1988-a6-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-1988-a6-operation-term mul x add-yz)
             (putnam-1988-a6-operation-term
              add
              (putnam-1988-a6-operation-term mul x y)
              (putnam-1988-a6-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-1988-a6-implies-term all-in-carrier laws))))

(defun putnam-1988-a6-field-p
    (carrier zero one add mul neg inv)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp mul)
   (tamep-functionp neg)
   (tamep-functionp inv)
   (apply$ carrier (list zero))
   (apply$ carrier (list one))
   (not (equal zero one))
   (fn-equal
    (putnam-1988-a6-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-1988-a6-true-function '(x y z)))))

(defun putnam-1988-a6-field-add (add x y)
  (apply$ add (list x y)))

(defun putnam-1988-a6-field-mul (mul x y)
  (apply$ mul (list x y)))

(defun putnam-1988-a6-field-neg (neg x)
  (apply$ neg (list x)))

(defun putnam-1988-a6-field-inv (inv x)
  (apply$ inv (list x)))

(defun putnam-1988-a6-vector-p (vector n carrier)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (equal vector nil)
    (and
     (consp vector)
     (apply$ carrier (list (car vector)))
     (putnam-1988-a6-vector-p
      (cdr vector) (- n 1) carrier))))

(defun putnam-1988-a6-matrix-rows-p
    (matrix width remaining carrier)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-1988-a6-vector-p
      (car matrix) width carrier)
     (putnam-1988-a6-matrix-rows-p
      (cdr matrix) width (- remaining 1) carrier))))

(defun putnam-1988-a6-matrix-p (matrix n carrier)
  (putnam-1988-a6-matrix-rows-p
   matrix n n carrier))

(defun putnam-1988-a6-vector-list-p
    (vectors n carrier)
  (if (endp vectors)
      (equal vectors nil)
    (and
     (putnam-1988-a6-vector-p (car vectors) n carrier)
     (putnam-1988-a6-vector-list-p
      (cdr vectors) n carrier))))

(defun putnam-1988-a6-vector-zero-p (vector zero)
  (if (endp vector)
      t
    (and
     (equal (car vector) zero)
     (putnam-1988-a6-vector-zero-p (cdr vector) zero))))

(defun putnam-1988-a6-dot-product
    (left right zero add mul)
  (if (endp left)
      zero
    (putnam-1988-a6-field-add
     add
     (putnam-1988-a6-field-mul
      mul (car left) (car right))
     (putnam-1988-a6-dot-product
      (cdr left) (cdr right) zero add mul))))

(defun putnam-1988-a6-matrix-vector
    (matrix vector zero add mul)
  (if (endp matrix)
      nil
    (cons
     (putnam-1988-a6-dot-product
      (car matrix) vector zero add mul)
     (putnam-1988-a6-matrix-vector
      (cdr matrix) vector zero add mul))))

(defun putnam-1988-a6-first-nonzero-index
    (vector zero)
  (if (endp vector)
      0
    (if (equal (car vector) zero)
        (+ 1
           (putnam-1988-a6-first-nonzero-index
            (cdr vector) zero))
      0)))

(defun putnam-1988-a6-scalar-vector-equal-p
    (image vector scalar mul)
  (if (endp vector)
      (equal image nil)
    (and
     (consp image)
     (equal
      (car image)
      (putnam-1988-a6-field-mul
       mul scalar (car vector)))
     (putnam-1988-a6-scalar-vector-equal-p
      (cdr image) (cdr vector) scalar mul))))

(defun putnam-1988-a6-eigenvector-p
    (matrix vector zero add mul inv)
  (if (putnam-1988-a6-vector-zero-p vector zero)
      nil
    (let* ((image
            (putnam-1988-a6-matrix-vector
             matrix vector zero add mul))
           (index
            (putnam-1988-a6-first-nonzero-index
             vector zero))
           (scalar
            (putnam-1988-a6-field-mul
             mul
             (nth index image)
             (putnam-1988-a6-field-inv
              inv (nth index vector)))))
      (putnam-1988-a6-scalar-vector-equal-p
       image vector scalar mul))))

(defun putnam-1988-a6-all-eigenvectors-p
    (vectors matrix zero add mul inv)
  (if (endp vectors)
      t
    (and
     (putnam-1988-a6-eigenvector-p
      matrix (car vectors) zero add mul inv)
     (putnam-1988-a6-all-eigenvectors-p
      (cdr vectors) matrix zero add mul inv))))

(defun putnam-1988-a6-insert-at
    (value position values)
  (declare (xargs :measure (nfix position)))
  (if (zp position)
      (cons value values)
    (cons
     (car values)
     (putnam-1988-a6-insert-at
      value (- position 1) (cdr values)))))

(defun putnam-1988-a6-insert-everywhere
    (value values position remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-1988-a6-insert-at value position values)
     (putnam-1988-a6-insert-everywhere
      value values (+ position 1) (- remaining 1)))))

(defun putnam-1988-a6-insert-into-permutations
    (value permutations width)
  (if (endp permutations)
      nil
    (append
     (putnam-1988-a6-insert-everywhere
      value (car permutations) 0 width)
     (putnam-1988-a6-insert-into-permutations
      value (cdr permutations) width))))

(defun putnam-1988-a6-permutations (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list nil)
    (putnam-1988-a6-insert-into-permutations
     (- n 1)
     (putnam-1988-a6-permutations (- n 1))
     n)))

(defun putnam-1988-a6-count-smaller (value values)
  (if (endp values)
      0
    (+ (if (< (car values) value) 1 0)
       (putnam-1988-a6-count-smaller
        value (cdr values)))))

(defun putnam-1988-a6-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (putnam-1988-a6-count-smaller
        (car permutation) (cdr permutation))
       (putnam-1988-a6-inversion-count
        (cdr permutation)))))

(defun putnam-1988-a6-permutation-product
    (matrix permutation one mul)
  (if (endp permutation)
      one
    (putnam-1988-a6-field-mul
     mul
     (nth (car permutation) (car matrix))
     (putnam-1988-a6-permutation-product
      (cdr matrix) (cdr permutation) one mul))))

(defun putnam-1988-a6-determinant-sum
    (matrix permutations zero one add mul neg)
  (if (endp permutations)
      zero
    (let* ((permutation (car permutations))
           (product
            (putnam-1988-a6-permutation-product
             matrix permutation one mul))
           (signed-product
            (if (evenp
                 (putnam-1988-a6-inversion-count
                  permutation))
                product
              (putnam-1988-a6-field-neg neg product))))
      (putnam-1988-a6-field-add
       add
       signed-product
       (putnam-1988-a6-determinant-sum
        matrix (cdr permutations)
        zero one add mul neg)))))

(defun putnam-1988-a6-determinant
    (matrix n zero one add mul neg)
  (putnam-1988-a6-determinant-sum
   matrix
   (putnam-1988-a6-permutations n)
   zero one add mul neg))

(defun putnam-1988-a6-remove-nth
    (position values)
  (declare (xargs :measure (nfix position)))
  (if (zp position)
      (cdr values)
    (cons
     (car values)
     (putnam-1988-a6-remove-nth
      (- position 1) (cdr values)))))

(defun putnam-1988-a6-all-deletions-independent-p
    (vectors position remaining n zero one add mul neg)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (not
      (equal
       (putnam-1988-a6-determinant
        (putnam-1988-a6-remove-nth position vectors)
        n zero one add mul neg)
       zero))
     (putnam-1988-a6-all-deletions-independent-p
      vectors (+ position 1) (- remaining 1)
      n zero one add mul neg))))

(defun putnam-1988-a6-scalar-row-p
    (row row-index column-index scalar zero)
  (if (endp row)
      t
    (and
     (equal
      (car row)
      (if (equal row-index column-index)
          scalar
        zero))
     (putnam-1988-a6-scalar-row-p
      (cdr row) row-index (+ column-index 1)
      scalar zero))))

(defun putnam-1988-a6-scalar-matrix-rows-p
    (matrix row-index scalar zero)
  (if (endp matrix)
      t
    (and
     (putnam-1988-a6-scalar-row-p
      (car matrix) row-index 0 scalar zero)
     (putnam-1988-a6-scalar-matrix-rows-p
      (cdr matrix) (+ row-index 1) scalar zero))))

(defun putnam-1988-a6-scalar-matrix-p (matrix zero)
  (putnam-1988-a6-scalar-matrix-rows-p
   matrix 0 (car (car matrix)) zero))

(defun putnambench-putnam-1988-a6-statement
    (n carrier zero one add mul neg inv matrix eigenvectors)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-1988-a6-field-p
     carrier zero one add mul neg inv)
    (putnam-1988-a6-matrix-p matrix n carrier)
    (true-listp eigenvectors)
    (equal (len eigenvectors) (+ n 1))
    (no-duplicatesp-equal eigenvectors)
    (putnam-1988-a6-vector-list-p
     eigenvectors n carrier)
    (putnam-1988-a6-all-eigenvectors-p
     eigenvectors matrix zero add mul inv)
    (putnam-1988-a6-all-deletions-independent-p
     eigenvectors 0 (+ n 1) n
     zero one add mul neg))
   (putnam-1988-a6-scalar-matrix-p matrix zero)))

(value-triple :itpeval-statement-checked)
:q
