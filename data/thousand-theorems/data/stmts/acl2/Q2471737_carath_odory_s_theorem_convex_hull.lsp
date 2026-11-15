;; Statement-only formalization of thousand-theorems corpus artifact Q2471737,
;; "Carathéodory's theorem (convex hull)": the convex hull of a set is the
;; union of the convex hulls of its finite affine-independent subsets. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Relative to an arbitrary basis, every vector over a field is uniquely a
;; finite-support coordinate map. Conversely, finite-support maps over any
;; basis-label carrier form a vector space. Linear equivalences preserve and
;; reflect convex hulls and affine independence, so this presentation is
;; bidirectionally equivalent to the source theorem without imposing finite
;; dimension. A vector is a duplicate-free true list of (label coefficient)
;; pairs, with nonzero coefficients.
;;
;; Convex combinations carry exact finite accumulator certificates. Affine
;; independence carries a finite coordinate minor and a left inverse for that
;; minor. Such a minor exists exactly when the finite family of differences
;; from its first point is linearly independent. Every function object passed
;; to FN-EQUAL contains only ACL2 primitives, fixed LOOP$ scions, and direct
;; APPLY$ calls on quoted tame functions.

(defun q2471737-quoted (object)
  (list 'quote object))

(defun q2471737-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q2471737-term-list (cdr terms)))
    (q2471737-quoted nil)))

(defun q2471737-static-apply-term (function arguments)
  (list 'apply$
        (q2471737-quoted function)
        (q2471737-term-list arguments)))

(defun q2471737-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q2471737-and-terms (cdr terms))
            (q2471737-quoted nil))
    (q2471737-quoted t)))

(defun q2471737-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q2471737-quoted t)
            (q2471737-or-terms (cdr terms)))
    (q2471737-quoted nil)))

(defun q2471737-not-term (term)
  (list 'if term
        (q2471737-quoted nil)
        (q2471737-quoted t)))

(defun q2471737-boolean-term (term)
  (list 'if term
        (q2471737-quoted t)
        (q2471737-quoted nil)))

(defun q2471737-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        (q2471737-boolean-term conclusion)
        (q2471737-quoted t)))

(defun q2471737-iff-term (left right)
  (q2471737-and-terms
   (list
    (q2471737-implies-term left right)
    (q2471737-implies-term right left))))

(defun q2471737-true-function (formals)
  (list 'lambda formals (q2471737-quoted t)))

(defun q2471737-false-function (formals)
  (list 'lambda formals (q2471737-quoted nil)))

(defun q2471737-universal-p (function formals)
  (let ((always-true (q2471737-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q2471737-exists-p (function formals)
  (let ((always-false (q2471737-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun q2471737-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q2471737-range-term (count)
  (list 'from-to-by
        (q2471737-quoted 0)
        (list 'binary-+ count (q2471737-quoted -1))
        (q2471737-quoted 1)))

(defun q2471737-index-tuple-function ()
  (list
   'lambda '(index)
   (list 'cons 'index (q2471737-quoted nil))))

(defun q2471737-index-tuples-term (count)
  (list 'collect$
        (q2471737-quoted
         (q2471737-index-tuple-function))
        (q2471737-range-term count)))

(defun q2471737-nth-term (index values)
  (list 'nth index values))

;; Exact first-order laws of a nontrivial linearly ordered field.

(defun q2471737-field-laws-function
    (carrier zero one add multiply negate inverse less)
  (let* ((xy-add
          (q2471737-static-apply-term add '(x y)))
         (yz-add
          (q2471737-static-apply-term add '(y z)))
         (xy-mul
          (q2471737-static-apply-term multiply '(x y)))
         (yz-mul
          (q2471737-static-apply-term multiply '(y z)))
         (neg-x
          (q2471737-static-apply-term negate '(x)))
         (inv-x
          (q2471737-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (q2471737-implies-term
      (q2471737-and-terms
       (list
        (q2471737-static-apply-term carrier '(x))
        (q2471737-static-apply-term carrier '(y))
        (q2471737-static-apply-term carrier '(z))))
      (q2471737-and-terms
       (list
        (q2471737-static-apply-term carrier (list xy-add))
        (q2471737-static-apply-term carrier (list xy-mul))
        (q2471737-static-apply-term carrier (list neg-x))
        (q2471737-static-apply-term carrier (list inv-x))
        (list 'equal
              (q2471737-static-apply-term add (list xy-add 'z))
              (q2471737-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (q2471737-static-apply-term add '(y x)))
        (list 'equal
              (q2471737-static-apply-term
               add (list 'x (q2471737-quoted zero)))
              'x)
        (list 'equal
              (q2471737-static-apply-term add (list 'x neg-x))
              (q2471737-quoted zero))
        (list 'equal
              (q2471737-static-apply-term multiply (list xy-mul 'z))
              (q2471737-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (q2471737-static-apply-term multiply '(y x)))
        (list 'equal
              (q2471737-static-apply-term
               multiply (list 'x (q2471737-quoted one)))
              'x)
        (list 'equal
              (q2471737-static-apply-term multiply (list 'x yz-add))
              (q2471737-static-apply-term
               add
               (list
                (q2471737-static-apply-term multiply '(x y))
                (q2471737-static-apply-term multiply '(x z)))))
        (q2471737-implies-term
         (list 'equal 'x (q2471737-quoted zero))
         (list 'equal inv-x (q2471737-quoted zero)))
        (q2471737-implies-term
         (q2471737-not-term
          (list 'equal 'x (q2471737-quoted zero)))
         (list 'equal
               (q2471737-static-apply-term
                multiply (list 'x inv-x))
               (q2471737-quoted one)))
        (q2471737-not-term
         (q2471737-static-apply-term less '(x x)))
        (q2471737-implies-term
         (q2471737-and-terms
          (list
           (q2471737-static-apply-term less '(x y))
           (q2471737-static-apply-term less '(y z))))
         (q2471737-static-apply-term less '(x z)))
        (q2471737-or-terms
         (list
          (q2471737-static-apply-term less '(x y))
          (list 'equal 'x 'y)
          (q2471737-static-apply-term less '(y x))))
        (q2471737-implies-term
         (q2471737-static-apply-term less '(x y))
         (q2471737-static-apply-term
          less
          (list
           (q2471737-static-apply-term add '(x z))
           (q2471737-static-apply-term add '(y z)))))
        (q2471737-implies-term
         (q2471737-and-terms
          (list
           (q2471737-static-apply-term
            less (list (q2471737-quoted zero) 'x))
           (q2471737-static-apply-term
            less (list (q2471737-quoted zero) 'y))))
         (q2471737-static-apply-term
          less
          (list
           (q2471737-quoted zero)
           xy-mul)))))))))

(defun q2471737-linearly-ordered-field-p
    (carrier zero one add multiply negate inverse less)
  (let ((laws
         (q2471737-field-laws-function
          carrier zero one add multiply negate inverse less)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp multiply)
     (tamep-functionp negate)
     (tamep-functionp inverse)
     (tamep-functionp less)
     (q2471737-member-p carrier zero)
     (q2471737-member-p carrier one)
     (not (equal zero one))
     (q2471737-universal-p laws '(x y z)))))

;; Primitive-only terms for sparse vectors.

(defun q2471737-vector-coordinate-term (vector label zero)
  (let ((entry (list 'assoc-equal label vector)))
    (list 'if
          entry
          (q2471737-nth-term (q2471737-quoted 1) entry)
          (q2471737-quoted zero))))

(defun q2471737-vector-entry-function
    (scalar-carrier zero basis-carrier)
  (let ((label
         (q2471737-nth-term (q2471737-quoted 0) 'entry))
        (coefficient
         (q2471737-nth-term (q2471737-quoted 1) 'entry)))
    (list
     'lambda '(globals entry)
     (q2471737-and-terms
      (list
       (list 'true-listp 'entry)
       (list 'equal
             (list 'len 'entry)
             (q2471737-quoted 2))
       (q2471737-static-apply-term basis-carrier (list label))
       (q2471737-static-apply-term scalar-carrier (list coefficient))
       (q2471737-not-term
        (list 'equal coefficient (q2471737-quoted zero))))))))

(defun q2471737-entry-order-function ()
  (let* ((index
          (q2471737-nth-term
           (q2471737-quoted 0) 'index-tuple))
         (vector
          (q2471737-nth-term (q2471737-quoted 0) 'globals))
         (left-entry
          (q2471737-nth-term index vector))
         (right-entry
          (q2471737-nth-term
           (list 'binary-+ index (q2471737-quoted 1))
           vector))
         (left-label
          (q2471737-nth-term
           (q2471737-quoted 0) left-entry))
         (right-label
          (q2471737-nth-term
           (q2471737-quoted 0) right-entry)))
    (list
     'lambda '(globals index-tuple)
     (q2471737-and-terms
      (list
       (q2471737-not-term
        (list 'equal left-label right-label))
       (list 'lexorder left-label right-label))))))

(defun q2471737-vector-valid-term
    (vector scalar-carrier zero basis-carrier)
  (let ((entry-valid
         (q2471737-vector-entry-function
          scalar-carrier zero basis-carrier))
        (entry-order
         (q2471737-entry-order-function))
        (entry-count
         (list 'len vector)))
    (q2471737-and-terms
     (list
      (list 'true-listp vector)
      (list 'no-duplicatesp-equal
            (list 'strip-cars vector))
      (list 'always$+
            (q2471737-quoted entry-valid)
            (q2471737-quoted nil)
            vector)
      (list 'if
            (list '< entry-count (q2471737-quoted 2))
            (q2471737-quoted t)
            (list 'always$+
                  (q2471737-quoted entry-order)
                  (q2471737-term-list (list vector))
                  (q2471737-index-tuples-term
                   (list 'binary-+
                         entry-count
                         (q2471737-quoted -1)))))))))

(defun q2471737-vector-valid-p
    (vector scalar-carrier zero basis-carrier)
  (and
   (true-listp vector)
   (no-duplicatesp-equal (strip-cars vector))
   (let ((entry-valid
          (q2471737-vector-entry-function
           scalar-carrier zero basis-carrier))
         (entry-order
          (q2471737-entry-order-function)))
     (and
      (always$+ entry-valid nil vector)
      (or
       (< (len vector) 2)
       (always$+
        entry-order
        (list vector)
        (collect$
         (q2471737-index-tuple-function)
         (from-to-by 0 (+ (len vector) -2) 1))))))))

(defun q2471737-vector-set-laws-function
    (set-predicate scalar-carrier zero basis-carrier)
  (list
   'lambda '(vector)
   (q2471737-implies-term
    (q2471737-static-apply-term set-predicate '(vector))
    (q2471737-vector-valid-term
     'vector scalar-carrier zero basis-carrier))))

(defun q2471737-vector-set-p
    (set-predicate scalar-carrier zero basis-carrier)
  (let ((laws
         (q2471737-vector-set-laws-function
          set-predicate scalar-carrier zero basis-carrier)))
    (and
     (tamep-functionp set-predicate)
     (q2471737-universal-p laws '(vector)))))

;; Finite convex-combination certificates.

(defun q2471737-support-entry-function
    (set-predicate scalar-carrier zero basis-carrier)
  (list
   'lambda '(globals vector)
   (q2471737-and-terms
    (list
     (q2471737-vector-valid-term
      'vector scalar-carrier zero basis-carrier)
     (q2471737-static-apply-term set-predicate '(vector))))))

(defun q2471737-weight-entry-function
    (scalar-carrier zero less)
  (list
   'lambda '(weight)
   (q2471737-and-terms
    (list
     (q2471737-static-apply-term scalar-carrier '(weight))
     (q2471737-not-term
      (q2471737-static-apply-term
       less (list 'weight (q2471737-quoted zero))))))))

(defun q2471737-scalar-accumulator-step-function (add)
  (let* ((index
          (q2471737-nth-term
           (q2471737-quoted 0) 'index-tuple))
         (weights
          (q2471737-nth-term (q2471737-quoted 0) 'globals))
         (partial-sums
          (q2471737-nth-term (q2471737-quoted 1) 'globals))
         (current
          (q2471737-nth-term index partial-sums))
         (weight
          (q2471737-nth-term index weights))
         (next
          (q2471737-nth-term
           (list 'binary-+ index (q2471737-quoted 1))
           partial-sums)))
    (list
     'lambda '(globals index-tuple)
     (list 'equal
           next
           (q2471737-static-apply-term
            add (list current weight))))))

(defun q2471737-entry-label-covered-function ()
  (let ((labels
         (q2471737-nth-term (q2471737-quoted 0) 'globals))
        (label
         (q2471737-nth-term
          (q2471737-quoted 0) 'entry)))
    (list
     'lambda '(globals entry)
     (list 'member-equal label labels))))

(defun q2471737-vector-labels-covered-function ()
  (let* ((entry-covered
          (q2471737-entry-label-covered-function))
         (labels
          (q2471737-nth-term (q2471737-quoted 0) 'globals)))
    (list
     'lambda '(globals vector)
     (list 'always$+
           (q2471737-quoted entry-covered)
           (q2471737-term-list (list labels))
           'vector))))

(defun q2471737-coordinate-accumulator-step-function
    (zero add multiply)
  (let* ((index
          (q2471737-nth-term
           (q2471737-quoted 0) 'index-tuple))
         (support
          (q2471737-nth-term (q2471737-quoted 0) 'globals))
         (weights
          (q2471737-nth-term (q2471737-quoted 1) 'globals))
         (partial-sums
          (q2471737-nth-term (q2471737-quoted 2) 'globals))
         (label
          (q2471737-nth-term (q2471737-quoted 3) 'globals))
         (vector
          (q2471737-nth-term index support))
         (weight
          (q2471737-nth-term index weights))
         (coordinate
          (q2471737-vector-coordinate-term vector label zero))
         (current
          (q2471737-nth-term index partial-sums))
         (next
          (q2471737-nth-term
           (list 'binary-+ index (q2471737-quoted 1))
           partial-sums)))
    (list
     'lambda '(globals index-tuple)
     (list
      'equal
      next
      (q2471737-static-apply-term
       add
       (list
        current
        (q2471737-static-apply-term
         multiply (list weight coordinate))))))))

(defun q2471737-coordinate-row-function
    (scalar-carrier zero add multiply)
  (let* ((step
          (q2471737-coordinate-accumulator-step-function
           zero add multiply))
         (label-index
          (q2471737-nth-term
           (q2471737-quoted 0) 'label-index-tuple))
         (support
          (q2471737-nth-term (q2471737-quoted 0) 'globals))
         (weights
          (q2471737-nth-term (q2471737-quoted 1) 'globals))
         (labels
          (q2471737-nth-term (q2471737-quoted 2) 'globals))
         (coordinate-sums
          (q2471737-nth-term (q2471737-quoted 3) 'globals))
         (point
          (q2471737-nth-term (q2471737-quoted 4) 'globals))
         (support-count
          (list 'len support))
         (label
          (q2471737-nth-term label-index labels))
         (partial-sums
          (q2471737-nth-term label-index coordinate-sums)))
    (list
     'lambda '(globals label-index-tuple)
     (q2471737-and-terms
      (list
       (list 'true-listp partial-sums)
       (list 'equal
             (list 'len partial-sums)
             (list 'binary-+
                   support-count
                   (q2471737-quoted 1)))
       (list 'always$
             (q2471737-quoted scalar-carrier)
             partial-sums)
       (list 'equal
             (q2471737-nth-term
              (q2471737-quoted 0) partial-sums)
             (q2471737-quoted zero))
       (list 'equal
             (q2471737-nth-term support-count partial-sums)
             (q2471737-vector-coordinate-term
              point label zero))
       (list 'if
             (list 'zp support-count)
             (q2471737-quoted t)
             (list 'always$+
                   (q2471737-quoted step)
                   (q2471737-term-list
                    (list support weights partial-sums label))
                   (q2471737-index-tuples-term
                    support-count))))))))

(defun q2471737-convex-certificate-term
    (support weights scalar-sums labels coordinate-sums point
     set-predicate scalar-carrier zero one add multiply less
     basis-carrier)
  (let* ((support-entry
          (q2471737-support-entry-function
           set-predicate scalar-carrier zero basis-carrier))
         (weight-entry
          (q2471737-weight-entry-function
           scalar-carrier zero less))
         (scalar-step
          (q2471737-scalar-accumulator-step-function add))
         (entry-covered
          (q2471737-entry-label-covered-function))
         (vector-covered
          (q2471737-vector-labels-covered-function))
         (coordinate-row
          (q2471737-coordinate-row-function
           scalar-carrier zero add multiply))
         (support-count
          (list 'len support))
         (label-count
          (list 'len labels)))
    (q2471737-and-terms
     (list
      (list 'true-listp support)
      (list 'no-duplicatesp-equal support)
      (list 'always$+
            (q2471737-quoted support-entry)
            (q2471737-quoted nil)
            support)
      (list 'true-listp weights)
      (list 'equal (list 'len weights) support-count)
      (list 'always$
            (q2471737-quoted weight-entry)
            weights)
      (list 'true-listp scalar-sums)
      (list 'equal
            (list 'len scalar-sums)
            (list 'binary-+
                  support-count
                  (q2471737-quoted 1)))
      (list 'always$
            (q2471737-quoted scalar-carrier)
            scalar-sums)
      (list 'equal
            (q2471737-nth-term
             (q2471737-quoted 0) scalar-sums)
            (q2471737-quoted zero))
      (list 'equal
            (q2471737-nth-term support-count scalar-sums)
            (q2471737-quoted one))
      (list 'if
            (list 'zp support-count)
            (q2471737-quoted t)
            (list 'always$+
                  (q2471737-quoted scalar-step)
                  (q2471737-term-list
                   (list weights scalar-sums))
                  (q2471737-index-tuples-term
                   support-count)))
      (list 'true-listp labels)
      (list 'no-duplicatesp-equal labels)
      (list 'always$
            (q2471737-quoted basis-carrier)
            labels)
      (list 'always$+
            (q2471737-quoted entry-covered)
            (q2471737-term-list (list labels))
            point)
      (list 'always$+
            (q2471737-quoted vector-covered)
            (q2471737-term-list (list labels))
            support)
      (list 'true-listp coordinate-sums)
      (list 'equal
            (list 'len coordinate-sums)
            label-count)
      (list 'if
            (list 'zp label-count)
            (q2471737-quoted t)
            (list 'always$+
                  (q2471737-quoted coordinate-row)
                  (q2471737-term-list
                   (list support weights labels
                         coordinate-sums point))
                  (q2471737-index-tuples-term
                   label-count)))))))

(defun q2471737-convex-representation-function
    (point set-predicate scalar-carrier zero one add multiply less
     basis-carrier)
  (let* ((support
          (q2471737-nth-term (q2471737-quoted 0) 'witness))
         (weights
          (q2471737-nth-term (q2471737-quoted 1) 'witness))
         (scalar-sums
          (q2471737-nth-term (q2471737-quoted 2) 'witness))
         (labels
          (q2471737-nth-term (q2471737-quoted 3) 'witness))
         (coordinate-sums
          (q2471737-nth-term (q2471737-quoted 4) 'witness)))
    (list
     'lambda '(witness)
     (q2471737-and-terms
      (list
       (list 'true-listp 'witness)
       (list 'equal
             (list 'len 'witness)
             (q2471737-quoted 5))
       (q2471737-convex-certificate-term
        support weights scalar-sums labels coordinate-sums
        (q2471737-quoted point)
        set-predicate scalar-carrier zero one add multiply less
        basis-carrier))))))

(defun q2471737-set-convex-hull-member-p
    (point set-predicate scalar-carrier zero one add multiply less
     basis-carrier)
  (let ((predicate
         (q2471737-convex-representation-function
          point set-predicate scalar-carrier zero one
          add multiply less basis-carrier)))
    (q2471737-exists-p predicate '(witness))))

;; A finite positive certificate for affine independence. For N support
;; points, the N-1 difference columns have a square coordinate minor with a
;; left inverse. Product accumulator rows validate the matrix equations over
;; the arbitrary field.

(defun q2471737-inverse-row-function (scalar-carrier)
  (let ((minor-size
         (q2471737-nth-term
          (q2471737-quoted 0) 'globals)))
    (list
     'lambda '(globals row)
     (q2471737-and-terms
      (list
       (list 'true-listp 'row)
       (list 'equal
             (list 'len 'row)
             minor-size)
       (list 'always$
             (q2471737-quoted scalar-carrier)
             'row))))))

(defun q2471737-product-accumulator-step-function
    (zero add multiply negate)
  (let* ((index
          (q2471737-nth-term
           (q2471737-quoted 0) 'index-tuple))
         (support
          (q2471737-nth-term (q2471737-quoted 0) 'globals))
         (row-labels
          (q2471737-nth-term (q2471737-quoted 1) 'globals))
         (inverse
          (q2471737-nth-term (q2471737-quoted 2) 'globals))
         (partial-sums
          (q2471737-nth-term (q2471737-quoted 3) 'globals))
         (row-index
          (q2471737-nth-term (q2471737-quoted 4) 'globals))
         (column-index
          (q2471737-nth-term (q2471737-quoted 5) 'globals))
         (anchor
          (q2471737-nth-term (q2471737-quoted 0) support))
         (column-vector
          (q2471737-nth-term
           (list 'binary-+
                 column-index
                 (q2471737-quoted 1))
           support))
         (label
          (q2471737-nth-term index row-labels))
         (anchor-coordinate
          (q2471737-vector-coordinate-term anchor label zero))
         (column-coordinate
          (q2471737-vector-coordinate-term
           column-vector label zero))
         (difference
          (q2471737-static-apply-term
           add
           (list
            column-coordinate
            (q2471737-static-apply-term
             negate (list anchor-coordinate)))))
         (inverse-entry
          (q2471737-nth-term
           index
           (q2471737-nth-term row-index inverse)))
         (current
          (q2471737-nth-term index partial-sums))
         (next
          (q2471737-nth-term
           (list 'binary-+ index (q2471737-quoted 1))
           partial-sums)))
    (list
     'lambda '(globals index-tuple)
     (list
      'equal
      next
      (q2471737-static-apply-term
       add
       (list
        current
        (q2471737-static-apply-term
         multiply (list inverse-entry difference))))))))

(defun q2471737-product-row-function
    (scalar-carrier zero one add multiply negate)
  (let* ((step
          (q2471737-product-accumulator-step-function
           zero add multiply negate))
         (pair-index
          (q2471737-nth-term
           (q2471737-quoted 0) 'pair-index-tuple))
         (support
          (q2471737-nth-term (q2471737-quoted 0) 'globals))
         (row-labels
          (q2471737-nth-term (q2471737-quoted 1) 'globals))
         (inverse
          (q2471737-nth-term (q2471737-quoted 2) 'globals))
         (products
          (q2471737-nth-term (q2471737-quoted 3) 'globals))
         (minor-size
          (list 'len row-labels))
         (row-index
          (list 'floor pair-index minor-size))
         (column-index
          (list 'mod pair-index minor-size))
         (partial-sums
          (q2471737-nth-term pair-index products))
         (target
          (list 'if
                (list 'equal row-index column-index)
                (q2471737-quoted one)
                (q2471737-quoted zero))))
    (list
     'lambda '(globals pair-index-tuple)
     (q2471737-and-terms
      (list
       (list 'true-listp partial-sums)
       (list 'equal
             (list 'len partial-sums)
             (list 'binary-+
                   minor-size
                   (q2471737-quoted 1)))
       (list 'always$
             (q2471737-quoted scalar-carrier)
             partial-sums)
       (list 'equal
             (q2471737-nth-term
              (q2471737-quoted 0) partial-sums)
             (q2471737-quoted zero))
       (list 'equal
             (q2471737-nth-term minor-size partial-sums)
             target)
       (list 'always$+
             (q2471737-quoted step)
             (q2471737-term-list
              (list support row-labels inverse partial-sums
                    row-index column-index))
             (q2471737-index-tuples-term
              minor-size)))))))

(defun q2471737-affine-independence-certificate-term
    (support row-labels inverse products
     scalar-carrier zero one add multiply negate basis-carrier)
  (let* ((support-count
          (list 'len support))
         (minor-size
          (list 'binary-+
                support-count
                (q2471737-quoted -1)))
         (inverse-row
          (q2471737-inverse-row-function scalar-carrier))
         (product-row
          (q2471737-product-row-function
           scalar-carrier zero one add multiply negate)))
    (q2471737-and-terms
     (list
      (q2471737-not-term
       (list 'zp support-count))
      (list
       'if
       (list 'zp minor-size)
       (q2471737-and-terms
        (list
         (list 'equal row-labels (q2471737-quoted nil))
         (list 'equal inverse (q2471737-quoted nil))
         (list 'equal products (q2471737-quoted nil))))
       (q2471737-and-terms
        (list
         (list 'true-listp row-labels)
         (list 'equal
               (list 'len row-labels)
               minor-size)
         (list 'no-duplicatesp-equal row-labels)
         (list 'always$
               (q2471737-quoted basis-carrier)
               row-labels)
         (list 'true-listp inverse)
         (list 'equal
               (list 'len inverse)
               minor-size)
         (list 'always$+
               (q2471737-quoted inverse-row)
               (q2471737-term-list (list minor-size))
               inverse)
         (list 'true-listp products)
         (list 'equal
               (list 'len products)
               (list 'binary-*
                     minor-size
                     minor-size))
         (list 'always$+
               (q2471737-quoted product-row)
               (q2471737-term-list
                (list support row-labels inverse products))
               (q2471737-index-tuples-term
                (list 'binary-*
                      minor-size
                      minor-size))))))))))

(defun q2471737-independent-support-function
    (point set-predicate scalar-carrier zero one add multiply negate less
     basis-carrier)
  (let* ((support
          (q2471737-nth-term (q2471737-quoted 0) 'witness))
         (weights
          (q2471737-nth-term (q2471737-quoted 1) 'witness))
         (scalar-sums
          (q2471737-nth-term (q2471737-quoted 2) 'witness))
         (labels
          (q2471737-nth-term (q2471737-quoted 3) 'witness))
         (coordinate-sums
          (q2471737-nth-term (q2471737-quoted 4) 'witness))
         (row-labels
          (q2471737-nth-term (q2471737-quoted 5) 'witness))
         (inverse
          (q2471737-nth-term (q2471737-quoted 6) 'witness))
         (products
          (q2471737-nth-term (q2471737-quoted 7) 'witness)))
    (list
     'lambda '(witness)
     (q2471737-and-terms
      (list
       (list 'true-listp 'witness)
       (list 'equal
             (list 'len 'witness)
             (q2471737-quoted 8))
       (q2471737-convex-certificate-term
        support weights scalar-sums labels coordinate-sums
        (q2471737-quoted point)
        set-predicate scalar-carrier zero one add multiply less
        basis-carrier)
       (q2471737-affine-independence-certificate-term
        support row-labels inverse products
        scalar-carrier zero one add multiply negate
        basis-carrier))))))

(defun q2471737-union-member-p
    (point set-predicate scalar-carrier zero one add multiply negate less
     basis-carrier)
  (let ((predicate
         (q2471737-independent-support-function
          point set-predicate scalar-carrier zero one
          add multiply negate less basis-carrier)))
    (q2471737-exists-p predicate '(witness))))

(defun thousand-theorems-q2471737-carath-odory-convex-hull-statement
    (scalar-carrier zero one add multiply negate inverse less
     basis-carrier set-predicate point)
  (implies
   (and
    (q2471737-linearly-ordered-field-p
     scalar-carrier zero one add multiply negate inverse less)
    (tamep-functionp basis-carrier)
    (q2471737-vector-set-p
     set-predicate scalar-carrier zero basis-carrier)
    (q2471737-vector-valid-p
     point scalar-carrier zero basis-carrier))
   (iff
    (q2471737-set-convex-hull-member-p
     point set-predicate scalar-carrier zero one
     add multiply less basis-carrier)
    (q2471737-union-member-p
     point set-predicate scalar-carrier zero one
     add multiply negate less basis-carrier))))

;; Admission-time audit of every reified function family. This asserts no
;; theorem and admits no proof, constraint, warrant, badge, or axiom.

(defun q2471737-all-reified-functions-tame-p ()
  (let* ((unary '(lambda (x) (quote t)))
         (binary '(lambda (x y) x))
         (point '((basis-label 1))))
    (and
     (tamep-functionp
      (q2471737-true-function '(x)))
     (tamep-functionp
      (q2471737-false-function '(x)))
     (tamep-functionp
      (q2471737-index-tuple-function))
     (tamep-functionp
      (q2471737-field-laws-function
       unary 0 1 binary binary unary unary binary))
     (tamep-functionp
      (q2471737-vector-entry-function unary 0 unary))
     (tamep-functionp
      (q2471737-entry-order-function))
     (tamep-functionp
      (q2471737-vector-set-laws-function unary unary 0 unary))
     (tamep-functionp
      (q2471737-support-entry-function unary unary 0 unary))
     (tamep-functionp
      (q2471737-weight-entry-function unary 0 binary))
     (tamep-functionp
      (q2471737-scalar-accumulator-step-function binary))
     (tamep-functionp
      (q2471737-entry-label-covered-function))
     (tamep-functionp
      (q2471737-vector-labels-covered-function))
     (tamep-functionp
      (q2471737-coordinate-accumulator-step-function
       0 binary binary))
     (tamep-functionp
      (q2471737-coordinate-row-function
       unary 0 binary binary))
     (tamep-functionp
     (q2471737-convex-representation-function
       point unary unary 0 1 binary binary binary unary))
     (tamep-functionp
      (q2471737-inverse-row-function unary))
     (tamep-functionp
      (q2471737-product-accumulator-step-function
       0 binary binary unary))
     (tamep-functionp
      (q2471737-product-row-function
       unary 0 1 binary binary unary))
     (tamep-functionp
      (q2471737-independent-support-function
       point unary unary 0 1 binary binary unary binary unary)))))

(value-triple
 (if (q2471737-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q2471737-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
