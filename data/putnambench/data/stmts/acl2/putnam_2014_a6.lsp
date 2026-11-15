;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_a6:
;; the largest size of two real n-by-n matrix families whose cross-products
;; have a zero diagonal entry exactly off the matching pairs is n^n. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The entries are interpreted in an arbitrary real closed ordered field.
;; Real closed fields are elementarily equivalent, so each fixed finite
;; matrix-existence assertion below holds in this presentation exactly when
;; it holds over the real numbers. Matrix families are flat finite lists only
;; as a representation of their finite index types, not as a restriction on
;; their entries. Negated FN-EQUAL supplies the internal existential
;; quantifier over the complete pair of matrix families.

(defun putnam-2014-a6-quoted (object)
  (list 'quote object))

(defun putnam-2014-a6-apply1-term (function argument)
  (list
   'apply$
   (putnam-2014-a6-quoted function)
   (list 'cons argument nil)))

(defun putnam-2014-a6-apply2-term (function left right)
  (list
   'apply$
   (putnam-2014-a6-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2014-a6-and-term (terms)
  (if (endp terms)
      (putnam-2014-a6-quoted t)
    (list
     'if
     (car terms)
     (putnam-2014-a6-and-term (cdr terms))
     (putnam-2014-a6-quoted nil))))

(defun putnam-2014-a6-or-term (terms)
  (if (endp terms)
      (putnam-2014-a6-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2014-a6-quoted t)
     (putnam-2014-a6-or-term (cdr terms)))))

(defun putnam-2014-a6-not-term (term)
  (list
   'if
   term
   (putnam-2014-a6-quoted nil)
   (putnam-2014-a6-quoted t)))

(defun putnam-2014-a6-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2014-a6-quoted t)))

(defun putnam-2014-a6-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2014-a6-quoted t)))

(defun putnam-2014-a6-carrier-term (carrier element)
  (putnam-2014-a6-apply1-term carrier element))

(defun putnam-2014-a6-operation-term (operation left right)
  (putnam-2014-a6-apply2-term operation left right))

(defun putnam-2014-a6-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2014-a6-carrier-term carrier 'loop$-ivars)))

(defun putnam-2014-a6-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2014-a6-quoted
    (putnam-2014-a6-all-coefficients-function carrier))
   (putnam-2014-a6-quoted nil)
   coefficients))

(defun putnam-2014-a6-polynomial-term
    (carrier zero coefficients)
  (putnam-2014-a6-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2014-a6-all-coefficients-term
     carrier coefficients)
    (putnam-2014-a6-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2014-a6-quoted 1))
      (putnam-2014-a6-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2014-a6-quoted zero))))))))

(defun putnam-2014-a6-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2014-a6-quoted zero))
         (qone (putnam-2014-a6-quoted one))
         (add-xy
          (putnam-2014-a6-operation-term add x y))
         (add-yz
          (putnam-2014-a6-operation-term add y z))
         (mul-xy
          (putnam-2014-a6-operation-term mul x y))
         (mul-yz
          (putnam-2014-a6-operation-term mul y z))
         (neg-x
          (putnam-2014-a6-apply1-term neg x))
         (inv-x
          (putnam-2014-a6-apply1-term inv x))
         (domain
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term carrier x)
            (putnam-2014-a6-carrier-term carrier y)
            (putnam-2014-a6-carrier-term carrier z))))
         (laws
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term carrier add-xy)
            (putnam-2014-a6-carrier-term carrier mul-xy)
            (putnam-2014-a6-carrier-term carrier neg-x)
            (putnam-2014-a6-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2014-a6-operation-term add add-xy z)
             (putnam-2014-a6-operation-term add x add-yz))
            (list
             'equal
             (putnam-2014-a6-operation-term mul mul-xy z)
             (putnam-2014-a6-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2014-a6-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2014-a6-operation-term mul y x))
            (list
             'equal
             (putnam-2014-a6-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2014-a6-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2014-a6-operation-term mul x qone)
             x)
            (putnam-2014-a6-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2014-a6-implies-term
             (putnam-2014-a6-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2014-a6-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2014-a6-operation-term mul x add-yz)
             (putnam-2014-a6-operation-term
              add
              (putnam-2014-a6-operation-term mul x y)
              (putnam-2014-a6-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2014-a6-implies-term domain laws))))

(defun putnam-2014-a6-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2014-a6-quoted zero))
         (lt-xy
          (putnam-2014-a6-operation-term lt x y))
         (lt-yx
          (putnam-2014-a6-operation-term lt y x))
         (lt-yz
          (putnam-2014-a6-operation-term lt y z))
         (lt-xz
          (putnam-2014-a6-operation-term lt x z))
         (domain
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term carrier x)
            (putnam-2014-a6-carrier-term carrier y)
            (putnam-2014-a6-carrier-term carrier z))))
         (laws
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-not-term
             (putnam-2014-a6-operation-term lt x x))
            (putnam-2014-a6-or-term
             (list lt-xy (list 'equal x y) lt-yx))
            (putnam-2014-a6-implies-term
             (putnam-2014-a6-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2014-a6-implies-term
             lt-xy
             (putnam-2014-a6-operation-term
              lt
              (putnam-2014-a6-operation-term add x z)
              (putnam-2014-a6-operation-term add y z)))
            (putnam-2014-a6-implies-term
             (putnam-2014-a6-and-term
              (list
               (putnam-2014-a6-operation-term lt qzero x)
               (putnam-2014-a6-operation-term lt qzero y)))
             (putnam-2014-a6-operation-term
              lt
              qzero
              (putnam-2014-a6-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2014-a6-implies-term domain laws))))

(defun putnam-2014-a6-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2014-a6-quoted zero))
         (root
          (putnam-2014-a6-apply1-term square-root x))
         (domain
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term carrier x)
            (putnam-2014-a6-not-term
             (putnam-2014-a6-operation-term lt x qzero)))))
         (laws
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term carrier root)
            (list
             'equal
             (putnam-2014-a6-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2014-a6-implies-term domain laws))))

(defun putnam-2014-a6-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2014-a6-quoted zero))
         (domain
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2014-a6-all-coefficients-term
             carrier rest)
            (putnam-2014-a6-carrier-term carrier x))))
         (empty-law
          (putnam-2014-a6-implies-term
           (putnam-2014-a6-carrier-term carrier x)
           (list
            'equal
            (putnam-2014-a6-operation-term
             evaluate
             (putnam-2014-a6-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2014-a6-operation-term
           add
           coefficient
           (putnam-2014-a6-operation-term
            mul
            x
            (putnam-2014-a6-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2014-a6-implies-term
           domain
           (putnam-2014-a6-and-term
            (list
             (putnam-2014-a6-carrier-term
              carrier
              (putnam-2014-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2014-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2014-a6-and-term
      (list empty-law recursive-law)))))

(defun putnam-2014-a6-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2014-a6-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2014-a6-and-term
           (list
            (putnam-2014-a6-carrier-term carrier root)
            (list
             'equal
             (putnam-2014-a6-operation-term
              evaluate coefficients root)
             (putnam-2014-a6-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2014-a6-implies-term domain laws))))

(defun putnam-2014-a6-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2014-a6-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2014-a6-true-function '(x y z)))
         (order-laws
          (putnam-2014-a6-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2014-a6-true-function '(x y z)))
         (square-root-laws
          (putnam-2014-a6-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2014-a6-true-function '(x)))
         (evaluation-laws
          (putnam-2014-a6-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2014-a6-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2014-a6-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2014-a6-true-function
           '(coefficients))))
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
     (tamep-functionp field-laws)
     (tamep-functionp field-laws-true)
     (tamep-functionp order-laws)
     (tamep-functionp order-laws-true)
     (tamep-functionp square-root-laws)
     (tamep-functionp square-root-laws-true)
     (tamep-functionp evaluation-laws)
     (tamep-functionp evaluation-laws-true)
     (tamep-functionp odd-root-laws)
     (tamep-functionp odd-root-laws-true)
     (apply$ carrier (list zero))
     (apply$ carrier (list one))
     (not (equal zero one))
     (fn-equal field-laws field-laws-true)
     (fn-equal order-laws order-laws-true)
     (fn-equal square-root-laws square-root-laws-true)
     (fn-equal evaluation-laws evaluation-laws-true)
     (fn-equal odd-root-laws odd-root-laws-true))))

(defun putnam-2014-a6-matrix-entry-index
    (family-offset n matrix row column)
  (+ family-offset
     (* matrix n n)
     (* row n)
     column))

(defun putnam-2014-a6-matrix-entry-term
    (family-offset n matrix row column)
  (list
   'nth
   (putnam-2014-a6-quoted
    (putnam-2014-a6-matrix-entry-index
     family-offset n matrix row column))
   'witness))

(defun putnam-2014-a6-product-diagonal-term
    (zero add mul m-offset n-offset n i j p index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2014-a6-quoted zero)
    (putnam-2014-a6-operation-term
     add
     (putnam-2014-a6-operation-term
      mul
      (putnam-2014-a6-matrix-entry-term
       m-offset n i p index)
      (putnam-2014-a6-matrix-entry-term
       n-offset n j index p))
     (putnam-2014-a6-product-diagonal-term
      zero add mul m-offset n-offset n i j p
      (+ index 1) (- remaining 1)))))

(defun putnam-2014-a6-some-zero-diagonal-term
    (zero add mul m-offset n-offset n i j p remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2014-a6-quoted nil)
    (putnam-2014-a6-or-term
     (list
      (list
       'equal
       (putnam-2014-a6-product-diagonal-term
        zero add mul m-offset n-offset n i j p 0 n)
       (putnam-2014-a6-quoted zero))
      (putnam-2014-a6-some-zero-diagonal-term
       zero add mul m-offset n-offset n i j
       (+ p 1) (- remaining 1))))))

(defun putnam-2014-a6-pair-condition-term
    (zero add mul m-offset n-offset n i j)
  (let ((some-zero
         (putnam-2014-a6-some-zero-diagonal-term
          zero add mul m-offset n-offset n i j 0 n)))
    (if (equal i j)
        (putnam-2014-a6-not-term some-zero)
      some-zero)))

(defun putnam-2014-a6-all-columns-term
    (zero add mul m-offset n-offset n i j remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2014-a6-quoted t)
    (putnam-2014-a6-and-term
     (list
      (putnam-2014-a6-pair-condition-term
       zero add mul m-offset n-offset n i j)
      (putnam-2014-a6-all-columns-term
       zero add mul m-offset n-offset n i
       (+ j 1) (- remaining 1))))))

(defun putnam-2014-a6-all-pairs-term
    (zero add mul m-offset n-offset n k i remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2014-a6-quoted t)
    (putnam-2014-a6-and-term
     (list
      (putnam-2014-a6-all-columns-term
       zero add mul m-offset n-offset n i 0 k)
      (putnam-2014-a6-all-pairs-term
       zero add mul m-offset n-offset n k
       (+ i 1) (- remaining 1))))))

(defun putnam-2014-a6-all-entries-term
    (carrier index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2014-a6-quoted t)
    (putnam-2014-a6-and-term
     (list
      (putnam-2014-a6-carrier-term
       carrier
       (list 'nth
             (putnam-2014-a6-quoted index)
             'witness))
      (putnam-2014-a6-all-entries-term
       carrier (+ index 1) (- remaining 1))))))

(defun putnam-2014-a6-witness-failure-function
    (carrier zero add mul n k)
  (let* ((family-size (* k n n))
         (entry-count (* 2 family-size))
         (qualification
          (putnam-2014-a6-and-term
           (list
            (list 'true-listp 'witness)
            (list
             'equal
             (list 'len 'witness)
             (putnam-2014-a6-quoted entry-count))
            (putnam-2014-a6-all-entries-term
             carrier 0 entry-count)
            (putnam-2014-a6-all-pairs-term
             zero add mul 0 family-size n k 0 k)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2014-a6-quoted nil)
      (putnam-2014-a6-quoted t)))))

(defun putnam-2014-a6-configuration-exists-p
    (carrier zero add mul n k)
  (let ((failure
         (putnam-2014-a6-witness-failure-function
          carrier zero add mul n k))
        (true-on-one
         (putnam-2014-a6-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp true-on-one)
     (not (fn-equal failure true-on-one)))))

;; The free ACL2 input K represents the source conclusion's universal
;; quantifier over positive integers. The first conjunct is independent of K
;; and states attainment at n^n; the second states maximality.
(defun putnambench-putnam-2014-a6-statement
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate n k)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-2014-a6-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate))
   (and
    (putnam-2014-a6-configuration-exists-p
     carrier zero add mul n (expt n n))
    (implies
     (and
      (natp k)
      (<= 1 k)
      (putnam-2014-a6-configuration-exists-p
       carrier zero add mul n k))
     (<= k (expt n n))))))

(value-triple :itpeval-statement-checked)
:q
