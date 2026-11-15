;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_a6:
;; the greatest number of initial odd-power interval-sum identities attainable
;; by 2n strictly increasing real points in (-1,1) is n. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source constraints are first-order formulas over the ordered real
;; field. Real closed fields are elementarily equivalent, so it is equivalent
;; to state the result over an arbitrary real closed ordered field. The
;; square-root and odd-polynomial-root selectors below are the standard
;; first-order presentation of real closedness; they add operations but do not
;; restrict the represented field.
;;
;; FN-EQUAL with a failure predicate supplies the internal existential
;; quantifier over the list x_1,...,x_(2n). The property P(m) is downward
;; closed in m, so saying that n is its greatest natural member is equivalent
;; to P(n) and not P(n+1). The Lean source's globally strictly increasing
;; natural-indexed sequence is equivalent here: any qualifying finite list can
;; be extended by one point below x_1 and an infinite increasing tail after
;; x_(2n), while restriction recovers exactly this list.

(defun putnam-2022-a6-quoted (object)
  (list 'quote object))

(defun putnam-2022-a6-apply1-term (function argument)
  (list
   'apply$
   (putnam-2022-a6-quoted function)
   (list 'cons argument nil)))

(defun putnam-2022-a6-apply2-term (function left right)
  (list
   'apply$
   (putnam-2022-a6-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2022-a6-and-term (terms)
  (if (endp terms)
      (putnam-2022-a6-quoted t)
    (list
     'if
     (car terms)
     (putnam-2022-a6-and-term (cdr terms))
     (putnam-2022-a6-quoted nil))))

(defun putnam-2022-a6-or-term (terms)
  (if (endp terms)
      (putnam-2022-a6-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2022-a6-quoted t)
     (putnam-2022-a6-or-term (cdr terms)))))

(defun putnam-2022-a6-not-term (term)
  (list
   'if
   term
   (putnam-2022-a6-quoted nil)
   (putnam-2022-a6-quoted t)))

(defun putnam-2022-a6-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2022-a6-quoted t)))

(defun putnam-2022-a6-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2022-a6-quoted t)))

(defun putnam-2022-a6-carrier-term (carrier element)
  (putnam-2022-a6-apply1-term carrier element))

(defun putnam-2022-a6-operation-term (operation left right)
  (putnam-2022-a6-apply2-term operation left right))

(defun putnam-2022-a6-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2022-a6-quoted zero))
         (qone (putnam-2022-a6-quoted one))
         (add-xy
          (putnam-2022-a6-operation-term add x y))
         (add-yz
          (putnam-2022-a6-operation-term add y z))
         (mul-xy
          (putnam-2022-a6-operation-term mul x y))
         (mul-yz
          (putnam-2022-a6-operation-term mul y z))
         (neg-x
          (putnam-2022-a6-apply1-term neg x))
         (inv-x
          (putnam-2022-a6-apply1-term inv x))
         (domain
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term carrier x)
            (putnam-2022-a6-carrier-term carrier y)
            (putnam-2022-a6-carrier-term carrier z))))
         (laws
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term carrier add-xy)
            (putnam-2022-a6-carrier-term carrier mul-xy)
            (putnam-2022-a6-carrier-term carrier neg-x)
            (putnam-2022-a6-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2022-a6-operation-term add add-xy z)
             (putnam-2022-a6-operation-term add x add-yz))
            (list
             'equal
             (putnam-2022-a6-operation-term mul mul-xy z)
             (putnam-2022-a6-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2022-a6-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2022-a6-operation-term mul y x))
            (list
             'equal
             (putnam-2022-a6-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2022-a6-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2022-a6-operation-term mul x qone)
             x)
            (putnam-2022-a6-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2022-a6-implies-term
             (putnam-2022-a6-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2022-a6-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2022-a6-operation-term mul x add-yz)
             (putnam-2022-a6-operation-term
              add
              (putnam-2022-a6-operation-term mul x y)
              (putnam-2022-a6-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2022-a6-implies-term domain laws))))

(defun putnam-2022-a6-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2022-a6-quoted zero))
         (lt-xy
          (putnam-2022-a6-operation-term lt x y))
         (lt-yx
          (putnam-2022-a6-operation-term lt y x))
         (lt-yz
          (putnam-2022-a6-operation-term lt y z))
         (lt-xz
          (putnam-2022-a6-operation-term lt x z))
         (domain
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term carrier x)
            (putnam-2022-a6-carrier-term carrier y)
            (putnam-2022-a6-carrier-term carrier z))))
         (laws
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-not-term
             (putnam-2022-a6-operation-term lt x x))
            (putnam-2022-a6-or-term
             (list
              lt-xy
              lt-yx
              (list 'equal x y)))
            (putnam-2022-a6-implies-term
             (putnam-2022-a6-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2022-a6-implies-term
             lt-xy
             (putnam-2022-a6-operation-term
              lt
              (putnam-2022-a6-operation-term add x z)
              (putnam-2022-a6-operation-term add y z)))
            (putnam-2022-a6-implies-term
             (putnam-2022-a6-and-term
              (list
               (putnam-2022-a6-operation-term lt qzero x)
               (putnam-2022-a6-operation-term lt qzero y)))
             (putnam-2022-a6-operation-term
              lt
              qzero
              (putnam-2022-a6-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2022-a6-implies-term domain laws))))

(defun putnam-2022-a6-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2022-a6-quoted zero))
         (root
          (putnam-2022-a6-apply1-term square-root x))
         (domain
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term carrier x)
            (putnam-2022-a6-not-term
             (putnam-2022-a6-operation-term lt x qzero)))))
         (laws
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term carrier root)
            (putnam-2022-a6-not-term
             (putnam-2022-a6-operation-term lt root qzero))
            (list
             'equal
             (putnam-2022-a6-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2022-a6-implies-term domain laws))))

(defun putnam-2022-a6-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2022-a6-carrier-term carrier 'loop$-ivars)))

(defun putnam-2022-a6-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2022-a6-quoted
    (putnam-2022-a6-all-coefficients-function carrier))
   (putnam-2022-a6-quoted nil)
   coefficients))

(defun putnam-2022-a6-polynomial-term
    (carrier zero coefficients)
  (putnam-2022-a6-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2022-a6-all-coefficients-term
     carrier coefficients)
    (putnam-2022-a6-or-term
     (list
      (list
       'equal
       (list 'len coefficients)
       (putnam-2022-a6-quoted 1))
      (putnam-2022-a6-not-term
       (list
        'equal
        (list 'car (list 'last coefficients))
        (putnam-2022-a6-quoted zero))))))))

(defun putnam-2022-a6-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2022-a6-quoted zero))
         (domain
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2022-a6-all-coefficients-term
             carrier rest)
            (putnam-2022-a6-carrier-term carrier x))))
         (empty-law
          (putnam-2022-a6-implies-term
           (putnam-2022-a6-carrier-term carrier x)
           (list
            'equal
            (putnam-2022-a6-operation-term
             evaluate
             (putnam-2022-a6-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2022-a6-operation-term
           add
           coefficient
           (putnam-2022-a6-operation-term
            mul
            x
            (putnam-2022-a6-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2022-a6-implies-term
           domain
           (putnam-2022-a6-and-term
            (list
             (putnam-2022-a6-carrier-term
              carrier
              (putnam-2022-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2022-a6-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2022-a6-and-term
      (list empty-law recursive-law)))))

(defun putnam-2022-a6-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (half 'half)
         (root
          (putnam-2022-a6-apply2-term
           odd-root coefficients half))
         (domain
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-polynomial-term
             carrier zero coefficients)
            (list 'natp half)
            (list
             'equal
             (list 'len coefficients)
             (list
              'binary-+
              (list
               'binary-*
               (putnam-2022-a6-quoted 2)
               half)
              (putnam-2022-a6-quoted 2))))))
         (laws
          (putnam-2022-a6-and-term
           (list
            (putnam-2022-a6-carrier-term carrier root)
            (list
             'equal
             (putnam-2022-a6-operation-term
              evaluate coefficients root)
             (putnam-2022-a6-quoted zero))))))
    (list
     'lambda
     '(coefficients half)
     (putnam-2022-a6-implies-term domain laws))))

(defun putnam-2022-a6-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root evaluate odd-root)
  (let* ((field-laws
          (putnam-2022-a6-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2022-a6-true-function '(x y z)))
         (order-laws
          (putnam-2022-a6-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2022-a6-true-function '(x y z)))
         (square-root-laws
          (putnam-2022-a6-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2022-a6-true-function '(x)))
         (evaluation-laws
          (putnam-2022-a6-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2022-a6-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2022-a6-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2022-a6-true-function
           '(coefficients half))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp mul)
     (tamep-functionp neg)
     (tamep-functionp inv)
     (tamep-functionp lt)
     (tamep-functionp square-root)
     (tamep-functionp evaluate)
     (tamep-functionp odd-root)
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

(defun putnam-2022-a6-nth-term (index values)
  (list 'nth (putnam-2022-a6-quoted index) values))

(defun putnam-2022-a6-field-element-terms
    (count index carrier values)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (putnam-2022-a6-carrier-term
      carrier
      (putnam-2022-a6-nth-term index values))
     (putnam-2022-a6-field-element-terms
      (- count 1) (+ index 1) carrier values))))

(defun putnam-2022-a6-increasing-terms
    (count index lt values)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1))
      nil
    (cons
     (putnam-2022-a6-operation-term
      lt
      (putnam-2022-a6-nth-term index values)
      (putnam-2022-a6-nth-term (+ index 1) values))
     (putnam-2022-a6-increasing-terms
      (- count 1) (+ index 1) lt values))))

(defun putnam-2022-a6-power-term (base exponent one mul)
  (declare (xargs :measure (nfix exponent)))
  (cond
   ((zp exponent)
    (putnam-2022-a6-quoted one))
   ((equal exponent 1)
    base)
   (t
    (putnam-2022-a6-operation-term
     mul
     base
     (putnam-2022-a6-power-term
      base (- exponent 1) one mul)))))

(defun putnam-2022-a6-interval-sum-term
    (values pair-index pairs exponent zero one add mul neg)
  (declare (xargs :measure (nfix pairs)))
  (if (zp pairs)
      (putnam-2022-a6-quoted zero)
    (putnam-2022-a6-operation-term
     add
     (putnam-2022-a6-operation-term
      add
      (putnam-2022-a6-power-term
       (putnam-2022-a6-nth-term
        (+ (* 2 pair-index) 1) values)
       exponent one mul)
      (putnam-2022-a6-apply1-term
       neg
       (putnam-2022-a6-power-term
        (putnam-2022-a6-nth-term
         (* 2 pair-index) values)
        exponent one mul)))
     (putnam-2022-a6-interval-sum-term
      values
      (+ pair-index 1)
      (- pairs 1)
      exponent
      zero one add mul neg))))

(defun putnam-2022-a6-identity-terms
    (values n k zero one add mul neg)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      nil
    (cons
     (list
      'equal
      (putnam-2022-a6-interval-sum-term
       values
       0
       n
       (- (* 2 k) 1)
       zero one add mul neg)
      (putnam-2022-a6-quoted one))
     (putnam-2022-a6-identity-terms
      values n (- k 1) zero one add mul neg))))

(defun putnam-2022-a6-witness-term
    (n m carrier zero one add mul neg lt values)
  (let ((count (* 2 n)))
    (putnam-2022-a6-and-term
     (append
      (list
       (list 'true-listp values)
       (list
        'equal
        (list 'len values)
        (putnam-2022-a6-quoted count)))
      (putnam-2022-a6-field-element-terms
       count 0 carrier values)
      (putnam-2022-a6-increasing-terms
       count 0 lt values)
      (list
       (putnam-2022-a6-operation-term
        lt
        (putnam-2022-a6-apply1-term
         neg
         (putnam-2022-a6-quoted one))
        (putnam-2022-a6-nth-term 0 values))
       (putnam-2022-a6-operation-term
        lt
        (putnam-2022-a6-nth-term (- count 1) values)
        (putnam-2022-a6-quoted one)))
      (putnam-2022-a6-identity-terms
       values n m zero one add mul neg)))))

(defun putnam-2022-a6-witness-failure-function
    (n m carrier zero one add mul neg lt)
  (list
   'lambda
   '(values)
   (list
    'if
    (putnam-2022-a6-witness-term
     n m carrier zero one add mul neg lt 'values)
    (putnam-2022-a6-quoted nil)
    (putnam-2022-a6-quoted t))))

(defun putnam-2022-a6-witness-exists-p
    (n m carrier zero one add mul neg lt)
  (let ((failure
         (putnam-2022-a6-witness-failure-function
          n m carrier zero one add mul neg lt))
        (always-true
         (putnam-2022-a6-true-function '(values))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun putnambench-putnam-2022-a6-statement
    (n carrier zero one add mul neg inv lt
       square-root evaluate odd-root)
  (implies
   (and
    (posp n)
    (putnam-2022-a6-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root evaluate odd-root))
   (and
    (putnam-2022-a6-witness-exists-p
     n n carrier zero one add mul neg lt)
    (not
     (putnam-2022-a6-witness-exists-p
      n (+ n 1) carrier zero one add mul neg lt)))))

(value-triple :itpeval-statement-checked)
:q
