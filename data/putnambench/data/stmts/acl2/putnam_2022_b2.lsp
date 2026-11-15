;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_b2:
;; the positive cardinalities of finite subsets of real three-space that are
;; exactly closed under taking all pairwise cross products are 1 and 7. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar domain is presented as a real closed ordered field. Completeness
;; of the first-order theory of real closed fields transfers this finite
;; algebraic assertion bidirectionally between the presentation and the real
;; numbers. A vector is a length-three field list.
;;
;; A duplicate-free list represents the finite set extensionally. The two
;; inclusions below say exactly that this set equals the set of all v cross w
;; with v and w in the set. NOT/FN-EQUAL keeps the finite-set witness internal
;; rather than adding it as a parameter of the root statement.

(defun putnam-2022-b2-quoted (object)
  (list 'quote object))

(defun putnam-2022-b2-apply1-term (function argument)
  (list
   'apply$
   (putnam-2022-b2-quoted function)
   (list 'cons argument nil)))

(defun putnam-2022-b2-apply2-term (function left right)
  (list
   'apply$
   (putnam-2022-b2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2022-b2-and-term (terms)
  (if (endp terms)
      (putnam-2022-b2-quoted t)
    (list
     'if
     (car terms)
     (putnam-2022-b2-and-term (cdr terms))
     (putnam-2022-b2-quoted nil))))

(defun putnam-2022-b2-or-term (terms)
  (if (endp terms)
      (putnam-2022-b2-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2022-b2-quoted t)
     (putnam-2022-b2-or-term (cdr terms)))))

(defun putnam-2022-b2-not-term (term)
  (list
   'if
   term
   (putnam-2022-b2-quoted nil)
   (putnam-2022-b2-quoted t)))

(defun putnam-2022-b2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2022-b2-quoted t)))

(defun putnam-2022-b2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2022-b2-quoted t)))

(defun putnam-2022-b2-carrier-term (carrier element)
  (putnam-2022-b2-apply1-term carrier element))

(defun putnam-2022-b2-operation-term (operation left right)
  (putnam-2022-b2-apply2-term operation left right))

(defun putnam-2022-b2-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2022-b2-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2022-b2-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2022-b2-quoted
    (putnam-2022-b2-all-coefficients-function
     carrier))
   (putnam-2022-b2-quoted nil)
   coefficients))

(defun putnam-2022-b2-polynomial-term
    (carrier zero coefficients)
  (putnam-2022-b2-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2022-b2-all-coefficients-term
     carrier coefficients)
    (putnam-2022-b2-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2022-b2-quoted 1))
      (putnam-2022-b2-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2022-b2-quoted zero))))))))

(defun putnam-2022-b2-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2022-b2-quoted zero))
         (qone (putnam-2022-b2-quoted one))
         (add-xy
          (putnam-2022-b2-operation-term add x y))
         (add-yz
          (putnam-2022-b2-operation-term add y z))
         (mul-xy
          (putnam-2022-b2-operation-term mul x y))
         (mul-yz
          (putnam-2022-b2-operation-term mul y z))
         (neg-x
          (putnam-2022-b2-apply1-term neg x))
         (inv-x
          (putnam-2022-b2-apply1-term inv x))
         (domain
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term carrier x)
            (putnam-2022-b2-carrier-term carrier y)
            (putnam-2022-b2-carrier-term carrier z))))
         (laws
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term carrier add-xy)
            (putnam-2022-b2-carrier-term carrier mul-xy)
            (putnam-2022-b2-carrier-term carrier neg-x)
            (putnam-2022-b2-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2022-b2-operation-term add add-xy z)
             (putnam-2022-b2-operation-term add x add-yz))
            (list
             'equal
             (putnam-2022-b2-operation-term mul mul-xy z)
             (putnam-2022-b2-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2022-b2-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2022-b2-operation-term mul y x))
            (list
             'equal
             (putnam-2022-b2-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2022-b2-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2022-b2-operation-term mul x qone)
             x)
            (putnam-2022-b2-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2022-b2-implies-term
             (putnam-2022-b2-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2022-b2-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2022-b2-operation-term mul x add-yz)
             (putnam-2022-b2-operation-term
              add
              (putnam-2022-b2-operation-term mul x y)
              (putnam-2022-b2-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2022-b2-implies-term domain laws))))

(defun putnam-2022-b2-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2022-b2-quoted zero))
         (lt-xy
          (putnam-2022-b2-operation-term lt x y))
         (lt-yx
          (putnam-2022-b2-operation-term lt y x))
         (lt-yz
          (putnam-2022-b2-operation-term lt y z))
         (lt-xz
          (putnam-2022-b2-operation-term lt x z))
         (domain
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term carrier x)
            (putnam-2022-b2-carrier-term carrier y)
            (putnam-2022-b2-carrier-term carrier z))))
         (laws
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-not-term
             (putnam-2022-b2-operation-term lt x x))
            (putnam-2022-b2-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2022-b2-implies-term
             (putnam-2022-b2-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2022-b2-implies-term
             lt-xy
             (putnam-2022-b2-operation-term
              lt
              (putnam-2022-b2-operation-term add x z)
              (putnam-2022-b2-operation-term add y z)))
            (putnam-2022-b2-implies-term
             (putnam-2022-b2-and-term
              (list
               (putnam-2022-b2-operation-term lt qzero x)
               (putnam-2022-b2-operation-term lt qzero y)))
             (putnam-2022-b2-operation-term
              lt
              qzero
              (putnam-2022-b2-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2022-b2-implies-term domain laws))))

(defun putnam-2022-b2-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2022-b2-quoted zero))
         (root
          (putnam-2022-b2-apply1-term square-root x))
         (domain
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term carrier x)
            (putnam-2022-b2-not-term
             (putnam-2022-b2-operation-term lt x qzero)))))
         (laws
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term carrier root)
            (list
             'equal
             (putnam-2022-b2-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2022-b2-implies-term domain laws))))

(defun putnam-2022-b2-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2022-b2-quoted zero))
         (domain
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2022-b2-all-coefficients-term
             carrier rest)
            (putnam-2022-b2-carrier-term carrier x))))
         (empty-law
          (putnam-2022-b2-implies-term
           (putnam-2022-b2-carrier-term carrier x)
           (list
            'equal
            (putnam-2022-b2-operation-term
             evaluate
             (putnam-2022-b2-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2022-b2-operation-term
           add
           coefficient
           (putnam-2022-b2-operation-term
            mul
            x
            (putnam-2022-b2-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2022-b2-implies-term
           domain
           (putnam-2022-b2-and-term
            (list
             (putnam-2022-b2-carrier-term
              carrier
              (putnam-2022-b2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2022-b2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2022-b2-and-term
      (list empty-law recursive-law)))))

(defun putnam-2022-b2-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2022-b2-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2022-b2-and-term
           (list
            (putnam-2022-b2-carrier-term carrier root)
            (list
             'equal
             (putnam-2022-b2-operation-term
              evaluate coefficients root)
             (putnam-2022-b2-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2022-b2-implies-term domain laws))))

(defun putnam-2022-b2-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2022-b2-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2022-b2-true-function '(x y z)))
         (order-laws
          (putnam-2022-b2-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2022-b2-true-function '(x y z)))
         (square-root-laws
          (putnam-2022-b2-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2022-b2-true-function '(x)))
         (evaluation-laws
          (putnam-2022-b2-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2022-b2-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2022-b2-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2022-b2-true-function
           '(coefficients)))
         (all-coefficients-loop
          (putnam-2022-b2-all-coefficients-function
           carrier)))
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
     (tamep-functionp all-coefficients-loop)
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

(defun putnam-2022-b2-first-term (vector)
  (list 'car vector))

(defun putnam-2022-b2-second-term (vector)
  (list 'car (list 'cdr vector)))

(defun putnam-2022-b2-third-term (vector)
  (list 'car (list 'cdr (list 'cdr vector))))

(defun putnam-2022-b2-vector-term (field-carrier vector)
  (putnam-2022-b2-and-term
   (list
    (list 'true-listp vector)
    (list
     'equal
     (list 'len vector)
     (putnam-2022-b2-quoted 3))
    (putnam-2022-b2-carrier-term
     field-carrier
     (putnam-2022-b2-first-term vector))
    (putnam-2022-b2-carrier-term
     field-carrier
     (putnam-2022-b2-second-term vector))
    (putnam-2022-b2-carrier-term
     field-carrier
     (putnam-2022-b2-third-term vector)))))

(defun putnam-2022-b2-difference-term
    (add mul neg left-a left-b right-a right-b)
  (putnam-2022-b2-operation-term
   add
   (putnam-2022-b2-operation-term
    mul left-a left-b)
   (putnam-2022-b2-apply1-term
    neg
    (putnam-2022-b2-operation-term
     mul right-a right-b))))

(defun putnam-2022-b2-cross-term
    (add mul neg left right)
  (let ((left-0 (putnam-2022-b2-first-term left))
        (left-1 (putnam-2022-b2-second-term left))
        (left-2 (putnam-2022-b2-third-term left))
        (right-0 (putnam-2022-b2-first-term right))
        (right-1 (putnam-2022-b2-second-term right))
        (right-2 (putnam-2022-b2-third-term right)))
    (list
     'cons
     (putnam-2022-b2-difference-term
      add mul neg left-1 right-2 left-2 right-1)
     (list
      'cons
      (putnam-2022-b2-difference-term
       add mul neg left-2 right-0 left-0 right-2)
      (list
       'cons
       (putnam-2022-b2-difference-term
        add mul neg left-0 right-1 left-1 right-0)
       nil)))))

(defun putnam-2022-b2-vector-p (vector field-carrier)
  (and
   (true-listp vector)
   (equal (len vector) 3)
   (apply$ field-carrier (list (nth 0 vector)))
   (apply$ field-carrier (list (nth 1 vector)))
   (apply$ field-carrier (list (nth 2 vector)))))

(defun putnam-2022-b2-vector-list-p
    (vectors field-carrier)
  (if (endp vectors)
      (equal vectors nil)
    (and
     (putnam-2022-b2-vector-p
      (car vectors) field-carrier)
     (putnam-2022-b2-vector-list-p
      (cdr vectors) field-carrier))))

(defun putnam-2022-b2-scalar-difference
    (add mul neg left-a left-b right-a right-b)
  (apply$
   add
   (list
    (apply$ mul (list left-a left-b))
    (apply$
     neg
     (list
      (apply$ mul (list right-a right-b)))))))

(defun putnam-2022-b2-cross
    (left right add mul neg)
  (list
   (putnam-2022-b2-scalar-difference
    add mul neg
    (nth 1 left) (nth 2 right)
    (nth 2 left) (nth 1 right))
   (putnam-2022-b2-scalar-difference
    add mul neg
    (nth 2 left) (nth 0 right)
    (nth 0 left) (nth 2 right))
   (putnam-2022-b2-scalar-difference
    add mul neg
    (nth 0 left) (nth 1 right)
    (nth 1 left) (nth 0 right))))

;; Every pairwise cross product belongs to the represented set.
(defun putnam-2022-b2-cross-with-all-in-set-p
    (left rights set add mul neg)
  (if (endp rights)
      (equal rights nil)
    (and
     (member-equal
      (putnam-2022-b2-cross
       left (car rights) add mul neg)
      set)
     (putnam-2022-b2-cross-with-all-in-set-p
      left (cdr rights) set add mul neg))))

(defun putnam-2022-b2-all-crosses-in-set-p
    (lefts set add mul neg)
  (if (endp lefts)
      (equal lefts nil)
    (and
     (putnam-2022-b2-cross-with-all-in-set-p
      (car lefts) set set add mul neg)
     (putnam-2022-b2-all-crosses-in-set-p
      (cdr lefts) set add mul neg))))

;; Every represented-set element is the cross product of two represented-set
;; elements, giving the reverse inclusion.
(defun putnam-2022-b2-cross-from-left-exists-p
    (target left rights add mul neg)
  (if (endp rights)
      nil
    (or
     (equal
      target
      (putnam-2022-b2-cross
       left (car rights) add mul neg))
     (putnam-2022-b2-cross-from-left-exists-p
      target left (cdr rights) add mul neg))))

(defun putnam-2022-b2-cross-preimage-exists-p
    (target lefts set add mul neg)
  (if (endp lefts)
      nil
    (or
     (putnam-2022-b2-cross-from-left-exists-p
      target (car lefts) set add mul neg)
     (putnam-2022-b2-cross-preimage-exists-p
      target (cdr lefts) set add mul neg))))

(defun putnam-2022-b2-all-elements-have-preimage-p
    (elements set add mul neg)
  (if (endp elements)
      (equal elements nil)
    (and
     (putnam-2022-b2-cross-preimage-exists-p
      (car elements) set set add mul neg)
     (putnam-2022-b2-all-elements-have-preimage-p
      (cdr elements) set add mul neg))))

(defun putnam-2022-b2-set-witness-p
    (set n field-carrier add mul neg)
  (and
   (true-listp set)
   (no-duplicatesp-equal set)
   (equal (len set) n)
   (putnam-2022-b2-vector-list-p set field-carrier)
   (putnam-2022-b2-all-crosses-in-set-p
    set set add mul neg)
   (putnam-2022-b2-all-elements-have-preimage-p
    set set add mul neg)))

;; The FN-EQUAL witness is a three-part certificate:
;;
;;   (set ordered-pairs preimages).
;;
;; ORDERED-PAIRS is a duplicate-free list of |SET|^2 valid pairs, hence an
;; enumeration of every ordered pair from SET. PREIMAGES contains |SET|
;; records (target left right), with distinct targets, so it supplies exactly
;; one cross-product preimage for every element of SET. This finite
;; certificate is definitionally equivalent to the two recursive inclusions
;; above, while every lambda evaluated by FN-EQUAL contains primitives only.

(defun putnam-2022-b2-list-term (terms)
  (if (endp terms)
      (putnam-2022-b2-quoted nil)
    (list
     'cons
     (car terms)
     (putnam-2022-b2-list-term (cdr terms)))))

(defun putnam-2022-b2-vector-loop-function
    (field-carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2022-b2-vector-term
    field-carrier 'loop$-ivars)))

(defun putnam-2022-b2-pair-closure-loop-function
    (add mul neg)
  (let* ((pair 'loop$-ivars)
         (set '(car loop$-gvars))
         (left (putnam-2022-b2-first-term pair))
         (right (putnam-2022-b2-second-term pair)))
    (list
     'lambda
     '(loop$-gvars loop$-ivars)
     (putnam-2022-b2-and-term
      (list
       (list 'true-listp pair)
       (list
        'equal
        (list 'len pair)
        (putnam-2022-b2-quoted 2))
       (list 'member-equal left set)
       (list 'member-equal right set)
       (list
        'member-equal
        (putnam-2022-b2-cross-term
         add mul neg left right)
        set))))))

(defun putnam-2022-b2-preimage-loop-function
    (add mul neg)
  (let* ((record 'loop$-ivars)
         (set '(car loop$-gvars))
         (target (putnam-2022-b2-first-term record))
         (left (putnam-2022-b2-second-term record))
         (right (putnam-2022-b2-third-term record)))
    (list
     'lambda
     '(loop$-gvars loop$-ivars)
     (putnam-2022-b2-and-term
      (list
       (list 'true-listp record)
       (list
        'equal
        (list 'len record)
        (putnam-2022-b2-quoted 3))
       (list 'member-equal target set)
       (list 'member-equal left set)
       (list 'member-equal right set)
       (list
        'equal
        target
        (putnam-2022-b2-cross-term
         add mul neg left right)))))))

(defun putnam-2022-b2-all-vectors-term
    (field-carrier set)
  (list
   'always$+
   (putnam-2022-b2-quoted
    (putnam-2022-b2-vector-loop-function
     field-carrier))
   (putnam-2022-b2-quoted nil)
   set))

(defun putnam-2022-b2-all-pairs-close-term
    (set ordered-pairs add mul neg)
  (list
   'always$+
   (putnam-2022-b2-quoted
    (putnam-2022-b2-pair-closure-loop-function
     add mul neg))
   (putnam-2022-b2-list-term (list set))
   ordered-pairs))

(defun putnam-2022-b2-all-preimages-valid-term
    (set preimages add mul neg)
  (list
   'always$+
   (putnam-2022-b2-quoted
    (putnam-2022-b2-preimage-loop-function
     add mul neg))
   (putnam-2022-b2-list-term (list set))
   preimages))

(defun putnam-2022-b2-set-failure-function
    (n field-carrier add mul neg)
  (let* ((set '(car witness))
         (ordered-pairs '(car (cdr witness)))
         (preimages '(car (cdr (cdr witness))))
         (set-size (list 'len set))
         (qualification
          (putnam-2022-b2-and-term
           (list
            '(true-listp witness)
            '(equal (len witness) '3)
            (list 'true-listp set)
            (list 'no-duplicatesp-equal set)
            (list
             'equal
             set-size
             (putnam-2022-b2-quoted n))
            (putnam-2022-b2-all-vectors-term
             field-carrier set)
            (list 'true-listp ordered-pairs)
            (list 'no-duplicatesp-equal ordered-pairs)
            (list
             'equal
             (list 'len ordered-pairs)
             (list 'binary-* set-size set-size))
            (putnam-2022-b2-all-pairs-close-term
             set ordered-pairs add mul neg)
            (list 'true-listp preimages)
            (list
             'equal
             (list 'len preimages)
             set-size)
            (list
             'no-duplicatesp-equal
             (list 'strip-cars preimages))
            (putnam-2022-b2-all-preimages-valid-term
             set preimages add mul neg)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2022-b2-quoted nil)
      (putnam-2022-b2-quoted t)))))

(defun putnam-2022-b2-set-exists-p
    (n field-carrier add mul neg)
  (let ((failure-function
         (putnam-2022-b2-set-failure-function
          n field-carrier add mul neg))
        (true-function
         (putnam-2022-b2-true-function '(witness))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not
      (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2022-b2-statement
    (n field-carrier zero one add mul neg field-inverse lt
       square-root odd-root evaluate)
  (implies
   (putnam-2022-b2-real-closed-field-p
    field-carrier zero one add mul neg field-inverse lt
    square-root odd-root evaluate)
   (iff
    (and
     (natp n)
     (< 0 n)
     (putnam-2022-b2-set-exists-p
      n field-carrier add mul neg))
    (or
     (equal n 1)
     (equal n 7)))))

(value-triple :itpeval-statement-checked)
:q
