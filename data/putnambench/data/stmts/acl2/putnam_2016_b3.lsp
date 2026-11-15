;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_b3:
;; every finite planar point set whose member triples have area at most 1 is
;; contained in a triangle of area 4. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are interpreted in an arbitrary real closed ordered field. Real
;; closed fields are elementarily equivalent. For each finite list length,
;; area bounds and triangle containment are first-order ordered-field
;; relations, so a counterexample exists here exactly when one exists over R.
;;
;; A duplicate-free true list represents the finite set extensionally. Twice
;; the Euclidean area of triangle ABC is |det(B-A,C-A)|. A point is in a
;; nondegenerate closed triangle exactly when its three edge determinants all
;; have the same weak sign. Negated FN-EQUAL keeps the enclosing triangle as
;; an internal existential witness rather than a statement parameter.

(defun putnam-2016-b3-quoted (object)
  (list 'quote object))

(defun putnam-2016-b3-apply1-term (function argument)
  (list
   'apply$
   (putnam-2016-b3-quoted function)
   (list 'cons argument nil)))

(defun putnam-2016-b3-apply2-term (function left right)
  (list
   'apply$
   (putnam-2016-b3-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2016-b3-and-term (terms)
  (if (endp terms)
      (putnam-2016-b3-quoted t)
    (list
     'if
     (car terms)
     (putnam-2016-b3-and-term (cdr terms))
     (putnam-2016-b3-quoted nil))))

(defun putnam-2016-b3-or-term (terms)
  (if (endp terms)
      (putnam-2016-b3-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2016-b3-quoted t)
     (putnam-2016-b3-or-term (cdr terms)))))

(defun putnam-2016-b3-not-term (term)
  (list
   'if
   term
   (putnam-2016-b3-quoted nil)
   (putnam-2016-b3-quoted t)))

(defun putnam-2016-b3-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2016-b3-quoted t)))

(defun putnam-2016-b3-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2016-b3-quoted t)))

(defun putnam-2016-b3-carrier-term (carrier element)
  (putnam-2016-b3-apply1-term carrier element))

(defun putnam-2016-b3-operation-term (operation left right)
  (putnam-2016-b3-apply2-term operation left right))

(defun putnam-2016-b3-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2016-b3-carrier-term carrier 'loop$-ivars)))

(defun putnam-2016-b3-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2016-b3-quoted
    (putnam-2016-b3-all-coefficients-function carrier))
   (putnam-2016-b3-quoted nil)
   coefficients))

(defun putnam-2016-b3-polynomial-term
    (carrier zero coefficients)
  (putnam-2016-b3-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2016-b3-all-coefficients-term
     carrier coefficients)
    (putnam-2016-b3-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2016-b3-quoted 1))
      (putnam-2016-b3-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2016-b3-quoted zero))))))))

(defun putnam-2016-b3-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2016-b3-quoted zero))
         (qone (putnam-2016-b3-quoted one))
         (add-xy
          (putnam-2016-b3-operation-term add x y))
         (add-yz
          (putnam-2016-b3-operation-term add y z))
         (mul-xy
          (putnam-2016-b3-operation-term mul x y))
         (mul-yz
          (putnam-2016-b3-operation-term mul y z))
         (neg-x
          (putnam-2016-b3-apply1-term neg x))
         (inv-x
          (putnam-2016-b3-apply1-term inv x))
         (domain
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term carrier x)
            (putnam-2016-b3-carrier-term carrier y)
            (putnam-2016-b3-carrier-term carrier z))))
         (laws
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term carrier add-xy)
            (putnam-2016-b3-carrier-term carrier mul-xy)
            (putnam-2016-b3-carrier-term carrier neg-x)
            (putnam-2016-b3-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2016-b3-operation-term add add-xy z)
             (putnam-2016-b3-operation-term add x add-yz))
            (list
             'equal
             (putnam-2016-b3-operation-term mul mul-xy z)
             (putnam-2016-b3-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2016-b3-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2016-b3-operation-term mul y x))
            (list
             'equal
             (putnam-2016-b3-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2016-b3-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2016-b3-operation-term mul x qone)
             x)
            (putnam-2016-b3-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2016-b3-implies-term
             (putnam-2016-b3-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2016-b3-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2016-b3-operation-term mul x add-yz)
             (putnam-2016-b3-operation-term
              add
              (putnam-2016-b3-operation-term mul x y)
              (putnam-2016-b3-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2016-b3-implies-term domain laws))))

(defun putnam-2016-b3-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2016-b3-quoted zero))
         (lt-xy
          (putnam-2016-b3-operation-term lt x y))
         (lt-yx
          (putnam-2016-b3-operation-term lt y x))
         (lt-yz
          (putnam-2016-b3-operation-term lt y z))
         (lt-xz
          (putnam-2016-b3-operation-term lt x z))
         (domain
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term carrier x)
            (putnam-2016-b3-carrier-term carrier y)
            (putnam-2016-b3-carrier-term carrier z))))
         (laws
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-not-term
             (putnam-2016-b3-operation-term lt x x))
            (putnam-2016-b3-or-term
             (list lt-xy (list 'equal x y) lt-yx))
            (putnam-2016-b3-implies-term
             (putnam-2016-b3-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2016-b3-implies-term
             lt-xy
             (putnam-2016-b3-operation-term
              lt
              (putnam-2016-b3-operation-term add x z)
              (putnam-2016-b3-operation-term add y z)))
            (putnam-2016-b3-implies-term
             (putnam-2016-b3-and-term
              (list
               (putnam-2016-b3-operation-term lt qzero x)
               (putnam-2016-b3-operation-term lt qzero y)))
             (putnam-2016-b3-operation-term
              lt
              qzero
              (putnam-2016-b3-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2016-b3-implies-term domain laws))))

(defun putnam-2016-b3-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2016-b3-quoted zero))
         (root
          (putnam-2016-b3-apply1-term square-root x))
         (domain
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term carrier x)
            (putnam-2016-b3-not-term
             (putnam-2016-b3-operation-term lt x qzero)))))
         (laws
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term carrier root)
            (list
             'equal
             (putnam-2016-b3-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2016-b3-implies-term domain laws))))

(defun putnam-2016-b3-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2016-b3-quoted zero))
         (domain
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2016-b3-all-coefficients-term
             carrier rest)
            (putnam-2016-b3-carrier-term carrier x))))
         (empty-law
          (putnam-2016-b3-implies-term
           (putnam-2016-b3-carrier-term carrier x)
           (list
            'equal
            (putnam-2016-b3-operation-term
             evaluate
             (putnam-2016-b3-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2016-b3-operation-term
           add
           coefficient
           (putnam-2016-b3-operation-term
            mul
            x
            (putnam-2016-b3-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2016-b3-implies-term
           domain
           (putnam-2016-b3-and-term
            (list
             (putnam-2016-b3-carrier-term
              carrier
              (putnam-2016-b3-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2016-b3-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2016-b3-and-term
      (list empty-law recursive-law)))))

(defun putnam-2016-b3-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2016-b3-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2016-b3-and-term
           (list
            (putnam-2016-b3-carrier-term carrier root)
            (list
             'equal
             (putnam-2016-b3-operation-term
              evaluate coefficients root)
             (putnam-2016-b3-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2016-b3-implies-term domain laws))))

(defun putnam-2016-b3-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2016-b3-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2016-b3-true-function '(x y z)))
         (order-laws
          (putnam-2016-b3-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2016-b3-true-function '(x y z)))
         (square-root-laws
          (putnam-2016-b3-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2016-b3-true-function '(x)))
         (evaluation-laws
          (putnam-2016-b3-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2016-b3-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2016-b3-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2016-b3-true-function
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

(defun putnam-2016-b3-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2016-b3-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2016-b3-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2016-b3-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2016-b3-lt (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2016-b3-le (lt left right)
  (not (putnam-2016-b3-lt lt right left)))

(defun putnam-2016-b3-sub (add neg left right)
  (putnam-2016-b3-add
   add left (putnam-2016-b3-neg neg right)))

(defun putnam-2016-b3-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2016-b3-add
     add
     one
     (putnam-2016-b3-field-natural
      (- n 1) zero one add))))

(defun putnam-2016-b3-abs
    (value zero neg lt)
  (if (putnam-2016-b3-lt lt value zero)
      (putnam-2016-b3-neg neg value)
    value))

(defun putnam-2016-b3-point-p (point carrier)
  (and
   (true-listp point)
   (equal (len point) 2)
   (apply$ carrier (list (nth 0 point)))
   (apply$ carrier (list (nth 1 point)))))

(defun putnam-2016-b3-finite-point-set-p
    (points carrier)
  (if (consp points)
      (and
       (putnam-2016-b3-point-p (car points) carrier)
       (not (member-equal (car points) (cdr points)))
       (putnam-2016-b3-finite-point-set-p
        (cdr points) carrier))
    (equal points nil)))

(defun putnam-2016-b3-determinant
    (a b c add mul neg)
  (putnam-2016-b3-sub
   add neg
   (putnam-2016-b3-mul
    mul
    (putnam-2016-b3-sub
     add neg (nth 0 b) (nth 0 a))
    (putnam-2016-b3-sub
     add neg (nth 1 c) (nth 1 a)))
   (putnam-2016-b3-mul
    mul
    (putnam-2016-b3-sub
     add neg (nth 1 b) (nth 1 a))
    (putnam-2016-b3-sub
     add neg (nth 0 c) (nth 0 a)))))

(defun putnam-2016-b3-area-at-most-one-p
    (a b c zero one add mul neg lt)
  (putnam-2016-b3-le
   lt
   (putnam-2016-b3-abs
    (putnam-2016-b3-determinant
     a b c add mul neg)
    zero neg lt)
   (putnam-2016-b3-field-natural
    2 zero one add)))

(defun putnam-2016-b3-all-third-points-p
    (a b third-points zero one add mul neg lt)
  (if (consp third-points)
      (and
       (putnam-2016-b3-area-at-most-one-p
        a b (car third-points)
        zero one add mul neg lt)
       (putnam-2016-b3-all-third-points-p
        a b (cdr third-points)
        zero one add mul neg lt))
    (equal third-points nil)))

(defun putnam-2016-b3-all-second-third-points-p
    (a second-points all-points zero one add mul neg lt)
  (if (consp second-points)
      (and
       (putnam-2016-b3-all-third-points-p
        a (car second-points) all-points
        zero one add mul neg lt)
       (putnam-2016-b3-all-second-third-points-p
        a (cdr second-points) all-points
        zero one add mul neg lt))
    (equal second-points nil)))

(defun putnam-2016-b3-all-triples-p
    (first-points all-points zero one add mul neg lt)
  (if (consp first-points)
      (and
       (putnam-2016-b3-all-second-third-points-p
        (car first-points) all-points all-points
        zero one add mul neg lt)
       (putnam-2016-b3-all-triples-p
        (cdr first-points) all-points
        zero one add mul neg lt))
    (equal first-points nil)))

(defun putnam-2016-b3-same-weak-sign-p
    (x y z zero lt)
  (or
   (and
    (putnam-2016-b3-le lt zero x)
    (putnam-2016-b3-le lt zero y)
    (putnam-2016-b3-le lt zero z))
   (and
    (putnam-2016-b3-le lt x zero)
    (putnam-2016-b3-le lt y zero)
    (putnam-2016-b3-le lt z zero))))

(defun putnam-2016-b3-point-in-triangle-p
    (point a b c zero add mul neg lt)
  (putnam-2016-b3-same-weak-sign-p
   (putnam-2016-b3-determinant
    a b point add mul neg)
   (putnam-2016-b3-determinant
    b c point add mul neg)
   (putnam-2016-b3-determinant
    c a point add mul neg)
   zero lt))

(defun putnam-2016-b3-all-points-contained-p
    (points a b c zero add mul neg lt)
  (if (consp points)
      (and
       (putnam-2016-b3-point-in-triangle-p
        (car points) a b c zero add mul neg lt)
       (putnam-2016-b3-all-points-contained-p
        (cdr points) a b c zero add mul neg lt))
    (equal points nil)))

(defun putnam-2016-b3-enclosing-triangle-p
    (witness points carrier zero one add mul neg lt)
  (and
   (true-listp witness)
   (equal (len witness) 3)
   (putnam-2016-b3-point-p (nth 0 witness) carrier)
   (putnam-2016-b3-point-p (nth 1 witness) carrier)
   (putnam-2016-b3-point-p (nth 2 witness) carrier)
   (equal
    (putnam-2016-b3-abs
     (putnam-2016-b3-determinant
      (nth 0 witness)
      (nth 1 witness)
      (nth 2 witness)
      add mul neg)
     zero neg lt)
    (putnam-2016-b3-field-natural
     8 zero one add))
   (putnam-2016-b3-all-points-contained-p
    points
    (nth 0 witness)
    (nth 1 witness)
    (nth 2 witness)
    zero add mul neg lt)))

(defun putnam-2016-b3-car-term (term)
  (list 'car term))

(defun putnam-2016-b3-cdr-term (term)
  (list 'cdr term))

(defun putnam-2016-b3-add-term (add left right)
  (putnam-2016-b3-operation-term add left right))

(defun putnam-2016-b3-mul-term (mul left right)
  (putnam-2016-b3-operation-term mul left right))

(defun putnam-2016-b3-neg-term (neg value)
  (putnam-2016-b3-apply1-term neg value))

(defun putnam-2016-b3-lt-term (lt left right)
  (putnam-2016-b3-operation-term lt left right))

(defun putnam-2016-b3-le-term (lt left right)
  (putnam-2016-b3-not-term
   (putnam-2016-b3-lt-term lt right left)))

(defun putnam-2016-b3-sub-term (add neg left right)
  (putnam-2016-b3-add-term
   add
   left
   (putnam-2016-b3-neg-term neg right)))

(defun putnam-2016-b3-abs-term (zero neg lt value)
  (list
   'if
   (putnam-2016-b3-lt-term
    lt value (putnam-2016-b3-quoted zero))
   (putnam-2016-b3-neg-term neg value)
   value))

(defun putnam-2016-b3-point-term (point carrier)
  (let ((tail (putnam-2016-b3-cdr-term point)))
    (putnam-2016-b3-and-term
     (list
      (list 'consp point)
      (list 'consp tail)
      (list
       'equal
       (putnam-2016-b3-cdr-term tail)
       (putnam-2016-b3-quoted nil))
      (putnam-2016-b3-apply1-term
       carrier
       (putnam-2016-b3-car-term point))
      (putnam-2016-b3-apply1-term
       carrier
       (putnam-2016-b3-car-term tail))))))

(defun putnam-2016-b3-determinant-term (a b c add mul neg)
  (let ((a-tail (putnam-2016-b3-cdr-term a))
        (b-tail (putnam-2016-b3-cdr-term b))
        (c-tail (putnam-2016-b3-cdr-term c)))
    (putnam-2016-b3-sub-term
     add
     neg
     (putnam-2016-b3-mul-term
      mul
      (putnam-2016-b3-sub-term
       add
       neg
       (putnam-2016-b3-car-term b)
       (putnam-2016-b3-car-term a))
      (putnam-2016-b3-sub-term
       add
       neg
       (putnam-2016-b3-car-term c-tail)
       (putnam-2016-b3-car-term a-tail)))
     (putnam-2016-b3-mul-term
      mul
      (putnam-2016-b3-sub-term
       add
       neg
       (putnam-2016-b3-car-term b-tail)
       (putnam-2016-b3-car-term a-tail))
      (putnam-2016-b3-sub-term
       add
       neg
       (putnam-2016-b3-car-term c)
       (putnam-2016-b3-car-term a))))))

(defun putnam-2016-b3-same-weak-sign-term
    (x y z zero lt)
  (putnam-2016-b3-or-term
   (list
    (putnam-2016-b3-and-term
     (list
      (putnam-2016-b3-le-term
       lt (putnam-2016-b3-quoted zero) x)
      (putnam-2016-b3-le-term
       lt (putnam-2016-b3-quoted zero) y)
      (putnam-2016-b3-le-term
       lt (putnam-2016-b3-quoted zero) z)))
    (putnam-2016-b3-and-term
     (list
      (putnam-2016-b3-le-term
       lt x (putnam-2016-b3-quoted zero))
      (putnam-2016-b3-le-term
       lt y (putnam-2016-b3-quoted zero))
      (putnam-2016-b3-le-term
       lt z (putnam-2016-b3-quoted zero)))))))

(defun putnam-2016-b3-point-in-triangle-term
    (point a b c zero add mul neg lt)
  (putnam-2016-b3-same-weak-sign-term
   (putnam-2016-b3-determinant-term
    a b point add mul neg)
   (putnam-2016-b3-determinant-term
    b c point add mul neg)
   (putnam-2016-b3-determinant-term
    c a point add mul neg)
   zero
   lt))

(defun putnam-2016-b3-all-points-contained-term
    (points a b c zero add mul neg lt)
  (if (consp points)
      (putnam-2016-b3-and-term
       (list
        (putnam-2016-b3-point-in-triangle-term
         (putnam-2016-b3-quoted (car points))
         a b c zero add mul neg lt)
        (putnam-2016-b3-all-points-contained-term
         (cdr points) a b c zero add mul neg lt)))
    (putnam-2016-b3-quoted t)))

(defun putnam-2016-b3-enclosing-triangle-failure-function
    (points carrier zero one add mul neg lt)
  (let* ((witness 'witness)
         (witness-tail
          (putnam-2016-b3-cdr-term witness))
         (witness-tail-tail
          (putnam-2016-b3-cdr-term witness-tail))
         (a (putnam-2016-b3-car-term witness))
         (b (putnam-2016-b3-car-term witness-tail))
         (c (putnam-2016-b3-car-term witness-tail-tail))
         (determinant
          (putnam-2016-b3-determinant-term
           a b c add mul neg))
         (qualification
          (putnam-2016-b3-and-term
           (list
            (list 'consp witness)
            (list 'consp witness-tail)
            (list 'consp witness-tail-tail)
            (list
             'equal
             (putnam-2016-b3-cdr-term witness-tail-tail)
             (putnam-2016-b3-quoted nil))
            (putnam-2016-b3-point-term a carrier)
            (putnam-2016-b3-point-term b carrier)
            (putnam-2016-b3-point-term c carrier)
            (list
             'equal
             (putnam-2016-b3-abs-term
              zero neg lt determinant)
             (putnam-2016-b3-quoted
              (putnam-2016-b3-field-natural
               8 zero one add)))
            (putnam-2016-b3-all-points-contained-term
             points a b c zero add mul neg lt)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2016-b3-quoted nil)
      (putnam-2016-b3-quoted t)))))

(defun putnam-2016-b3-sample-failure-function-tame-p ()
  (tamep-functionp
   (putnam-2016-b3-enclosing-triangle-failure-function
    '((0 0))
    (putnam-2016-b3-true-function '(x))
    0
    1
    'binary-+
    'binary-*
    'unary--
    '<)))

(defun putnam-2016-b3-enclosing-triangle-exists-p
    (points carrier zero one add mul neg lt)
  (let ((failure-function
         (putnam-2016-b3-enclosing-triangle-failure-function
          points carrier zero one add mul neg lt))
        (true-function
         (putnam-2016-b3-true-function '(witness))))
    (and
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

(defun putnambench-putnam-2016-b3-statement
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate points)
  (implies
   (and
    (putnam-2016-b3-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate)
    (putnam-2016-b3-finite-point-set-p
     points carrier)
    (putnam-2016-b3-all-triples-p
     points points zero one add mul neg lt))
   (putnam-2016-b3-enclosing-triangle-exists-p
    points carrier zero one add mul neg lt)))

(value-triple
 (if (putnam-2016-b3-sample-failure-function-tame-p)
     :itpeval-tame-function-checked
   (er hard
       'putnam-2016-b3-sample-failure-function-tame-p
       "The generated enclosing-triangle failure function is not tame."
       nil)))

(value-triple :itpeval-statement-checked)
:q
