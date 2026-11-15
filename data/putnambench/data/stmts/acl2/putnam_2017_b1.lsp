;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_b1:
;; two distinct affine lines in the real plane intersect exactly when every
;; nonzero scalar and every point off both lines determine corresponding
;; points on the two lines with the prescribed displacement ratio. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real coefficient domain is presented as a real closed ordered field.
;; The square-root and odd-degree-root laws are the standard algebraic
;; characterization of real closedness. FN-EQUAL against a constant-T
;; function supplies universal quantification over the whole represented
;; field. Every FN-EQUAL operand and coefficient-traversal function is checked
;; to be tame before use.
;;
;; A source affine line {v+t*w | t real}, with w nonzero, is represented by
;; a nontrivial equation a*x+b*y=c. These presentations are bidirectionally
;; equivalent: from w=(wx,wy) take (a,b)=(-wy,wx), and conversely
;; (b,-a) is a nonzero direction for any equation with (a,b) nonzero.
;; Equality of represented line sets is exactly proportionality of the three
;; coefficients, expressed below by the three 2-by-2 minors. Existence of the
;; intersection point and of the two points related by the prescribed scalar
;; is equivalently expressed by the determinant and augmented-minor consistency
;; conditions for two linear equations. Thus no line, real scalar, point, or
;; quantified witness is restricted to a finite or rational carrier.
;; Completeness of real closed fields transfers this first-order affine
;; statement bidirectionally between the represented field and the real
;; numbers.

(defun putnam-2017-b1-quoted (object)
  (list 'quote object))

(defun putnam-2017-b1-apply1-term (function argument)
  (list
   'apply$
   (putnam-2017-b1-quoted function)
   (list 'cons argument nil)))

(defun putnam-2017-b1-apply2-term (function left right)
  (list
   'apply$
   (putnam-2017-b1-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2017-b1-and-term (terms)
  (if (endp terms)
      (putnam-2017-b1-quoted t)
    (list
     'if
     (car terms)
     (putnam-2017-b1-and-term (cdr terms))
     (putnam-2017-b1-quoted nil))))

(defun putnam-2017-b1-or-term (terms)
  (if (endp terms)
      (putnam-2017-b1-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2017-b1-quoted t)
     (putnam-2017-b1-or-term (cdr terms)))))

(defun putnam-2017-b1-not-term (term)
  (list
   'if
   term
   (putnam-2017-b1-quoted nil)
   (putnam-2017-b1-quoted t)))

(defun putnam-2017-b1-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2017-b1-quoted t)))

(defun putnam-2017-b1-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2017-b1-quoted t)))

(defun putnam-2017-b1-carrier-term (carrier element)
  (putnam-2017-b1-apply1-term carrier element))

(defun putnam-2017-b1-operation-term (operation left right)
  (putnam-2017-b1-apply2-term operation left right))

(defun putnam-2017-b1-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2017-b1-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2017-b1-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2017-b1-quoted
    (putnam-2017-b1-all-coefficients-function carrier))
   (putnam-2017-b1-quoted nil)
   coefficients))

(defun putnam-2017-b1-polynomial-term
    (carrier zero coefficients)
  (putnam-2017-b1-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2017-b1-all-coefficients-term
     carrier coefficients)
    (putnam-2017-b1-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2017-b1-quoted 1))
      (putnam-2017-b1-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2017-b1-quoted zero))))))))

(defun putnam-2017-b1-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2017-b1-quoted zero))
         (qone (putnam-2017-b1-quoted one))
         (add-xy
          (putnam-2017-b1-operation-term add x y))
         (add-yz
          (putnam-2017-b1-operation-term add y z))
         (mul-xy
          (putnam-2017-b1-operation-term mul x y))
         (mul-yz
          (putnam-2017-b1-operation-term mul y z))
         (neg-x
          (putnam-2017-b1-apply1-term neg x))
         (inv-x
          (putnam-2017-b1-apply1-term inv x))
         (domain
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term carrier x)
            (putnam-2017-b1-carrier-term carrier y)
            (putnam-2017-b1-carrier-term carrier z))))
         (laws
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term carrier add-xy)
            (putnam-2017-b1-carrier-term carrier mul-xy)
            (putnam-2017-b1-carrier-term carrier neg-x)
            (putnam-2017-b1-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2017-b1-operation-term add add-xy z)
             (putnam-2017-b1-operation-term add x add-yz))
            (list
             'equal
             (putnam-2017-b1-operation-term mul mul-xy z)
             (putnam-2017-b1-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2017-b1-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2017-b1-operation-term mul y x))
            (list
             'equal
             (putnam-2017-b1-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2017-b1-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2017-b1-operation-term mul x qone)
             x)
            (putnam-2017-b1-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2017-b1-implies-term
             (putnam-2017-b1-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2017-b1-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2017-b1-operation-term mul x add-yz)
             (putnam-2017-b1-operation-term
              add
              (putnam-2017-b1-operation-term mul x y)
              (putnam-2017-b1-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2017-b1-implies-term domain laws))))

(defun putnam-2017-b1-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2017-b1-quoted zero))
         (lt-xy
          (putnam-2017-b1-operation-term lt x y))
         (lt-yx
          (putnam-2017-b1-operation-term lt y x))
         (lt-yz
          (putnam-2017-b1-operation-term lt y z))
         (lt-xz
          (putnam-2017-b1-operation-term lt x z))
         (domain
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term carrier x)
            (putnam-2017-b1-carrier-term carrier y)
            (putnam-2017-b1-carrier-term carrier z))))
         (laws
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-not-term
             (putnam-2017-b1-operation-term lt x x))
            (putnam-2017-b1-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2017-b1-implies-term
             (putnam-2017-b1-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2017-b1-implies-term
             lt-xy
             (putnam-2017-b1-operation-term
              lt
              (putnam-2017-b1-operation-term add x z)
              (putnam-2017-b1-operation-term add y z)))
            (putnam-2017-b1-implies-term
             (putnam-2017-b1-and-term
              (list
               (putnam-2017-b1-operation-term lt qzero x)
               (putnam-2017-b1-operation-term lt qzero y)))
             (putnam-2017-b1-operation-term
              lt
              qzero
              (putnam-2017-b1-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2017-b1-implies-term domain laws))))

(defun putnam-2017-b1-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2017-b1-quoted zero))
         (root
          (putnam-2017-b1-apply1-term square-root x))
         (domain
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term carrier x)
            (putnam-2017-b1-not-term
             (putnam-2017-b1-operation-term lt x qzero)))))
         (laws
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term carrier root)
            (list
             'equal
             (putnam-2017-b1-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2017-b1-implies-term domain laws))))

(defun putnam-2017-b1-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2017-b1-quoted zero))
         (domain
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2017-b1-all-coefficients-term
             carrier rest)
            (putnam-2017-b1-carrier-term carrier x))))
         (empty-law
          (putnam-2017-b1-implies-term
           (putnam-2017-b1-carrier-term carrier x)
           (list
            'equal
            (putnam-2017-b1-operation-term
             evaluate
             (putnam-2017-b1-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2017-b1-operation-term
           add
           coefficient
           (putnam-2017-b1-operation-term
            mul
            x
            (putnam-2017-b1-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2017-b1-implies-term
           domain
           (putnam-2017-b1-and-term
            (list
             (putnam-2017-b1-carrier-term
              carrier
              (putnam-2017-b1-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2017-b1-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2017-b1-and-term
      (list empty-law recursive-law)))))

(defun putnam-2017-b1-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2017-b1-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term carrier root)
            (list
             'equal
             (putnam-2017-b1-operation-term
              evaluate coefficients root)
             (putnam-2017-b1-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2017-b1-implies-term domain laws))))

(defun putnam-2017-b1-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate)
  (let* ((field-laws
          (putnam-2017-b1-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2017-b1-true-function '(x y z)))
         (order-laws
          (putnam-2017-b1-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2017-b1-true-function '(x y z)))
         (square-root-laws
          (putnam-2017-b1-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2017-b1-true-function '(x)))
         (evaluation-laws
          (putnam-2017-b1-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2017-b1-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2017-b1-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2017-b1-true-function
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

(defun putnam-2017-b1-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun putnam-2017-b1-negated-value (neg value)
  (apply$ neg (list value)))

(defun putnam-2017-b1-subtracted-value (add neg left right)
  (putnam-2017-b1-binary-value
   add left (putnam-2017-b1-negated-value neg right)))

(defun putnam-2017-b1-line-value
    (add mul a b x y)
  (putnam-2017-b1-binary-value
   add
   (putnam-2017-b1-binary-value mul a x)
   (putnam-2017-b1-binary-value mul b y)))

(defun putnam-2017-b1-point-on-line-p
    (add mul a b c x y)
  (equal
   (putnam-2017-b1-line-value add mul a b x y)
   c))

(defun putnam-2017-b1-line-p
    (carrier zero a b c)
  (and
   (apply$ carrier (list a))
   (apply$ carrier (list b))
   (apply$ carrier (list c))
   (not (and (equal a zero)
             (equal b zero)))))

(defun putnam-2017-b1-same-line-p
    (mul a1 b1 c1 a2 b2 c2)
  (and
   (equal
    (putnam-2017-b1-binary-value mul a1 b2)
    (putnam-2017-b1-binary-value mul a2 b1))
   (equal
    (putnam-2017-b1-binary-value mul a1 c2)
    (putnam-2017-b1-binary-value mul a2 c1))
   (equal
    (putnam-2017-b1-binary-value mul b1 c2)
    (putnam-2017-b1-binary-value mul b2 c1))))

(defun putnam-2017-b1-linear-system-consistent-p
    (mul a1 b1 c1 a2 b2 c2)
  (or
   (not
    (equal
     (putnam-2017-b1-binary-value mul a1 b2)
     (putnam-2017-b1-binary-value mul a2 b1)))
   (putnam-2017-b1-same-line-p
    mul a1 b1 c1 a2 b2 c2)))

(defun putnam-2017-b1-relation-consistent-p
    (one add mul neg
         a1 b1 c1 a2 b2 c2 scalar px py)
  (let* ((one-minus-scalar
          (putnam-2017-b1-subtracted-value
           add neg one scalar))
         (line2-at-p
          (putnam-2017-b1-line-value
           add mul a2 b2 px py))
         (translated-constant
          (putnam-2017-b1-subtracted-value
           add
           neg
           c2
           (putnam-2017-b1-binary-value
            mul one-minus-scalar line2-at-p)))
         (scaled-a2
          (putnam-2017-b1-binary-value
           mul scalar a2))
         (scaled-b2
          (putnam-2017-b1-binary-value
           mul scalar b2)))
    (putnam-2017-b1-linear-system-consistent-p
     mul
     a1 b1 c1
     scaled-a2 scaled-b2 translated-constant)))

(defun putnam-2017-b1-line-value-term
    (add mul a b x y)
  (putnam-2017-b1-operation-term
   add
   (putnam-2017-b1-operation-term mul a x)
   (putnam-2017-b1-operation-term mul b y)))

(defun putnam-2017-b1-point-on-line-term
    (add mul a b c x y)
  (list
   'equal
   (putnam-2017-b1-line-value-term
    add mul a b x y)
   c))

(defun putnam-2017-b1-same-line-term
    (mul a1 b1 c1 a2 b2 c2)
  (putnam-2017-b1-and-term
   (list
    (list
     'equal
     (putnam-2017-b1-operation-term mul a1 b2)
     (putnam-2017-b1-operation-term mul a2 b1))
    (list
     'equal
     (putnam-2017-b1-operation-term mul a1 c2)
     (putnam-2017-b1-operation-term mul a2 c1))
    (list
     'equal
     (putnam-2017-b1-operation-term mul b1 c2)
     (putnam-2017-b1-operation-term mul b2 c1)))))

(defun putnam-2017-b1-linear-system-consistent-term
    (mul a1 b1 c1 a2 b2 c2)
  (putnam-2017-b1-or-term
   (list
    (putnam-2017-b1-not-term
     (list
      'equal
      (putnam-2017-b1-operation-term mul a1 b2)
      (putnam-2017-b1-operation-term mul a2 b1)))
    (putnam-2017-b1-same-line-term
     mul a1 b1 c1 a2 b2 c2))))

(defun putnam-2017-b1-relation-consistent-term
    (one add mul neg
         a1 b1 c1 a2 b2 c2 scalar px py)
  (let* ((one-minus-scalar
          (putnam-2017-b1-operation-term
           add
           one
           (putnam-2017-b1-apply1-term neg scalar)))
         (line2-at-p
          (putnam-2017-b1-line-value-term
           add mul a2 b2 px py))
         (translated-constant
          (putnam-2017-b1-operation-term
           add
           c2
           (putnam-2017-b1-apply1-term
            neg
            (putnam-2017-b1-operation-term
             mul one-minus-scalar line2-at-p))))
         (scaled-a2
          (putnam-2017-b1-operation-term
           mul scalar a2))
         (scaled-b2
          (putnam-2017-b1-operation-term
           mul scalar b2)))
    (putnam-2017-b1-linear-system-consistent-term
     mul
     a1 b1 c1
     scaled-a2 scaled-b2 translated-constant)))

(defun putnam-2017-b1-property-function
    (carrier zero one add mul neg a1 b1 c1 a2 b2 c2)
  (let* ((scalar 'scalar)
         (px 'px)
         (py 'py)
         (qzero (putnam-2017-b1-quoted zero))
         (qone (putnam-2017-b1-quoted one))
         (qa1 (putnam-2017-b1-quoted a1))
         (qb1 (putnam-2017-b1-quoted b1))
         (qc1 (putnam-2017-b1-quoted c1))
         (qa2 (putnam-2017-b1-quoted a2))
         (qb2 (putnam-2017-b1-quoted b2))
         (qc2 (putnam-2017-b1-quoted c2))
         (domain
          (putnam-2017-b1-and-term
           (list
            (putnam-2017-b1-carrier-term
             carrier scalar)
            (putnam-2017-b1-not-term
             (list 'equal scalar qzero))
            (putnam-2017-b1-carrier-term carrier px)
            (putnam-2017-b1-carrier-term carrier py)
            (putnam-2017-b1-not-term
             (putnam-2017-b1-point-on-line-term
              add mul qa1 qb1 qc1 px py))
            (putnam-2017-b1-not-term
             (putnam-2017-b1-point-on-line-term
              add mul qa2 qb2 qc2 px py)))))
         (conclusion
          (putnam-2017-b1-relation-consistent-term
           qone add mul neg
           qa1 qb1 qc1 qa2 qb2 qc2
           scalar px py)))
    (list
     'lambda
     '(scalar px py)
     (putnam-2017-b1-implies-term
      domain conclusion))))

(defun putnam-2017-b1-property-p
    (carrier zero one add mul neg a1 b1 c1 a2 b2 c2)
  (let ((property
         (putnam-2017-b1-property-function
          carrier zero one add mul neg
          a1 b1 c1 a2 b2 c2))
        (always-true
         (putnam-2017-b1-true-function
          '(scalar px py))))
    (and
     (tamep-functionp property)
     (tamep-functionp always-true)
     (fn-equal property always-true))))

(defun putnambench-putnam-2017-b1-statement
    (carrier zero one add mul neg inv lt square-root odd-root evaluate
             a1 b1 c1 a2 b2 c2)
  (implies
   (and
    (putnam-2017-b1-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root evaluate)
    (putnam-2017-b1-line-p carrier zero a1 b1 c1)
    (putnam-2017-b1-line-p carrier zero a2 b2 c2)
    (not
     (putnam-2017-b1-same-line-p
      mul a1 b1 c1 a2 b2 c2)))
   (iff
    (putnam-2017-b1-linear-system-consistent-p
     mul a1 b1 c1 a2 b2 c2)
    (putnam-2017-b1-property-p
     carrier zero one add mul neg
     a1 b1 c1 a2 b2 c2))))

(value-triple :itpeval-statement-checked)
:q
