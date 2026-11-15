;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_a4:
;; pointwise absolute-value domination of two real quadratic polynomials
;; implies domination of the absolute values of their discriminants. This
;; file contains no proof.

(in-package "ACL2")

;; The source theorem is a first-order sentence over the real ordered field.
;; We present its domain as an arbitrary real closed ordered field. The square
;; root and odd-degree-root laws below are the standard algebraic
;; characterization of real closedness, so completeness of real closed fields
;; makes this presentation bidirectionally equivalent to the source statement
;; over the reals. ACL2 function objects supply the field operations, and
;; FN-EQUAL against a constant-T function preserves the internal universal
;; quantifier over every real x in the pointwise hypothesis.

(defun putnam-2003-a4-quoted (object)
  (list 'quote object))

(defun putnam-2003-a4-apply1-term (function argument)
  (list
   'apply$
   (putnam-2003-a4-quoted function)
   (list 'cons argument nil)))

(defun putnam-2003-a4-apply2-term (function left right)
  (list
   'apply$
   (putnam-2003-a4-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2003-a4-and-term (terms)
  (if (endp terms)
      (putnam-2003-a4-quoted t)
    (list
     'if
     (car terms)
     (putnam-2003-a4-and-term (cdr terms))
     (putnam-2003-a4-quoted nil))))

(defun putnam-2003-a4-or-term (terms)
  (if (endp terms)
      (putnam-2003-a4-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2003-a4-quoted t)
     (putnam-2003-a4-or-term (cdr terms)))))

(defun putnam-2003-a4-not-term (term)
  (list
   'if
   term
   (putnam-2003-a4-quoted nil)
   (putnam-2003-a4-quoted t)))

(defun putnam-2003-a4-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2003-a4-quoted t)))

(defun putnam-2003-a4-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2003-a4-quoted t)))

(defun putnam-2003-a4-carrier-term (carrier element)
  (putnam-2003-a4-apply1-term carrier element))

(defun putnam-2003-a4-operation-term (operation left right)
  (putnam-2003-a4-apply2-term operation left right))

(defun putnam-2003-a4-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2003-a4-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2003-a4-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2003-a4-quoted
    (putnam-2003-a4-all-coefficients-function
     carrier))
   (putnam-2003-a4-quoted nil)
   coefficients))

(defun putnam-2003-a4-polynomial-term
    (carrier zero coefficients)
  (putnam-2003-a4-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2003-a4-all-coefficients-term
     carrier coefficients)
    (putnam-2003-a4-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2003-a4-quoted 1))
      (putnam-2003-a4-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2003-a4-quoted zero))))))))

(defun putnam-2003-a4-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2003-a4-quoted zero))
         (qone (putnam-2003-a4-quoted one))
         (add-xy
          (putnam-2003-a4-operation-term add x y))
         (add-yz
          (putnam-2003-a4-operation-term add y z))
         (mul-xy
          (putnam-2003-a4-operation-term mul x y))
         (mul-yz
          (putnam-2003-a4-operation-term mul y z))
         (neg-x
          (putnam-2003-a4-apply1-term neg x))
         (inv-x
          (putnam-2003-a4-apply1-term inv x))
         (domain
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term carrier x)
            (putnam-2003-a4-carrier-term carrier y)
            (putnam-2003-a4-carrier-term carrier z))))
         (laws
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term carrier add-xy)
            (putnam-2003-a4-carrier-term carrier mul-xy)
            (putnam-2003-a4-carrier-term carrier neg-x)
            (putnam-2003-a4-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2003-a4-operation-term add add-xy z)
             (putnam-2003-a4-operation-term add x add-yz))
            (list
             'equal
             (putnam-2003-a4-operation-term mul mul-xy z)
             (putnam-2003-a4-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2003-a4-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2003-a4-operation-term mul y x))
            (list
             'equal
             (putnam-2003-a4-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2003-a4-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2003-a4-operation-term mul x qone)
             x)
            (putnam-2003-a4-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2003-a4-implies-term
             (putnam-2003-a4-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2003-a4-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2003-a4-operation-term mul x add-yz)
             (putnam-2003-a4-operation-term
              add
              (putnam-2003-a4-operation-term mul x y)
              (putnam-2003-a4-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2003-a4-implies-term domain laws))))

(defun putnam-2003-a4-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2003-a4-quoted zero))
         (lt-xy
          (putnam-2003-a4-operation-term lt x y))
         (lt-yx
          (putnam-2003-a4-operation-term lt y x))
         (lt-yz
          (putnam-2003-a4-operation-term lt y z))
         (lt-xz
          (putnam-2003-a4-operation-term lt x z))
         (domain
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term carrier x)
            (putnam-2003-a4-carrier-term carrier y)
            (putnam-2003-a4-carrier-term carrier z))))
         (laws
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-not-term
             (putnam-2003-a4-operation-term lt x x))
            (putnam-2003-a4-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2003-a4-implies-term
             (putnam-2003-a4-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2003-a4-implies-term
             lt-xy
             (putnam-2003-a4-operation-term
              lt
              (putnam-2003-a4-operation-term add x z)
              (putnam-2003-a4-operation-term add y z)))
            (putnam-2003-a4-implies-term
             (putnam-2003-a4-and-term
              (list
               (putnam-2003-a4-operation-term lt qzero x)
               (putnam-2003-a4-operation-term lt qzero y)))
             (putnam-2003-a4-operation-term
              lt
              qzero
              (putnam-2003-a4-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2003-a4-implies-term domain laws))))

(defun putnam-2003-a4-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2003-a4-quoted zero))
         (root
          (putnam-2003-a4-apply1-term square-root x))
         (domain
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term carrier x)
            (putnam-2003-a4-not-term
             (putnam-2003-a4-operation-term lt x qzero)))))
         (laws
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term carrier root)
            (list
             'equal
             (putnam-2003-a4-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2003-a4-implies-term domain laws))))

(defun putnam-2003-a4-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2003-a4-quoted zero))
         (domain
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2003-a4-all-coefficients-term
             carrier rest)
            (putnam-2003-a4-carrier-term carrier x))))
         (empty-law
          (putnam-2003-a4-implies-term
           (putnam-2003-a4-carrier-term carrier x)
           (list
            'equal
            (putnam-2003-a4-operation-term
             evaluate
             (putnam-2003-a4-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2003-a4-operation-term
           add
           coefficient
           (putnam-2003-a4-operation-term
            mul
            x
            (putnam-2003-a4-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2003-a4-implies-term
           domain
           (putnam-2003-a4-and-term
            (list
             (putnam-2003-a4-carrier-term
              carrier
              (putnam-2003-a4-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2003-a4-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2003-a4-and-term
      (list empty-law recursive-law)))))

(defun putnam-2003-a4-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2003-a4-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2003-a4-and-term
           (list
            (putnam-2003-a4-carrier-term carrier root)
            (list
             'equal
             (putnam-2003-a4-operation-term
              evaluate coefficients root)
             (putnam-2003-a4-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2003-a4-implies-term domain laws))))

(defun putnam-2003-a4-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2003-a4-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2003-a4-true-function '(x y z)))
         (order-laws
          (putnam-2003-a4-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2003-a4-true-function '(x y z)))
         (square-root-laws
          (putnam-2003-a4-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2003-a4-true-function '(x)))
         (evaluation-laws
          (putnam-2003-a4-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2003-a4-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2003-a4-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2003-a4-true-function
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

(defun putnam-2003-a4-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2003-a4-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2003-a4-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2003-a4-less-p (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2003-a4-abs (zero neg lt value)
  (if (putnam-2003-a4-less-p lt value zero)
      (putnam-2003-a4-neg neg value)
    value))

(defun putnam-2003-a4-quadratic-value
    (add mul a b c x)
  (putnam-2003-a4-add
   add
   (putnam-2003-a4-add
    add
    (putnam-2003-a4-mul
     mul a (putnam-2003-a4-mul mul x x))
    (putnam-2003-a4-mul mul b x))
   c))

(defun putnam-2003-a4-discriminant
    (one add mul neg a b c)
  (let* ((two (putnam-2003-a4-add add one one))
         (four (putnam-2003-a4-mul mul two two)))
    (putnam-2003-a4-add
     add
     (putnam-2003-a4-mul mul b b)
     (putnam-2003-a4-neg
      neg
      (putnam-2003-a4-mul
       mul four (putnam-2003-a4-mul mul a c))))))

(defun putnam-2003-a4-quadratic-term
    (add mul a b c x)
  (putnam-2003-a4-operation-term
   add
   (putnam-2003-a4-operation-term
    add
    (putnam-2003-a4-operation-term
     mul
     (putnam-2003-a4-quoted a)
     (putnam-2003-a4-operation-term mul x x))
    (putnam-2003-a4-operation-term
     mul
     (putnam-2003-a4-quoted b)
     x))
   (putnam-2003-a4-quoted c)))

(defun putnam-2003-a4-abs-term
    (zero neg lt value)
  (list
   'if
   (putnam-2003-a4-operation-term
    lt value (putnam-2003-a4-quoted zero))
   (putnam-2003-a4-apply1-term neg value)
   value))

(defun putnam-2003-a4-domination-function
    (carrier zero add mul neg lt a b c big-a big-b big-c)
  (let* ((x 'x)
         (left
          (putnam-2003-a4-abs-term
           zero neg lt
           (putnam-2003-a4-quadratic-term
            add mul a b c x)))
         (right
          (putnam-2003-a4-abs-term
           zero neg lt
           (putnam-2003-a4-quadratic-term
            add mul big-a big-b big-c x)))
         (dominated
          (putnam-2003-a4-not-term
           (putnam-2003-a4-operation-term
            lt right left))))
    (list
     'lambda
     '(x)
     (putnam-2003-a4-implies-term
      (putnam-2003-a4-carrier-term carrier x)
      dominated))))

(defun putnam-2003-a4-domination-p
    (carrier zero add mul neg lt a b c big-a big-b big-c)
  (let* ((domination-function
          (putnam-2003-a4-domination-function
           carrier zero add mul neg lt
           a b c big-a big-b big-c))
         (domination-true
          (putnam-2003-a4-true-function '(x))))
    (and
     (tamep-functionp domination-function)
     (tamep-functionp domination-true)
     (fn-equal domination-function domination-true))))

(defun putnambench-putnam-2003-a4-statement
    (carrier zero one add mul neg inv lt square-root odd-root evaluate
             a b c big-a big-b big-c)
  (implies
   (and
    (putnam-2003-a4-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate)
    (apply$ carrier (list a))
    (apply$ carrier (list b))
    (apply$ carrier (list c))
    (apply$ carrier (list big-a))
    (apply$ carrier (list big-b))
    (apply$ carrier (list big-c))
    (not (equal a zero))
    (not (equal big-a zero))
    (putnam-2003-a4-domination-p
     carrier zero add mul neg lt
     a b c big-a big-b big-c))
   (not
    (putnam-2003-a4-less-p
     lt
     (putnam-2003-a4-abs
      zero neg lt
      (putnam-2003-a4-discriminant
       one add mul neg big-a big-b big-c))
     (putnam-2003-a4-abs
      zero neg lt
      (putnam-2003-a4-discriminant
       one add mul neg a b c))))))

(value-triple :itpeval-statement-checked)
:q
