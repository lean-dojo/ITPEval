;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_b2:
;; the real solutions of a two-equation reciprocal polynomial system form the
;; singleton determined by the positive real fifth root of 3. This file
;; contains no proof.

(in-package "ACL2")

;; The source quantifies over arbitrary real x and y.  The parameters below
;; present a real closed ordered field, rather than replacing the reals by
;; ACL2's rational numbers.  FN-EQUAL against a constant-T function expresses
;; the universal field, order, and real-closure laws over the whole carrier.
;;
;; If r is the unique real root of r^5 = 3, the source solution
;; ((r+1)/2,(r-1)/2) is equivalently characterized by
;;
;;   x - y = 1  and  (x + y)^5 = 3.
;;
;; Odd fifth powers are injective in every ordered field, so this eliminates
;; the named irrational without changing the singleton or introducing an
;; external witness.  The reciprocal equations themselves are retained
;; directly using the field inverse operation.

(defun putnam-2001-b2-quoted (object)
  (list 'quote object))

(defun putnam-2001-b2-apply1-term (function argument)
  (list
   'apply$
   (putnam-2001-b2-quoted function)
   (list 'cons argument nil)))

(defun putnam-2001-b2-apply2-term (function left right)
  (list
   'apply$
   (putnam-2001-b2-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2001-b2-and-term (terms)
  (if (endp terms)
      (putnam-2001-b2-quoted t)
    (list
     'if
     (car terms)
     (putnam-2001-b2-and-term (cdr terms))
     (putnam-2001-b2-quoted nil))))

(defun putnam-2001-b2-or-term (terms)
  (if (endp terms)
      (putnam-2001-b2-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2001-b2-quoted t)
     (putnam-2001-b2-or-term (cdr terms)))))

(defun putnam-2001-b2-not-term (term)
  (list
   'if
   term
   (putnam-2001-b2-quoted nil)
   (putnam-2001-b2-quoted t)))

(defun putnam-2001-b2-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2001-b2-quoted t)))

(defun putnam-2001-b2-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2001-b2-quoted t)))

(defun putnam-2001-b2-carrier-term (carrier element)
  (putnam-2001-b2-apply1-term carrier element))

(defun putnam-2001-b2-operation-term (operation left right)
  (putnam-2001-b2-apply2-term operation left right))

(defun putnam-2001-b2-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2001-b2-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2001-b2-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2001-b2-quoted
    (putnam-2001-b2-all-coefficients-function
     carrier))
   (putnam-2001-b2-quoted nil)
   coefficients))

(defun putnam-2001-b2-polynomial-term
    (carrier zero coefficients)
  (putnam-2001-b2-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2001-b2-all-coefficients-term
     carrier coefficients)
    (putnam-2001-b2-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2001-b2-quoted 1))
      (putnam-2001-b2-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2001-b2-quoted zero))))))))

(defun putnam-2001-b2-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2001-b2-quoted zero))
         (qone (putnam-2001-b2-quoted one))
         (add-xy
          (putnam-2001-b2-operation-term add x y))
         (add-yz
          (putnam-2001-b2-operation-term add y z))
         (mul-xy
          (putnam-2001-b2-operation-term mul x y))
         (mul-yz
          (putnam-2001-b2-operation-term mul y z))
         (neg-x
          (putnam-2001-b2-apply1-term neg x))
         (inv-x
          (putnam-2001-b2-apply1-term inv x))
         (domain
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term carrier x)
            (putnam-2001-b2-carrier-term carrier y)
            (putnam-2001-b2-carrier-term carrier z))))
         (laws
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term carrier add-xy)
            (putnam-2001-b2-carrier-term carrier mul-xy)
            (putnam-2001-b2-carrier-term carrier neg-x)
            (putnam-2001-b2-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2001-b2-operation-term add add-xy z)
             (putnam-2001-b2-operation-term add x add-yz))
            (list
             'equal
             (putnam-2001-b2-operation-term mul mul-xy z)
             (putnam-2001-b2-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2001-b2-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2001-b2-operation-term mul y x))
            (list
             'equal
             (putnam-2001-b2-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2001-b2-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2001-b2-operation-term mul x qone)
             x)
            (putnam-2001-b2-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2001-b2-implies-term
             (putnam-2001-b2-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2001-b2-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2001-b2-operation-term mul x add-yz)
             (putnam-2001-b2-operation-term
              add
              (putnam-2001-b2-operation-term mul x y)
              (putnam-2001-b2-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2001-b2-implies-term domain laws))))

(defun putnam-2001-b2-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2001-b2-quoted zero))
         (lt-xy
          (putnam-2001-b2-operation-term lt x y))
         (lt-yx
          (putnam-2001-b2-operation-term lt y x))
         (lt-yz
          (putnam-2001-b2-operation-term lt y z))
         (lt-xz
          (putnam-2001-b2-operation-term lt x z))
         (domain
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term carrier x)
            (putnam-2001-b2-carrier-term carrier y)
            (putnam-2001-b2-carrier-term carrier z))))
         (laws
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-not-term
             (putnam-2001-b2-operation-term lt x x))
            (putnam-2001-b2-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2001-b2-implies-term
             (putnam-2001-b2-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2001-b2-implies-term
             lt-xy
             (putnam-2001-b2-operation-term
              lt
              (putnam-2001-b2-operation-term add x z)
              (putnam-2001-b2-operation-term add y z)))
            (putnam-2001-b2-implies-term
             (putnam-2001-b2-and-term
              (list
               (putnam-2001-b2-operation-term lt qzero x)
               (putnam-2001-b2-operation-term lt qzero y)))
             (putnam-2001-b2-operation-term
              lt
              qzero
              (putnam-2001-b2-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2001-b2-implies-term domain laws))))

(defun putnam-2001-b2-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2001-b2-quoted zero))
         (root
          (putnam-2001-b2-apply1-term square-root x))
         (domain
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term carrier x)
            (putnam-2001-b2-not-term
             (putnam-2001-b2-operation-term lt x qzero)))))
         (laws
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term carrier root)
            (list
             'equal
             (putnam-2001-b2-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2001-b2-implies-term domain laws))))

(defun putnam-2001-b2-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2001-b2-quoted zero))
         (domain
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2001-b2-all-coefficients-term
             carrier rest)
            (putnam-2001-b2-carrier-term carrier x))))
         (empty-law
          (putnam-2001-b2-implies-term
           (putnam-2001-b2-carrier-term carrier x)
           (list
            'equal
            (putnam-2001-b2-operation-term
             evaluate
             (putnam-2001-b2-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2001-b2-operation-term
           add
           coefficient
           (putnam-2001-b2-operation-term
            mul
            x
            (putnam-2001-b2-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2001-b2-implies-term
           domain
           (putnam-2001-b2-and-term
            (list
             (putnam-2001-b2-carrier-term
              carrier
              (putnam-2001-b2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2001-b2-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2001-b2-and-term
      (list empty-law recursive-law)))))

(defun putnam-2001-b2-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2001-b2-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2001-b2-and-term
           (list
            (putnam-2001-b2-carrier-term carrier root)
            (list
             'equal
             (putnam-2001-b2-operation-term
              evaluate coefficients root)
             (putnam-2001-b2-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2001-b2-implies-term domain laws))))

(defun putnam-2001-b2-real-closed-field-p
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
    (putnam-2001-b2-field-laws-function
     carrier zero one add mul neg inv)
    (putnam-2001-b2-true-function '(x y z)))
   (fn-equal
    (putnam-2001-b2-order-laws-function
     carrier zero add mul lt)
    (putnam-2001-b2-true-function '(x y z)))
   (fn-equal
    (putnam-2001-b2-square-root-laws-function
     carrier zero mul lt square-root)
    (putnam-2001-b2-true-function '(x)))
   (fn-equal
    (putnam-2001-b2-evaluation-laws-function
     carrier zero add mul evaluate)
    (putnam-2001-b2-true-function
     '(coefficient rest x)))
   (fn-equal
    (putnam-2001-b2-odd-root-laws-function
     carrier zero evaluate odd-root)
    (putnam-2001-b2-true-function
     '(coefficients)))))

(defun putnam-2001-b2-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2001-b2-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2001-b2-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2001-b2-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2001-b2-sub (add neg left right)
  (putnam-2001-b2-add
   add left (putnam-2001-b2-neg neg right)))

(defun putnam-2001-b2-power (mul one value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2001-b2-mul
     mul
     value
     (putnam-2001-b2-power
      mul one value (- exponent 1)))))

(defun putnam-2001-b2-system-p
    (one add mul neg inv x y)
  (let* ((two
          (putnam-2001-b2-add add one one))
         (three
          (putnam-2001-b2-add add two one))
         (x2
          (putnam-2001-b2-power mul one x 2))
         (y2
          (putnam-2001-b2-power mul one y 2))
         (x4
          (putnam-2001-b2-power mul one x 4))
         (y4
          (putnam-2001-b2-power mul one y 4))
         (two-y
          (putnam-2001-b2-mul mul two y))
         (left1
          (putnam-2001-b2-add
           add
           (putnam-2001-b2-inv inv x)
           (putnam-2001-b2-inv inv two-y)))
         (right1
          (putnam-2001-b2-mul
           mul
           (putnam-2001-b2-add
            add
            x2
            (putnam-2001-b2-mul mul three y2))
           (putnam-2001-b2-add
            add
            (putnam-2001-b2-mul mul three x2)
            y2)))
         (left2
          (putnam-2001-b2-sub
           add neg
           (putnam-2001-b2-inv inv x)
           (putnam-2001-b2-inv inv two-y)))
         (right2
          (putnam-2001-b2-mul
           mul
           two
           (putnam-2001-b2-sub add neg y4 x4))))
    (and
     (equal left1 right1)
     (equal left2 right2))))

(defun putnam-2001-b2-solution-p
    (one add mul neg x y)
  (let* ((two
          (putnam-2001-b2-add add one one))
         (three
          (putnam-2001-b2-add add two one))
         (difference
          (putnam-2001-b2-sub add neg x y))
         (sum
          (putnam-2001-b2-add add x y)))
    (and
     (equal difference one)
     (equal
      (putnam-2001-b2-power mul one sum 5)
      three))))

(defun putnambench-putnam-2001-b2-statement
    (carrier zero one add mul neg inv lt square-root odd-root
             evaluate x y)
  (implies
   (and
    (putnam-2001-b2-real-closed-field-p
     carrier zero one add mul neg inv lt square-root odd-root evaluate)
    (apply$ carrier (list x))
    (apply$ carrier (list y))
    (not (equal x zero))
    (not (equal y zero)))
   (iff
    (putnam-2001-b2-system-p
     one add mul neg inv x y)
    (putnam-2001-b2-solution-p
     one add mul neg x y))))

(value-triple :itpeval-statement-checked)
:q
