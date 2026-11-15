;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_a3:
;; the greatest universal lower bound for the average modulus of the roots of
;; a degree-2019 polynomial with real coefficients
;; 1 <= b_0 < ... < b_2019 <= 2019 is 2019^(-1/2019).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are interpreted in an arbitrary real closed ordered field. Real
;; closed fields are elementarily equivalent, and the assertion below is
;; first-order in ordered-field operations and square roots. Complex numbers
;; are pairs of field elements. A list of 2019 roots represents the full root
;; multiset exactly when its product of linear factors, scaled by the leading
;; coefficient, reproduces all 2020 real coefficients.
;;
;; FN-EQUAL against a constant-T function supplies universal quantification
;; over every coefficient list and root list. Thus roots remain internal to
;; the lower-bound predicate rather than becoming extra assumptions on a
;; particular polynomial.

(defun putnam-2019-a3-quoted (object)
  (list 'quote object))

(defun putnam-2019-a3-apply1-term (function argument)
  (list
   'apply$
   (putnam-2019-a3-quoted function)
   (list 'cons argument nil)))

(defun putnam-2019-a3-apply2-term (function left right)
  (list
   'apply$
   (putnam-2019-a3-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2019-a3-and-term (terms)
  (if (endp terms)
      (putnam-2019-a3-quoted t)
    (list
     'if
     (car terms)
     (putnam-2019-a3-and-term (cdr terms))
     (putnam-2019-a3-quoted nil))))

(defun putnam-2019-a3-or-term (terms)
  (if (endp terms)
      (putnam-2019-a3-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2019-a3-quoted t)
     (putnam-2019-a3-or-term (cdr terms)))))

(defun putnam-2019-a3-not-term (term)
  (list
   'if
   term
   (putnam-2019-a3-quoted nil)
   (putnam-2019-a3-quoted t)))

(defun putnam-2019-a3-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2019-a3-quoted t)))

(defun putnam-2019-a3-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2019-a3-quoted t)))

(defun putnam-2019-a3-carrier-term (carrier element)
  (putnam-2019-a3-apply1-term carrier element))

(defun putnam-2019-a3-operation-term (operation left right)
  (putnam-2019-a3-apply2-term operation left right))

(defun putnam-2019-a3-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2019-a3-quoted zero))
         (qone (putnam-2019-a3-quoted one))
         (add-xy
          (putnam-2019-a3-operation-term add x y))
         (add-yz
          (putnam-2019-a3-operation-term add y z))
         (mul-xy
          (putnam-2019-a3-operation-term mul x y))
         (mul-yz
          (putnam-2019-a3-operation-term mul y z))
         (neg-x
          (putnam-2019-a3-apply1-term neg x))
         (inv-x
          (putnam-2019-a3-apply1-term inv x))
         (domain
          (putnam-2019-a3-and-term
           (list
            (putnam-2019-a3-carrier-term carrier x)
            (putnam-2019-a3-carrier-term carrier y)
            (putnam-2019-a3-carrier-term carrier z))))
         (laws
          (putnam-2019-a3-and-term
           (list
            (putnam-2019-a3-carrier-term carrier add-xy)
            (putnam-2019-a3-carrier-term carrier mul-xy)
            (putnam-2019-a3-carrier-term carrier neg-x)
            (putnam-2019-a3-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2019-a3-operation-term add add-xy z)
             (putnam-2019-a3-operation-term add x add-yz))
            (list
             'equal
             (putnam-2019-a3-operation-term mul mul-xy z)
             (putnam-2019-a3-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2019-a3-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2019-a3-operation-term mul y x))
            (list
             'equal
             (putnam-2019-a3-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2019-a3-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2019-a3-operation-term mul x qone)
             x)
            (putnam-2019-a3-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2019-a3-implies-term
             (putnam-2019-a3-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2019-a3-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2019-a3-operation-term mul x add-yz)
             (putnam-2019-a3-operation-term
              add
              (putnam-2019-a3-operation-term mul x y)
              (putnam-2019-a3-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2019-a3-implies-term domain laws))))

(defun putnam-2019-a3-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2019-a3-quoted zero))
         (lt-xy
          (putnam-2019-a3-operation-term lt x y))
         (lt-yx
          (putnam-2019-a3-operation-term lt y x))
         (lt-yz
          (putnam-2019-a3-operation-term lt y z))
         (lt-xz
          (putnam-2019-a3-operation-term lt x z))
         (domain
          (putnam-2019-a3-and-term
           (list
            (putnam-2019-a3-carrier-term carrier x)
            (putnam-2019-a3-carrier-term carrier y)
            (putnam-2019-a3-carrier-term carrier z))))
         (laws
          (putnam-2019-a3-and-term
           (list
            (putnam-2019-a3-not-term
             (putnam-2019-a3-operation-term lt x x))
            (putnam-2019-a3-or-term
             (list
              lt-xy
              lt-yx
              (list 'equal x y)))
            (putnam-2019-a3-implies-term
             (putnam-2019-a3-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2019-a3-implies-term
             lt-xy
             (putnam-2019-a3-operation-term
              lt
              (putnam-2019-a3-operation-term add x z)
              (putnam-2019-a3-operation-term add y z)))
            (putnam-2019-a3-implies-term
             (putnam-2019-a3-and-term
              (list
               (putnam-2019-a3-operation-term lt qzero x)
               (putnam-2019-a3-operation-term lt qzero y)))
             (putnam-2019-a3-operation-term
              lt
              qzero
              (putnam-2019-a3-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2019-a3-implies-term domain laws))))

(defun putnam-2019-a3-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2019-a3-quoted zero))
         (root
          (putnam-2019-a3-apply1-term square-root x))
         (domain
          (putnam-2019-a3-and-term
           (list
            (putnam-2019-a3-carrier-term carrier x)
            (putnam-2019-a3-not-term
             (putnam-2019-a3-operation-term lt x qzero)))))
         (laws
          (putnam-2019-a3-and-term
           (list
            (putnam-2019-a3-carrier-term carrier root)
            (putnam-2019-a3-not-term
             (putnam-2019-a3-operation-term lt root qzero))
            (list
             'equal
             (putnam-2019-a3-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2019-a3-implies-term domain laws))))

(defun putnam-2019-a3-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2019-a3-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2019-a3-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2019-a3-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2019-a3-lt (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2019-a3-le (lt left right)
  (not (putnam-2019-a3-lt lt right left)))

(defun putnam-2019-a3-field-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2019-a3-add
     add
     one
     (putnam-2019-a3-field-natural
      (- n 1) zero one add))))

(defun putnam-2019-a3-field-power (base exponent one mul)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2019-a3-mul
     mul
     base
     (putnam-2019-a3-field-power
      base (- exponent 1) one mul))))

(defun putnam-2019-a3-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-2019-a3-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2019-a3-polynomial-p
    (coefficients carrier zero)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (putnam-2019-a3-coefficient-list-p
    coefficients carrier)
   (or
    (equal (len coefficients) 1)
    (not (equal (car (last coefficients)) zero)))))

(defun putnam-2019-a3-polynomial-eval
    (coefficients x zero add mul)
  (if (endp coefficients)
      zero
    (putnam-2019-a3-add
     add
     (car coefficients)
     (putnam-2019-a3-mul
      mul
      x
      (putnam-2019-a3-polynomial-eval
       (cdr coefficients) x zero add mul)))))

(defun-sk putnam-2019-a3-odd-root-laws-p
    (carrier zero add mul odd-root)
  (forall (coefficients)
    (implies
     (and
      (putnam-2019-a3-polynomial-p
       coefficients carrier zero)
      (evenp (len coefficients)))
     (let ((root (apply$ odd-root (list coefficients))))
       (and
        (apply$ carrier (list root))
        (equal
         (putnam-2019-a3-polynomial-eval
          coefficients root zero add mul)
         zero))))))

(defun putnam-2019-a3-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root odd-root)
  (let* ((field-laws
          (putnam-2019-a3-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2019-a3-true-function '(x y z)))
         (order-laws
          (putnam-2019-a3-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2019-a3-true-function '(x y z)))
         (square-root-laws
          (putnam-2019-a3-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2019-a3-true-function '(x))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp mul)
     (tamep-functionp neg)
     (tamep-functionp inv)
     (tamep-functionp lt)
     (tamep-functionp square-root)
     (tamep-functionp odd-root)
     (tamep-functionp field-laws)
     (tamep-functionp field-laws-true)
     (tamep-functionp order-laws)
     (tamep-functionp order-laws-true)
     (tamep-functionp square-root-laws)
     (tamep-functionp square-root-laws-true)
     (apply$ carrier (list zero))
     (apply$ carrier (list one))
     (not (equal zero one))
     (fn-equal field-laws field-laws-true)
     (fn-equal order-laws order-laws-true)
     (fn-equal square-root-laws square-root-laws-true)
     (putnam-2019-a3-odd-root-laws-p
      carrier zero add mul odd-root))))

(defun putnam-2019-a3-complex-p (z carrier)
  (and
   (consp z)
   (apply$ carrier (list (car z)))
   (apply$ carrier (list (cdr z)))))

(defun putnam-2019-a3-complex-zero (zero)
  (cons zero zero))

(defun putnam-2019-a3-complex-one (zero one)
  (cons one zero))

(defun putnam-2019-a3-complex-add (left right add)
  (cons
   (putnam-2019-a3-add add (car left) (car right))
   (putnam-2019-a3-add add (cdr left) (cdr right))))

(defun putnam-2019-a3-complex-neg (value neg)
  (cons
   (putnam-2019-a3-neg neg (car value))
   (putnam-2019-a3-neg neg (cdr value))))

(defun putnam-2019-a3-complex-mul
    (left right add mul neg)
  (let ((ac
         (putnam-2019-a3-mul mul (car left) (car right)))
        (bd
         (putnam-2019-a3-mul mul (cdr left) (cdr right)))
        (ad
         (putnam-2019-a3-mul mul (car left) (cdr right)))
        (bc
         (putnam-2019-a3-mul mul (cdr left) (car right))))
    (cons
     (putnam-2019-a3-add
      add ac (putnam-2019-a3-neg neg bd))
     (putnam-2019-a3-add add ad bc))))

(defun putnam-2019-a3-complex-polynomial-add
    (left right add)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (putnam-2019-a3-complex-add
      (car left) (car right) add)
     (putnam-2019-a3-complex-polynomial-add
      (cdr left) (cdr right) add)))))

(defun putnam-2019-a3-complex-polynomial-scale
    (scalar coefficients add mul neg)
  (if (endp coefficients)
      nil
    (cons
     (putnam-2019-a3-complex-mul
      scalar (car coefficients) add mul neg)
     (putnam-2019-a3-complex-polynomial-scale
      scalar (cdr coefficients) add mul neg))))

(defun putnam-2019-a3-multiply-by-linear
    (coefficients root zero add mul neg)
  (putnam-2019-a3-complex-polynomial-add
   (putnam-2019-a3-complex-polynomial-scale
    (putnam-2019-a3-complex-neg root neg)
    coefficients add mul neg)
   (cons (putnam-2019-a3-complex-zero zero)
         coefficients)
   add))

(defun putnam-2019-a3-root-product
    (roots zero one add mul neg)
  (if (endp roots)
      (list (putnam-2019-a3-complex-one zero one))
    (putnam-2019-a3-multiply-by-linear
     (putnam-2019-a3-root-product
      (cdr roots) zero one add mul neg)
     (car roots)
     zero add mul neg)))

(defun putnam-2019-a3-real-coefficients-as-complex
    (coefficients zero)
  (if (endp coefficients)
      nil
    (cons
     (cons (car coefficients) zero)
     (putnam-2019-a3-real-coefficients-as-complex
      (cdr coefficients) zero))))

(defun putnam-2019-a3-roots-p (roots carrier)
  (if (endp roots)
      (equal roots nil)
    (and
     (putnam-2019-a3-complex-p (car roots) carrier)
     (putnam-2019-a3-roots-p (cdr roots) carrier))))

(defun putnam-2019-a3-increasing-p (coefficients lt)
  (if (or (endp coefficients)
          (endp (cdr coefficients)))
      t
    (and
     (putnam-2019-a3-lt
      lt (car coefficients) (cadr coefficients))
     (putnam-2019-a3-increasing-p
      (cdr coefficients) lt))))

(defun putnam-2019-a3-admissible-polynomial-p
    (coefficients carrier zero one add lt)
  (let ((upper
         (putnam-2019-a3-field-natural
          2019 zero one add)))
    (and
     (true-listp coefficients)
     (equal (len coefficients) 2020)
     (putnam-2019-a3-coefficient-list-p
      coefficients carrier)
     (putnam-2019-a3-le lt one (car coefficients))
     (putnam-2019-a3-increasing-p coefficients lt)
     (putnam-2019-a3-le
      lt (car (last coefficients)) upper))))

(defun putnam-2019-a3-factorization-p
    (coefficients roots zero one add mul neg)
  (let* ((monic-product
          (putnam-2019-a3-root-product
           roots zero one add mul neg))
         (leading
          (cons (car (last coefficients)) zero))
         (scaled-product
          (putnam-2019-a3-complex-polynomial-scale
           leading monic-product add mul neg)))
    (equal
     scaled-product
     (putnam-2019-a3-real-coefficients-as-complex
      coefficients zero))))

(defun putnam-2019-a3-complex-norm
    (z add mul square-root)
  (apply$
   square-root
   (list
    (putnam-2019-a3-add
     add
     (putnam-2019-a3-mul mul (car z) (car z))
     (putnam-2019-a3-mul mul (cdr z) (cdr z))))))

(defun putnam-2019-a3-root-norm-sum
    (roots zero add mul square-root)
  (if (endp roots)
      zero
    (putnam-2019-a3-add
     add
     (putnam-2019-a3-complex-norm
      (car roots) add mul square-root)
     (putnam-2019-a3-root-norm-sum
      (cdr roots) zero add mul square-root))))

(defun putnam-2019-a3-root-norm-average
    (roots zero one add mul inv square-root)
  (putnam-2019-a3-mul
   mul
   (putnam-2019-a3-root-norm-sum
    roots zero add mul square-root)
   (putnam-2019-a3-inv
    inv
    (putnam-2019-a3-field-natural
     2019 zero one add))))

(defun putnam-2019-a3-bound-instance-p
    (coefficients roots constant
                  carrier zero one add mul neg inv lt square-root)
  (if
      (and
       (putnam-2019-a3-admissible-polynomial-p
        coefficients carrier zero one add lt)
       (true-listp roots)
       (equal (len roots) 2019)
       (putnam-2019-a3-roots-p roots carrier)
       (putnam-2019-a3-factorization-p
        coefficients roots zero one add mul neg))
      (putnam-2019-a3-le
       lt
       constant
       (putnam-2019-a3-root-norm-average
        roots zero one add mul inv square-root))
    t))

(defun-sk putnam-2019-a3-bound-p
    (constant carrier zero one add mul neg inv lt square-root)
  (forall (coefficients roots)
    (putnam-2019-a3-bound-instance-p
     coefficients roots constant
     carrier zero one add mul neg inv lt square-root)))

(defun putnam-2019-a3-zero-list (count zero)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     zero
     (putnam-2019-a3-zero-list (- count 1) zero))))

(defun putnam-2019-a3-solution-polynomial
    (zero one add neg)
  (cons
   (putnam-2019-a3-neg neg one)
   (append
    (putnam-2019-a3-zero-list 2018 zero)
    (list
     (putnam-2019-a3-field-natural
      2019 zero one add)))))

(defun putnambench-putnam-2019-a3-statement
    (carrier zero one add mul neg inv lt
             square-root odd-root constant)
  (implies
   (putnam-2019-a3-real-closed-field-p
    carrier zero one add mul neg inv lt square-root odd-root)
   (let* ((solution-polynomial
           (putnam-2019-a3-solution-polynomial
            zero one add neg))
          (solution
           (apply$ odd-root (list solution-polynomial))))
     (and
      (putnam-2019-a3-bound-p
       solution
       carrier zero one add mul neg inv lt square-root)
      (implies
       (and
        (apply$ carrier (list constant))
        (putnam-2019-a3-bound-p
         constant
         carrier zero one add mul neg inv lt square-root))
       (putnam-2019-a3-le lt constant solution))))))

(value-triple :itpeval-statement-checked)
:q
