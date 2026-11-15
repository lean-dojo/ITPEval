;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_a5:
;; the complex zeros of the weighted sum
;; sum_{k=0}^{3^1010-1} (-2)^(number of base-3 ones in k) (z+k)^2023
;; are exactly the three specified values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Scalars are interpreted in an arbitrary real closed ordered field. Real
;; closed fields are elementarily equivalent, and the assertion below is
;; first-order in ordered-field operations. Complex numbers are pairs of field
;; elements, so this does not restrict their real or imaginary parts to ACL2's
;; rational numbers.
;; A tame external polynomial evaluator is constrained by universal Horner
;; laws, making it definitionally equivalent to polynomial evaluation while
;; keeping every FN-EQUAL operand within ACL2's APPLY$ language.
;;
;; The two nonreal roots have real part -(3^1010-1)/2 and imaginary part y
;; satisfying y^2 = (9^1010-1)/16. Over a real closed ordered field this is
;; bidirectionally equivalent to y = +/-sqrt(9^1010-1)/4, without turning the
;; square root into an external witness. The argument Z supplies the universal
;; quantifier implicit in the source set equality.

(defun putnam-2023-a5-quoted (object)
  (list 'quote object))

(defun putnam-2023-a5-apply1-term (function argument)
  (list
   'apply$
   (putnam-2023-a5-quoted function)
   (list 'cons argument nil)))

(defun putnam-2023-a5-apply2-term (function left right)
  (list
   'apply$
   (putnam-2023-a5-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2023-a5-and-term (terms)
  (if (endp terms)
      (putnam-2023-a5-quoted t)
    (list
     'if
     (car terms)
     (putnam-2023-a5-and-term (cdr terms))
     (putnam-2023-a5-quoted nil))))

(defun putnam-2023-a5-or-term (terms)
  (if (endp terms)
      (putnam-2023-a5-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2023-a5-quoted t)
     (putnam-2023-a5-or-term (cdr terms)))))

(defun putnam-2023-a5-not-term (term)
  (list
   'if
   term
   (putnam-2023-a5-quoted nil)
   (putnam-2023-a5-quoted t)))

(defun putnam-2023-a5-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2023-a5-quoted t)))

(defun putnam-2023-a5-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2023-a5-quoted t)))

(defun putnam-2023-a5-carrier-term (carrier element)
  (putnam-2023-a5-apply1-term carrier element))

(defun putnam-2023-a5-operation-term (operation left right)
  (putnam-2023-a5-apply2-term operation left right))

(defun putnam-2023-a5-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2023-a5-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2023-a5-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2023-a5-quoted
    (putnam-2023-a5-all-coefficients-function
     carrier))
   (putnam-2023-a5-quoted nil)
   coefficients))

(defun putnam-2023-a5-polynomial-term
    (carrier zero coefficients)
  (putnam-2023-a5-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2023-a5-all-coefficients-term
     carrier coefficients)
    (putnam-2023-a5-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2023-a5-quoted 1))
      (putnam-2023-a5-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2023-a5-quoted zero))))))))

(defun putnam-2023-a5-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2023-a5-quoted zero))
         (qone (putnam-2023-a5-quoted one))
         (add-xy
          (putnam-2023-a5-operation-term add x y))
         (add-yz
          (putnam-2023-a5-operation-term add y z))
         (mul-xy
          (putnam-2023-a5-operation-term mul x y))
         (mul-yz
          (putnam-2023-a5-operation-term mul y z))
         (neg-x
          (putnam-2023-a5-apply1-term neg x))
         (inv-x
          (putnam-2023-a5-apply1-term inv x))
         (domain
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term carrier x)
            (putnam-2023-a5-carrier-term carrier y)
            (putnam-2023-a5-carrier-term carrier z))))
         (laws
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term carrier add-xy)
            (putnam-2023-a5-carrier-term carrier mul-xy)
            (putnam-2023-a5-carrier-term carrier neg-x)
            (putnam-2023-a5-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2023-a5-operation-term add add-xy z)
             (putnam-2023-a5-operation-term add x add-yz))
            (list
             'equal
             (putnam-2023-a5-operation-term mul mul-xy z)
             (putnam-2023-a5-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2023-a5-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2023-a5-operation-term mul y x))
            (list
             'equal
             (putnam-2023-a5-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2023-a5-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2023-a5-operation-term mul x qone)
             x)
            (putnam-2023-a5-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2023-a5-implies-term
             (putnam-2023-a5-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2023-a5-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2023-a5-operation-term mul x add-yz)
             (putnam-2023-a5-operation-term
              add
              (putnam-2023-a5-operation-term mul x y)
              (putnam-2023-a5-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2023-a5-implies-term domain laws))))

(defun putnam-2023-a5-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2023-a5-quoted zero))
         (lt-xy
          (putnam-2023-a5-operation-term lt x y))
         (lt-yx
          (putnam-2023-a5-operation-term lt y x))
         (lt-yz
          (putnam-2023-a5-operation-term lt y z))
         (lt-xz
          (putnam-2023-a5-operation-term lt x z))
         (domain
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term carrier x)
            (putnam-2023-a5-carrier-term carrier y)
            (putnam-2023-a5-carrier-term carrier z))))
         (laws
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-not-term
             (putnam-2023-a5-operation-term lt x x))
            (putnam-2023-a5-or-term
             (list
              lt-xy
              lt-yx
              (list 'equal x y)))
            (putnam-2023-a5-implies-term
             (putnam-2023-a5-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2023-a5-implies-term
             lt-xy
             (putnam-2023-a5-operation-term
              lt
              (putnam-2023-a5-operation-term add x z)
              (putnam-2023-a5-operation-term add y z)))
            (putnam-2023-a5-implies-term
             (putnam-2023-a5-and-term
              (list
               (putnam-2023-a5-operation-term lt qzero x)
               (putnam-2023-a5-operation-term lt qzero y)))
             (putnam-2023-a5-operation-term
              lt
              qzero
              (putnam-2023-a5-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2023-a5-implies-term domain laws))))

(defun putnam-2023-a5-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2023-a5-quoted zero))
         (root
          (putnam-2023-a5-apply1-term square-root x))
         (domain
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term carrier x)
            (putnam-2023-a5-not-term
             (putnam-2023-a5-operation-term lt x qzero)))))
         (laws
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term carrier root)
            (putnam-2023-a5-not-term
             (putnam-2023-a5-operation-term lt root qzero))
            (list
             'equal
             (putnam-2023-a5-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2023-a5-implies-term domain laws))))

(defun putnam-2023-a5-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2023-a5-quoted zero))
         (domain
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2023-a5-all-coefficients-term
             carrier rest)
            (putnam-2023-a5-carrier-term carrier x))))
         (empty-law
          (putnam-2023-a5-implies-term
           (putnam-2023-a5-carrier-term carrier x)
           (list
            'equal
            (putnam-2023-a5-operation-term
             evaluate
             (putnam-2023-a5-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2023-a5-operation-term
           add
           coefficient
           (putnam-2023-a5-operation-term
            mul
            x
            (putnam-2023-a5-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2023-a5-implies-term
           domain
           (putnam-2023-a5-and-term
            (list
             (putnam-2023-a5-carrier-term
              carrier
              (putnam-2023-a5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2023-a5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2023-a5-and-term
      (list empty-law recursive-law)))))

(defun putnam-2023-a5-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2023-a5-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2023-a5-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2023-a5-inv (inv value)
  (apply$ inv (list value)))

(defun putnam-2023-a5-lt (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2023-a5-le (lt left right)
  (not (putnam-2023-a5-lt lt right left)))

(defun putnam-2023-a5-field-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-2023-a5-add
     add
     one
     (putnam-2023-a5-field-natural
      (- n 1) zero one add))))

(defun putnam-2023-a5-field-power (base exponent one mul)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2023-a5-mul
     mul
     base
     (putnam-2023-a5-field-power
      base (- exponent 1) one mul))))

(defun putnam-2023-a5-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2023-a5-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2023-a5-and-term
           (list
            (putnam-2023-a5-carrier-term carrier root)
            (list
             'equal
             (putnam-2023-a5-operation-term
              evaluate coefficients root)
             (putnam-2023-a5-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2023-a5-implies-term domain laws))))

(defun putnam-2023-a5-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2023-a5-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2023-a5-true-function '(x y z)))
         (order-laws
          (putnam-2023-a5-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2023-a5-true-function '(x y z)))
         (square-root-laws
          (putnam-2023-a5-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2023-a5-true-function '(x)))
         (evaluation-laws
          (putnam-2023-a5-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2023-a5-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2023-a5-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2023-a5-true-function '(coefficients)))
         (all-coefficients-loop
          (putnam-2023-a5-all-coefficients-function
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

(defun putnam-2023-a5-complex-p (z carrier)
  (and
   (consp z)
   (apply$ carrier (list (car z)))
   (apply$ carrier (list (cdr z)))))

(defun putnam-2023-a5-complex-zero (zero)
  (cons zero zero))

(defun putnam-2023-a5-complex-one (zero one)
  (cons one zero))

(defun putnam-2023-a5-complex-add (left right add)
  (cons
   (putnam-2023-a5-add add (car left) (car right))
   (putnam-2023-a5-add add (cdr left) (cdr right))))

(defun putnam-2023-a5-complex-mul
    (left right add mul neg)
  (let ((ac
         (putnam-2023-a5-mul mul (car left) (car right)))
        (bd
         (putnam-2023-a5-mul mul (cdr left) (cdr right)))
        (ad
         (putnam-2023-a5-mul mul (car left) (cdr right)))
        (bc
         (putnam-2023-a5-mul mul (cdr left) (car right))))
    (cons
     (putnam-2023-a5-add
      add ac (putnam-2023-a5-neg neg bd))
     (putnam-2023-a5-add add ad bc))))

(defun putnam-2023-a5-complex-power
    (base exponent zero one add mul neg)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-2023-a5-complex-one zero one)
    (putnam-2023-a5-complex-mul
     base
     (putnam-2023-a5-complex-power
      base (- exponent 1) zero one add mul neg)
     add mul neg)))

(defun putnam-2023-a5-natural-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      1
    (* base
       (putnam-2023-a5-natural-power
        base (- exponent 1)))))

(defun putnam-2023-a5-num-ones-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond
   ((or (not (natp n))
        (zp fuel)
        (zp n))
    0)
   (t
    (+ (if (equal (mod n 3) 1) 1 0)
       (putnam-2023-a5-num-ones-aux
        (floor n 3)
        (- fuel 1))))))

(defun putnam-2023-a5-num-ones (n)
  (if (natp n)
      (putnam-2023-a5-num-ones-aux n (+ n 1))
    0))

(defun putnam-2023-a5-weighted-term
    (z k zero one add mul neg)
  (let* ((two
          (putnam-2023-a5-add add one one))
         (minus-two
          (putnam-2023-a5-neg neg two))
         (weight
          (putnam-2023-a5-field-power
           minus-two
           (putnam-2023-a5-num-ones k)
           one
           mul))
         (k-field
          (putnam-2023-a5-field-natural
           k zero one add))
         (shifted
          (putnam-2023-a5-complex-add
           z (cons k-field zero) add))
         (power
          (putnam-2023-a5-complex-power
           shifted 2023 zero one add mul neg)))
    (putnam-2023-a5-complex-mul
     (cons weight zero) power add mul neg)))

(defun putnam-2023-a5-weighted-sum
    (count z zero one add mul neg)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (putnam-2023-a5-complex-zero zero)
    (let ((k (- count 1)))
      (putnam-2023-a5-complex-add
       (putnam-2023-a5-weighted-sum
        k z zero one add mul neg)
       (putnam-2023-a5-weighted-term
        z k zero one add mul neg)
       add))))

(defun putnam-2023-a5-sum-zero-p
    (z zero one add mul neg)
  (equal
   (putnam-2023-a5-weighted-sum
    (putnam-2023-a5-natural-power 3 1010)
    z zero one add mul neg)
   (putnam-2023-a5-complex-zero zero)))

(defun putnam-2023-a5-solution-p
    (z zero one add mul neg inv)
  (let* ((two
          (putnam-2023-a5-field-natural
           2 zero one add))
         (sixteen
          (putnam-2023-a5-field-natural
           16 zero one add))
         (three-power
          (putnam-2023-a5-field-power
           (putnam-2023-a5-field-natural
            3 zero one add)
           1010
           one
           mul))
         (nine-power
          (putnam-2023-a5-field-power
           (putnam-2023-a5-field-natural
            9 zero one add)
           1010
           one
           mul))
         (three-power-minus-one
          (putnam-2023-a5-add
           add three-power (putnam-2023-a5-neg neg one)))
         (nine-power-minus-one
          (putnam-2023-a5-add
           add nine-power (putnam-2023-a5-neg neg one)))
         (center
          (putnam-2023-a5-mul
           mul
           (putnam-2023-a5-neg neg three-power-minus-one)
           (putnam-2023-a5-inv inv two)))
         (nonreal-imaginary-square
          (putnam-2023-a5-mul
           mul
           nine-power-minus-one
           (putnam-2023-a5-inv inv sixteen)))
         (imaginary-square
          (putnam-2023-a5-mul
           mul (cdr z) (cdr z))))
    (and
     (equal (car z) center)
     (or
      (equal (cdr z) zero)
      (equal imaginary-square
             nonreal-imaginary-square)))))

(defun putnambench-putnam-2023-a5-statement
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate z)
  (implies
   (and
    (putnam-2023-a5-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate)
    (putnam-2023-a5-complex-p z carrier))
   (equal
    (putnam-2023-a5-sum-zero-p
     z zero one add mul neg)
    (putnam-2023-a5-solution-p
     z zero one add mul neg inv))))

(value-triple :itpeval-statement-checked)
:q
