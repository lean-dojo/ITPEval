;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_a5:
;; real polynomial values at 1 through n forming a counterclockwise regular
;; n-gon force at least one polynomial to have degree at least n-1. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The coefficient domain is presented as an arbitrary real closed ordered
;; field. Completeness of real closed fields transfers this first-order
;; assertion bidirectionally between that presentation and the real numbers.
;; Complex values are pairs over the field. For n >= 3, exp(2*pi*i/n) is
;; exactly the positive-imaginary n-th root of unity having greatest real
;; part. The maximality condition below therefore fixes the source's
;; counterclockwise root rather than an arbitrary primitive root.
;;
;; Polynomials are canonical nonempty coefficient lists in ascending degree
;; order. FN-EQUAL supplies unbounded universal quantification for the field
;; laws and the root maximality condition. Negated FN-EQUAL keeps the source
;; center and nonzero complex scale existentially quantified inside the
;; statement predicate.

(defun putnam-2008-a5-quoted (object)
  (list 'quote object))

(defun putnam-2008-a5-apply1-term (function argument)
  (list
   'apply$
   (putnam-2008-a5-quoted function)
   (list 'cons argument nil)))

(defun putnam-2008-a5-apply2-term (function left right)
  (list
   'apply$
   (putnam-2008-a5-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2008-a5-and-term (terms)
  (if (endp terms)
      (putnam-2008-a5-quoted t)
    (list
     'if
     (car terms)
     (putnam-2008-a5-and-term (cdr terms))
     (putnam-2008-a5-quoted nil))))

(defun putnam-2008-a5-or-term (terms)
  (if (endp terms)
      (putnam-2008-a5-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2008-a5-quoted t)
     (putnam-2008-a5-or-term (cdr terms)))))

(defun putnam-2008-a5-not-term (term)
  (list
   'if
   term
   (putnam-2008-a5-quoted nil)
   (putnam-2008-a5-quoted t)))

(defun putnam-2008-a5-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2008-a5-quoted t)))

(defun putnam-2008-a5-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2008-a5-quoted t)))

(defun putnam-2008-a5-carrier-term (carrier element)
  (putnam-2008-a5-apply1-term carrier element))

(defun putnam-2008-a5-operation-term (operation left right)
  (putnam-2008-a5-apply2-term operation left right))

(defun putnam-2008-a5-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2008-a5-carrier-term
    carrier 'loop$-ivars)))

(defun putnam-2008-a5-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2008-a5-quoted
    (putnam-2008-a5-all-coefficients-function
     carrier))
   (putnam-2008-a5-quoted nil)
   coefficients))

(defun putnam-2008-a5-polynomial-term
    (carrier zero coefficients)
  (putnam-2008-a5-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2008-a5-all-coefficients-term
     carrier coefficients)
    (putnam-2008-a5-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2008-a5-quoted 1))
      (putnam-2008-a5-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2008-a5-quoted zero))))))))

(defun putnam-2008-a5-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2008-a5-quoted zero))
         (qone (putnam-2008-a5-quoted one))
         (add-xy
          (putnam-2008-a5-operation-term add x y))
         (add-yz
          (putnam-2008-a5-operation-term add y z))
         (mul-xy
          (putnam-2008-a5-operation-term mul x y))
         (mul-yz
          (putnam-2008-a5-operation-term mul y z))
         (neg-x
          (putnam-2008-a5-apply1-term neg x))
         (inv-x
          (putnam-2008-a5-apply1-term inv x))
         (domain
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term carrier x)
            (putnam-2008-a5-carrier-term carrier y)
            (putnam-2008-a5-carrier-term carrier z))))
         (laws
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term carrier add-xy)
            (putnam-2008-a5-carrier-term carrier mul-xy)
            (putnam-2008-a5-carrier-term carrier neg-x)
            (putnam-2008-a5-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2008-a5-operation-term add add-xy z)
             (putnam-2008-a5-operation-term add x add-yz))
            (list
             'equal
             (putnam-2008-a5-operation-term mul mul-xy z)
             (putnam-2008-a5-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2008-a5-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2008-a5-operation-term mul y x))
            (list
             'equal
             (putnam-2008-a5-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2008-a5-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2008-a5-operation-term mul x qone)
             x)
            (putnam-2008-a5-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2008-a5-implies-term
             (putnam-2008-a5-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2008-a5-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2008-a5-operation-term mul x add-yz)
             (putnam-2008-a5-operation-term
              add
              (putnam-2008-a5-operation-term mul x y)
              (putnam-2008-a5-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2008-a5-implies-term domain laws))))

(defun putnam-2008-a5-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2008-a5-quoted zero))
         (lt-xy
          (putnam-2008-a5-operation-term lt x y))
         (lt-yx
          (putnam-2008-a5-operation-term lt y x))
         (lt-yz
          (putnam-2008-a5-operation-term lt y z))
         (lt-xz
          (putnam-2008-a5-operation-term lt x z))
         (domain
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term carrier x)
            (putnam-2008-a5-carrier-term carrier y)
            (putnam-2008-a5-carrier-term carrier z))))
         (laws
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-not-term
             (putnam-2008-a5-operation-term lt x x))
            (putnam-2008-a5-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2008-a5-implies-term
             (putnam-2008-a5-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2008-a5-implies-term
             lt-xy
             (putnam-2008-a5-operation-term
              lt
              (putnam-2008-a5-operation-term add x z)
              (putnam-2008-a5-operation-term add y z)))
            (putnam-2008-a5-implies-term
             (putnam-2008-a5-and-term
              (list
               (putnam-2008-a5-operation-term lt qzero x)
               (putnam-2008-a5-operation-term lt qzero y)))
             (putnam-2008-a5-operation-term
              lt
              qzero
              (putnam-2008-a5-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2008-a5-implies-term domain laws))))

(defun putnam-2008-a5-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2008-a5-quoted zero))
         (root
          (putnam-2008-a5-apply1-term square-root x))
         (domain
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term carrier x)
            (putnam-2008-a5-not-term
             (putnam-2008-a5-operation-term lt x qzero)))))
         (laws
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term carrier root)
            (list
             'equal
             (putnam-2008-a5-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2008-a5-implies-term domain laws))))

(defun putnam-2008-a5-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2008-a5-quoted zero))
         (domain
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2008-a5-all-coefficients-term
             carrier rest)
            (putnam-2008-a5-carrier-term carrier x))))
         (empty-law
          (putnam-2008-a5-implies-term
           (putnam-2008-a5-carrier-term carrier x)
           (list
            'equal
            (putnam-2008-a5-operation-term
             evaluate
             (putnam-2008-a5-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2008-a5-operation-term
           add
           coefficient
           (putnam-2008-a5-operation-term
            mul
            x
            (putnam-2008-a5-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2008-a5-implies-term
           domain
           (putnam-2008-a5-and-term
            (list
             (putnam-2008-a5-carrier-term
              carrier
              (putnam-2008-a5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2008-a5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2008-a5-and-term
      (list empty-law recursive-law)))))

(defun putnam-2008-a5-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2008-a5-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2008-a5-and-term
           (list
            (putnam-2008-a5-carrier-term carrier root)
            (list
             'equal
             (putnam-2008-a5-operation-term
              evaluate coefficients root)
             (putnam-2008-a5-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2008-a5-implies-term domain laws))))

(defun putnam-2008-a5-real-closed-field-p
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate)
  (let* ((field-laws
          (putnam-2008-a5-field-laws-function
           carrier zero one add mul neg inv))
         (field-laws-true
          (putnam-2008-a5-true-function '(x y z)))
         (order-laws
          (putnam-2008-a5-order-laws-function
           carrier zero add mul lt))
         (order-laws-true
          (putnam-2008-a5-true-function '(x y z)))
         (square-root-laws
          (putnam-2008-a5-square-root-laws-function
           carrier zero mul lt square-root))
         (square-root-laws-true
          (putnam-2008-a5-true-function '(x)))
         (evaluation-laws
          (putnam-2008-a5-evaluation-laws-function
           carrier zero add mul evaluate))
         (evaluation-laws-true
          (putnam-2008-a5-true-function
           '(coefficient rest x)))
         (odd-root-laws
          (putnam-2008-a5-odd-root-laws-function
           carrier zero evaluate odd-root))
         (odd-root-laws-true
          (putnam-2008-a5-true-function
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

(defun putnam-2008-a5-add (add left right)
  (apply$ add (list left right)))

(defun putnam-2008-a5-mul (mul left right)
  (apply$ mul (list left right)))

(defun putnam-2008-a5-neg (neg value)
  (apply$ neg (list value)))

(defun putnam-2008-a5-less-p (lt left right)
  (apply$ lt (list left right)))

(defun putnam-2008-a5-evaluate (evaluate polynomial x)
  (apply$ evaluate (list polynomial x)))

(defun putnam-2008-a5-coefficient-list-p
    (coefficients carrier)
  (if (endp coefficients)
      (equal coefficients nil)
    (and
     (apply$ carrier (list (car coefficients)))
     (putnam-2008-a5-coefficient-list-p
      (cdr coefficients) carrier))))

(defun putnam-2008-a5-polynomial-p
    (polynomial carrier zero)
  (and
   (true-listp polynomial)
   (consp polynomial)
   (putnam-2008-a5-coefficient-list-p
    polynomial carrier)
   (or
    (equal (len polynomial) 1)
    (not (equal (car (last polynomial)) zero)))))

(defun putnam-2008-a5-polynomial-degree (polynomial)
  (- (len polynomial) 1))

(defun putnam-2008-a5-nat-value (zero one add n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (if (equal n 1)
        one
      (putnam-2008-a5-add
       add one
       (putnam-2008-a5-nat-value
        zero one add (- n 1))))))

;; A complex value is represented by (real-part . imaginary-part).

(defun putnam-2008-a5-complex-add (add left right)
  (cons
   (putnam-2008-a5-add add (car left) (car right))
   (putnam-2008-a5-add add (cdr left) (cdr right))))

(defun putnam-2008-a5-complex-mul
    (add mul neg left right)
  (let* ((ac
          (putnam-2008-a5-mul
           mul (car left) (car right)))
         (bd
          (putnam-2008-a5-mul
           mul (cdr left) (cdr right)))
         (ad
          (putnam-2008-a5-mul
           mul (car left) (cdr right)))
         (bc
          (putnam-2008-a5-mul
           mul (cdr left) (car right))))
    (cons
     (putnam-2008-a5-add
      add ac (putnam-2008-a5-neg neg bd))
     (putnam-2008-a5-add add ad bc))))

(defun putnam-2008-a5-complex-power
    (zero one add mul neg base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (cons one zero)
    (putnam-2008-a5-complex-mul
     add
     mul
     neg
     base
     (putnam-2008-a5-complex-power
      zero one add mul neg base (- exponent 1)))))

(defun putnam-2008-a5-root-candidate-p
    (carrier zero one add mul neg lt n real imaginary)
  (and
   (apply$ carrier (list real))
   (apply$ carrier (list imaginary))
   (putnam-2008-a5-less-p lt zero imaginary)
   (equal
    (putnam-2008-a5-complex-power
     zero one add mul neg (cons real imaginary) n)
    (cons one zero))))

(defun putnam-2008-a5-complex-add-function (add)
  (list
   'lambda
   '(left right)
   (list
    'cons
    (putnam-2008-a5-operation-term
     add (list 'car 'left) (list 'car 'right))
    (putnam-2008-a5-operation-term
     add (list 'cdr 'left) (list 'cdr 'right)))))

(defun putnam-2008-a5-complex-mul-function (add mul neg)
  (let* ((left-real (list 'car 'left))
         (left-imaginary (list 'cdr 'left))
         (right-real (list 'car 'right))
         (right-imaginary (list 'cdr 'right))
         (real-part
          (putnam-2008-a5-operation-term
           add
           (putnam-2008-a5-operation-term
            mul left-real right-real)
           (putnam-2008-a5-apply1-term
            neg
            (putnam-2008-a5-operation-term
             mul left-imaginary right-imaginary))))
         (imaginary-part
          (putnam-2008-a5-operation-term
           add
           (putnam-2008-a5-operation-term
            mul left-real right-imaginary)
           (putnam-2008-a5-operation-term
            mul left-imaginary right-real))))
    (list
     'lambda
     '(left right)
     (list 'cons real-part imaginary-part))))

(defun putnam-2008-a5-complex-power-term
    (zero one add mul neg base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list
       'cons
       (putnam-2008-a5-quoted one)
       (putnam-2008-a5-quoted zero))
    (putnam-2008-a5-apply2-term
     (putnam-2008-a5-complex-mul-function add mul neg)
     base
     (putnam-2008-a5-complex-power-term
      zero one add mul neg base (- exponent 1)))))

(defun putnam-2008-a5-root-candidate-term
    (carrier zero one add mul neg lt n real imaginary)
  (let ((power
         (putnam-2008-a5-complex-power-term
          zero
          one
          add
          mul
          neg
          (list 'cons real imaginary)
          n)))
    (putnam-2008-a5-and-term
     (list
      (putnam-2008-a5-carrier-term carrier real)
      (putnam-2008-a5-carrier-term carrier imaginary)
      (putnam-2008-a5-operation-term
       lt (putnam-2008-a5-quoted zero) imaginary)
      (list
       'equal
       power
       (list
        'cons
        (putnam-2008-a5-quoted one)
        (putnam-2008-a5-quoted zero)))))))

(defun putnam-2008-a5-root-maximality-function
    (carrier zero one add mul neg lt n root-real)
  (list
   'lambda
   '(real imaginary)
   (list
    'if
    (putnam-2008-a5-root-candidate-term
     carrier zero one add mul neg lt n
     'real 'imaginary)
    (list
     'if
     (putnam-2008-a5-operation-term
      lt
      (putnam-2008-a5-quoted root-real)
      'real)
     (putnam-2008-a5-quoted nil)
     (putnam-2008-a5-quoted t))
    (putnam-2008-a5-quoted t))))

(defun putnam-2008-a5-distinguished-root-p
    (carrier zero one add mul neg lt n root-real root-imaginary)
  (let ((maximality
         (putnam-2008-a5-root-maximality-function
          carrier zero one add mul neg lt n root-real))
        (true-on-two
         (putnam-2008-a5-true-function '(real imaginary))))
    (and
     (putnam-2008-a5-root-candidate-p
      carrier zero one add mul neg lt
      n root-real root-imaginary)
     (tamep-functionp maximality)
     (tamep-functionp true-on-two)
     (fn-equal maximality true-on-two))))

(defun putnam-2008-a5-nat-value-term (zero one add n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-2008-a5-quoted zero)
    (if (equal n 1)
        (putnam-2008-a5-quoted one)
      (putnam-2008-a5-operation-term
       add
       (putnam-2008-a5-quoted one)
       (putnam-2008-a5-nat-value-term
        zero one add (- n 1))))))

(defun putnam-2008-a5-point-term
    (evaluate f g x)
  (list
   'cons
   (putnam-2008-a5-operation-term
    evaluate (putnam-2008-a5-quoted f) x)
   (putnam-2008-a5-operation-term
    evaluate (putnam-2008-a5-quoted g) x)))

(defun putnam-2008-a5-regular-equation-term
    (zero one add mul neg evaluate
          f g root center scale k)
  (let* ((x
          (putnam-2008-a5-nat-value-term
           zero one add k))
         (point
          (putnam-2008-a5-point-term
           evaluate f g x))
         (root-power
          (putnam-2008-a5-complex-power-term
           zero one add mul neg root k))
         (scaled-power
          (putnam-2008-a5-apply2-term
           (putnam-2008-a5-complex-mul-function
            add mul neg)
           scale
           root-power))
         (translated-power
          (putnam-2008-a5-apply2-term
           (putnam-2008-a5-complex-add-function add)
           center
           scaled-power)))
    (list 'equal point translated-power)))

(defun putnam-2008-a5-regular-equations-term
    (zero one add mul neg evaluate
          f g root center scale k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-2008-a5-quoted t)
    (putnam-2008-a5-and-term
     (list
      (putnam-2008-a5-regular-equation-term
       zero one add mul neg evaluate
       f g root center scale k)
      (putnam-2008-a5-regular-equations-term
       zero one add mul neg evaluate
       f g root center scale
       (+ k 1) (- remaining 1))))))

(defun putnam-2008-a5-point
    (zero one add evaluate f g k)
  (let ((x (putnam-2008-a5-nat-value
            zero one add k)))
    (cons
     (putnam-2008-a5-evaluate evaluate f x)
     (putnam-2008-a5-evaluate evaluate g x))))

(defun putnam-2008-a5-regular-equations-p
    (zero one add mul neg evaluate
          f g root center scale k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (putnam-2008-a5-point
       zero one add evaluate f g k)
      (putnam-2008-a5-complex-add
       add
       center
       (putnam-2008-a5-complex-mul
        add
        mul
        neg
        scale
        (putnam-2008-a5-complex-power
         zero one add mul neg root k))))
     (putnam-2008-a5-regular-equations-p
      zero one add mul neg evaluate
      f g root center scale (+ k 1) (- remaining 1)))))

(defun putnam-2008-a5-regular-witness-p
    (carrier zero one add mul neg evaluate
             n f g root-real root-imaginary witness)
  (and
   (true-listp witness)
   (equal (len witness) 4)
   (apply$ carrier (list (nth 0 witness)))
   (apply$ carrier (list (nth 1 witness)))
   (apply$ carrier (list (nth 2 witness)))
   (apply$ carrier (list (nth 3 witness)))
   (or
    (not (equal (nth 2 witness) zero))
    (not (equal (nth 3 witness) zero)))
   (putnam-2008-a5-regular-equations-p
    zero
    one
    add
    mul
    neg
    evaluate
    f
    g
    (cons root-real root-imaginary)
    (cons (nth 0 witness) (nth 1 witness))
    (cons (nth 2 witness) (nth 3 witness))
    1
    n)))

(defun putnam-2008-a5-witness-failure-function
    (carrier zero one add mul neg evaluate
             n f g root-real root-imaginary)
  (let* ((center-real
          (list 'car 'witness))
         (center-imaginary
          (list 'car (list 'cdr 'witness)))
         (scale-real
          (list
           'car
           (list 'cdr (list 'cdr 'witness))))
         (scale-imaginary
          (list
           'car
           (list
            'cdr
            (list 'cdr (list 'cdr 'witness)))))
         (root
          (list
           'cons
           (putnam-2008-a5-quoted root-real)
           (putnam-2008-a5-quoted root-imaginary)))
         (center
          (list 'cons center-real center-imaginary))
         (scale
          (list 'cons scale-real scale-imaginary))
         (qualification
          (putnam-2008-a5-and-term
           (list
            (list 'true-listp 'witness)
            (list
             'equal
             (list 'len 'witness)
             (putnam-2008-a5-quoted 4))
            (putnam-2008-a5-carrier-term
             carrier center-real)
            (putnam-2008-a5-carrier-term
             carrier center-imaginary)
            (putnam-2008-a5-carrier-term
             carrier scale-real)
            (putnam-2008-a5-carrier-term
             carrier scale-imaginary)
            (putnam-2008-a5-or-term
             (list
              (putnam-2008-a5-not-term
               (list
                'equal
                scale-real
                (putnam-2008-a5-quoted zero)))
              (putnam-2008-a5-not-term
               (list
                'equal
                scale-imaginary
                (putnam-2008-a5-quoted zero)))))
            (putnam-2008-a5-regular-equations-term
             zero one add mul neg evaluate
             f g root center scale 1 n)))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2008-a5-quoted nil)
      (putnam-2008-a5-quoted t)))))

(defun putnam-2008-a5-regular-configuration-exists-p
    (carrier zero one add mul neg evaluate
             n f g root-real root-imaginary)
  (let ((failure
         (putnam-2008-a5-witness-failure-function
          carrier zero one add mul neg evaluate
          n f g root-real root-imaginary))
        (true-on-one
         (putnam-2008-a5-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp true-on-one)
     (not (fn-equal failure true-on-one)))))

(defun putnambench-putnam-2008-a5-statement
    (carrier zero one add mul neg inv lt
             square-root odd-root evaluate
             n f g root-real root-imaginary)
  (implies
   (and
    (natp n)
    (<= 3 n)
    (putnam-2008-a5-real-closed-field-p
     carrier zero one add mul neg inv lt
     square-root odd-root evaluate)
    (putnam-2008-a5-polynomial-p f carrier zero)
    (putnam-2008-a5-polynomial-p g carrier zero)
    (putnam-2008-a5-distinguished-root-p
     carrier zero one add mul neg lt
     n root-real root-imaginary)
    (putnam-2008-a5-regular-configuration-exists-p
     carrier zero one add mul neg evaluate
     n f g root-real root-imaginary))
   (or
    (<= (- n 1)
        (putnam-2008-a5-polynomial-degree f))
    (<= (- n 1)
        (putnam-2008-a5-polynomial-degree g)))))

(value-triple :itpeval-statement-checked)
:q
