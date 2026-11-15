;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_b5:
;; a real multivariate polynomial that is harmonic and divisible by the sum
;; of the squares of its variables is identically zero. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Coefficients live in a represented real closed field. Sparse polynomials
;; are canonical lists of (coefficient exponent-vector) terms, ordered
;; lexicographically by exponent vector. This is an exact representation of
;; real multivariate polynomials, not a restriction to ACL2 rationals.
;;
;; The formal Laplacian is computed term by term. Divisibility by
;; x_0^2+...+x_(n-1)^2 is decided by the standard single-divisor multivariate
;; division algorithm. Since the divisor is monic, zero remainder is
;; equivalent to the source's internal existential polynomial quotient.

(defun putnam-2005-b5-quoted (object)
  (list 'quote object))

(defun putnam-2005-b5-apply1-term (function argument)
  (list
   'apply$
   (putnam-2005-b5-quoted function)
   (list 'cons argument nil)))

(defun putnam-2005-b5-apply2-term (function left right)
  (list
   'apply$
   (putnam-2005-b5-quoted function)
   (list 'cons left (list 'cons right nil))))

(defun putnam-2005-b5-and-term (terms)
  (if (endp terms)
      (putnam-2005-b5-quoted t)
    (list
     'if
     (car terms)
     (putnam-2005-b5-and-term (cdr terms))
     (putnam-2005-b5-quoted nil))))

(defun putnam-2005-b5-or-term (terms)
  (if (endp terms)
      (putnam-2005-b5-quoted nil)
    (list
     'if
     (car terms)
     (putnam-2005-b5-quoted t)
     (putnam-2005-b5-or-term (cdr terms)))))

(defun putnam-2005-b5-not-term (term)
  (list
   'if
   term
   (putnam-2005-b5-quoted nil)
   (putnam-2005-b5-quoted t)))

(defun putnam-2005-b5-implies-term (antecedent consequent)
  (list
   'if
   antecedent
   consequent
   (putnam-2005-b5-quoted t)))

(defun putnam-2005-b5-true-function (formals)
  (list
   'lambda
   formals
   (putnam-2005-b5-quoted t)))

(defun putnam-2005-b5-carrier-term (carrier element)
  (putnam-2005-b5-apply1-term carrier element))

(defun putnam-2005-b5-operation-term (operation left right)
  (putnam-2005-b5-apply2-term operation left right))

(defun putnam-2005-b5-all-coefficients-function (carrier)
  (list
   'lambda
   '(loop$-gvars loop$-ivars)
   (putnam-2005-b5-apply1-term
    carrier 'loop$-ivars)))

(defun putnam-2005-b5-all-coefficients-term
    (carrier coefficients)
  (list
   'always$+
   (putnam-2005-b5-quoted
    (putnam-2005-b5-all-coefficients-function
     carrier))
   (putnam-2005-b5-quoted nil)
   coefficients))

(defun putnam-2005-b5-univariate-polynomial-term
    (carrier zero coefficients)
  (putnam-2005-b5-and-term
   (list
    (list 'true-listp coefficients)
    (list 'consp coefficients)
    (putnam-2005-b5-all-coefficients-term
     carrier coefficients)
    (putnam-2005-b5-or-term
     (list
      (list 'equal
            (list 'len coefficients)
            (putnam-2005-b5-quoted 1))
      (putnam-2005-b5-not-term
       (list 'equal
             (list 'car (list 'last coefficients))
             (putnam-2005-b5-quoted zero))))))))

(defun putnam-2005-b5-field-laws-function
    (carrier zero one add mul neg inv)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2005-b5-quoted zero))
         (qone (putnam-2005-b5-quoted one))
         (add-xy
          (putnam-2005-b5-operation-term add x y))
         (add-yz
          (putnam-2005-b5-operation-term add y z))
         (mul-xy
          (putnam-2005-b5-operation-term mul x y))
         (mul-yz
          (putnam-2005-b5-operation-term mul y z))
         (neg-x
          (putnam-2005-b5-apply1-term neg x))
         (inv-x
          (putnam-2005-b5-apply1-term inv x))
         (domain
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term carrier x)
            (putnam-2005-b5-carrier-term carrier y)
            (putnam-2005-b5-carrier-term carrier z))))
         (laws
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term carrier add-xy)
            (putnam-2005-b5-carrier-term carrier mul-xy)
            (putnam-2005-b5-carrier-term carrier neg-x)
            (putnam-2005-b5-carrier-term carrier inv-x)
            (list
             'equal
             (putnam-2005-b5-operation-term add add-xy z)
             (putnam-2005-b5-operation-term add x add-yz))
            (list
             'equal
             (putnam-2005-b5-operation-term mul mul-xy z)
             (putnam-2005-b5-operation-term mul x mul-yz))
            (list
             'equal
             add-xy
             (putnam-2005-b5-operation-term add y x))
            (list
             'equal
             mul-xy
             (putnam-2005-b5-operation-term mul y x))
            (list
             'equal
             (putnam-2005-b5-operation-term add x qzero)
             x)
            (list
             'equal
             (putnam-2005-b5-operation-term add x neg-x)
             qzero)
            (list
             'equal
             (putnam-2005-b5-operation-term mul x qone)
             x)
            (putnam-2005-b5-implies-term
             (list 'equal x qzero)
             (list 'equal inv-x qzero))
            (putnam-2005-b5-implies-term
             (putnam-2005-b5-not-term
              (list 'equal x qzero))
             (list
              'equal
              (putnam-2005-b5-operation-term mul x inv-x)
              qone))
            (list
             'equal
             (putnam-2005-b5-operation-term mul x add-yz)
             (putnam-2005-b5-operation-term
              add
              (putnam-2005-b5-operation-term mul x y)
              (putnam-2005-b5-operation-term mul x z)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2005-b5-implies-term domain laws))))

(defun putnam-2005-b5-order-laws-function
    (carrier zero add mul lt)
  (let* ((x 'x)
         (y 'y)
         (z 'z)
         (qzero (putnam-2005-b5-quoted zero))
         (lt-xy
          (putnam-2005-b5-operation-term lt x y))
         (lt-yx
          (putnam-2005-b5-operation-term lt y x))
         (lt-yz
          (putnam-2005-b5-operation-term lt y z))
         (lt-xz
          (putnam-2005-b5-operation-term lt x z))
         (domain
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term carrier x)
            (putnam-2005-b5-carrier-term carrier y)
            (putnam-2005-b5-carrier-term carrier z))))
         (laws
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-not-term
             (putnam-2005-b5-operation-term lt x x))
            (putnam-2005-b5-or-term
             (list
              lt-xy
              (list 'equal x y)
              lt-yx))
            (putnam-2005-b5-implies-term
             (putnam-2005-b5-and-term
              (list lt-xy lt-yz))
             lt-xz)
            (putnam-2005-b5-implies-term
             lt-xy
             (putnam-2005-b5-operation-term
              lt
              (putnam-2005-b5-operation-term add x z)
              (putnam-2005-b5-operation-term add y z)))
            (putnam-2005-b5-implies-term
             (putnam-2005-b5-and-term
              (list
               (putnam-2005-b5-operation-term lt qzero x)
               (putnam-2005-b5-operation-term lt qzero y)))
             (putnam-2005-b5-operation-term
              lt
              qzero
              (putnam-2005-b5-operation-term mul x y)))))))
    (list
     'lambda
     '(x y z)
     (putnam-2005-b5-implies-term domain laws))))

(defun putnam-2005-b5-square-root-laws-function
    (carrier zero mul lt square-root)
  (let* ((x 'x)
         (qzero (putnam-2005-b5-quoted zero))
         (root
          (putnam-2005-b5-apply1-term square-root x))
         (domain
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term carrier x)
            (putnam-2005-b5-not-term
             (putnam-2005-b5-operation-term lt x qzero)))))
         (laws
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term carrier root)
            (list
             'equal
             (putnam-2005-b5-operation-term mul root root)
             x)))))
    (list
     'lambda
     '(x)
     (putnam-2005-b5-implies-term domain laws))))

(defun putnam-2005-b5-evaluation-laws-function
    (carrier zero add mul evaluate)
  (let* ((coefficient 'coefficient)
         (rest 'rest)
         (x 'x)
         (qzero (putnam-2005-b5-quoted zero))
         (domain
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term
             carrier coefficient)
            (list 'true-listp rest)
            (putnam-2005-b5-all-coefficients-term
             carrier rest)
            (putnam-2005-b5-carrier-term carrier x))))
         (empty-law
          (putnam-2005-b5-implies-term
           (putnam-2005-b5-carrier-term carrier x)
           (list
            'equal
            (putnam-2005-b5-operation-term
             evaluate
             (putnam-2005-b5-quoted nil)
             x)
            qzero)))
         (recursive-value
          (putnam-2005-b5-operation-term
           add
           coefficient
           (putnam-2005-b5-operation-term
            mul
            x
            (putnam-2005-b5-operation-term
             evaluate rest x))))
         (recursive-law
          (putnam-2005-b5-implies-term
           domain
           (putnam-2005-b5-and-term
            (list
             (putnam-2005-b5-carrier-term
              carrier
              (putnam-2005-b5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x))
             (list
              'equal
              (putnam-2005-b5-operation-term
               evaluate
               (list 'cons coefficient rest)
               x)
              recursive-value))))))
    (list
     'lambda
     '(coefficient rest x)
     (putnam-2005-b5-and-term
      (list empty-law recursive-law)))))

(defun putnam-2005-b5-odd-root-laws-function
    (carrier zero evaluate odd-root)
  (let* ((coefficients 'coefficients)
         (root
          (putnam-2005-b5-apply1-term
           odd-root coefficients))
         (domain
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-univariate-polynomial-term
             carrier zero coefficients)
            (list 'evenp (list 'len coefficients)))))
         (laws
          (putnam-2005-b5-and-term
           (list
            (putnam-2005-b5-carrier-term carrier root)
            (list
             'equal
             (putnam-2005-b5-operation-term
              evaluate coefficients root)
             (putnam-2005-b5-quoted zero))))))
    (list
     'lambda
     '(coefficients)
     (putnam-2005-b5-implies-term domain laws))))

(defun putnam-2005-b5-real-closed-field-p
    (carrier zero one add mul neg inv lt square-root
             evaluate odd-root)
  (let* ((field-laws
          (putnam-2005-b5-field-laws-function
           carrier zero one add mul neg inv))
         (order-laws
          (putnam-2005-b5-order-laws-function
           carrier zero add mul lt))
         (square-root-laws
          (putnam-2005-b5-square-root-laws-function
           carrier zero mul lt square-root))
         (evaluation-laws
          (putnam-2005-b5-evaluation-laws-function
           carrier zero add mul evaluate))
         (odd-root-laws
          (putnam-2005-b5-odd-root-laws-function
           carrier zero evaluate odd-root))
         (true-ternary
          (putnam-2005-b5-true-function '(x y z)))
         (true-unary
          (putnam-2005-b5-true-function '(x)))
         (true-evaluation
          (putnam-2005-b5-true-function
           '(coefficient rest x)))
         (true-polynomial
          (putnam-2005-b5-true-function '(coefficients))))
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
     (tamep-functionp order-laws)
     (tamep-functionp square-root-laws)
     (tamep-functionp evaluation-laws)
     (tamep-functionp odd-root-laws)
     (tamep-functionp true-ternary)
     (tamep-functionp true-unary)
     (tamep-functionp true-evaluation)
     (tamep-functionp true-polynomial)
     (apply$ carrier (list zero))
     (apply$ carrier (list one))
     (not (equal zero one))
     (fn-equal field-laws true-ternary)
     (fn-equal order-laws true-ternary)
     (fn-equal square-root-laws true-unary)
     (fn-equal evaluation-laws true-evaluation)
     (fn-equal odd-root-laws true-polynomial))))

(defun putnam-2005-b5-nat-listp (values)
  (if (consp values)
      (and (natp (car values))
           (putnam-2005-b5-nat-listp (cdr values)))
    (equal values nil)))

(defun putnam-2005-b5-exponents-gt (left right)
  (if (consp left)
      (cond
       ((< (nfix (car right)) (nfix (car left))) t)
       ((< (nfix (car left)) (nfix (car right))) nil)
       (t
        (putnam-2005-b5-exponents-gt
         (cdr left) (cdr right))))
    nil))

(defun putnam-2005-b5-term-p
    (term n carrier zero)
  (and
   (true-listp term)
   (equal (len term) 2)
   (apply$ carrier (list (car term)))
   (not (equal (car term) zero))
   (true-listp (cadr term))
   (equal (len (cadr term)) n)
   (putnam-2005-b5-nat-listp (cadr term))))

(defun putnam-2005-b5-polynomial-p
    (polynomial n carrier zero)
  (if (consp polynomial)
      (and
       (putnam-2005-b5-term-p
        (car polynomial) n carrier zero)
       (or
        (endp (cdr polynomial))
        (putnam-2005-b5-exponents-gt
         (cadar polynomial)
         (cadadr polynomial)))
       (putnam-2005-b5-polynomial-p
        (cdr polynomial) n carrier zero))
    (equal polynomial nil)))

(defun putnam-2005-b5-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (apply$
     add
     (list
      one
      (putnam-2005-b5-field-natural
       (- n 1) zero one add)))))

(defun putnam-2005-b5-exponents-add (left right)
  (if (consp left)
      (cons
       (+ (nfix (car left)) (nfix (car right)))
       (putnam-2005-b5-exponents-add
        (cdr left) (cdr right)))
    nil))

(defun putnam-2005-b5-exponents-divide-p
    (divisor dividend)
  (if (consp divisor)
      (and
       (<= (nfix (car divisor)) (nfix (car dividend)))
       (putnam-2005-b5-exponents-divide-p
        (cdr divisor) (cdr dividend)))
    t))

(defun putnam-2005-b5-exponents-subtract
    (dividend divisor)
  (if (consp dividend)
      (cons
       (- (nfix (car dividend)) (nfix (car divisor)))
       (putnam-2005-b5-exponents-subtract
        (cdr dividend) (cdr divisor)))
    nil))

(defun putnam-2005-b5-insert-term
    (term polynomial add zero)
  (let ((coefficient (car term))
        (exponents (cadr term)))
    (cond
     ((equal coefficient zero)
      polynomial)
     ((endp polynomial)
      (list term))
     ((equal exponents (cadar polynomial))
      (let ((new-coefficient
             (apply$
              add
              (list coefficient (caar polynomial)))))
        (if (equal new-coefficient zero)
            (cdr polynomial)
          (cons
           (list new-coefficient exponents)
           (cdr polynomial)))))
     ((putnam-2005-b5-exponents-gt
       exponents (cadar polynomial))
      (cons term polynomial))
     (t
      (cons
       (car polynomial)
       (putnam-2005-b5-insert-term
        term (cdr polynomial) add zero))))))

(defun putnam-2005-b5-poly-add
    (left right add zero)
  (if (consp left)
      (putnam-2005-b5-insert-term
       (car left)
       (putnam-2005-b5-poly-add
        (cdr left) right add zero)
       add zero)
    right))

(defun putnam-2005-b5-poly-neg
    (polynomial neg)
  (if (consp polynomial)
      (cons
       (list
        (apply$ neg (list (caar polynomial)))
        (cadar polynomial))
       (putnam-2005-b5-poly-neg
        (cdr polynomial) neg))
    nil))

(defun putnam-2005-b5-poly-sub
    (left right add neg zero)
  (putnam-2005-b5-poly-add
   left
   (putnam-2005-b5-poly-neg right neg)
   add zero))

(defun putnam-2005-b5-monomial-times-poly
    (term polynomial mul add zero)
  (if (or (equal (car term) zero)
          (endp polynomial))
      nil
    (putnam-2005-b5-insert-term
     (list
      (apply$ mul (list (car term) (caar polynomial)))
      (putnam-2005-b5-exponents-add
       (cadr term) (cadar polynomial)))
     (putnam-2005-b5-monomial-times-poly
      term (cdr polynomial) mul add zero)
     add zero)))

(defun putnam-2005-b5-poly-mul
    (left right add mul zero)
  (if (consp left)
      (putnam-2005-b5-poly-add
       (putnam-2005-b5-monomial-times-poly
        (car left) right mul add zero)
       (putnam-2005-b5-poly-mul
        (cdr left) right add mul zero)
       add zero)
    nil))

(defun putnam-2005-b5-total-degree (exponents)
  (if (consp exponents)
      (+ (nfix (car exponents))
         (putnam-2005-b5-total-degree (cdr exponents)))
    0))

(defun putnam-2005-b5-max-total-degree (polynomial)
  (if (consp polynomial)
      (max
       (putnam-2005-b5-total-degree (cadar polynomial))
       (putnam-2005-b5-max-total-degree (cdr polynomial)))
    0))

(defun putnam-2005-b5-zero-exponents (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons
     0
     (putnam-2005-b5-zero-exponents (- n 1)))))

(defun putnam-2005-b5-unit-square-exponents
    (n index)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (if (zp index)
        (cons
         2
         (putnam-2005-b5-zero-exponents (- n 1)))
      (cons
       0
       (putnam-2005-b5-unit-square-exponents
        (- n 1) (- index 1))))))

(defun putnam-2005-b5-sum-squares-aux
    (remaining index n one add zero)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (putnam-2005-b5-insert-term
     (list
      one
      (putnam-2005-b5-unit-square-exponents
       n index))
     (putnam-2005-b5-sum-squares-aux
      (- remaining 1) (+ 1 (nfix index))
      n one add zero)
     add zero)))

(defun putnam-2005-b5-sum-squares
    (n one add zero)
  (putnam-2005-b5-sum-squares-aux
   n 0 n one add zero))

(defun putnam-2005-b5-lower-exponent-by-two
    (exponents index)
  (if (consp exponents)
      (if (zp index)
          (cons (- (nfix (car exponents)) 2)
                (cdr exponents))
        (cons
         (car exponents)
         (putnam-2005-b5-lower-exponent-by-two
          (cdr exponents) (- (nfix index) 1))))
    nil))

(defun putnam-2005-b5-second-derivative-term
    (term index zero one add mul)
  (let* ((exponents (cadr term))
         (exponent (nfix (nth index exponents))))
    (if (< exponent 2)
        nil
      (let* ((k
              (putnam-2005-b5-field-natural
               exponent zero one add))
             (k-minus-one
              (putnam-2005-b5-field-natural
               (- exponent 1) zero one add))
             (factor
              (apply$ mul (list k k-minus-one)))
             (coefficient
              (apply$ mul (list (car term) factor))))
        (list
         coefficient
         (putnam-2005-b5-lower-exponent-by-two
          exponents index))))))

(defun putnam-2005-b5-second-derivative
    (polynomial index zero one add mul)
  (if (consp polynomial)
      (let ((term
             (putnam-2005-b5-second-derivative-term
              (car polynomial) index zero one add mul)))
        (if (consp term)
            (putnam-2005-b5-insert-term
             term
             (putnam-2005-b5-second-derivative
              (cdr polynomial) index zero one add mul)
             add zero)
          (putnam-2005-b5-second-derivative
           (cdr polynomial) index zero one add mul)))
    nil))

(defun putnam-2005-b5-laplacian-aux
    (remaining index polynomial zero one add mul)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (putnam-2005-b5-poly-add
     (putnam-2005-b5-second-derivative
      polynomial index zero one add mul)
     (putnam-2005-b5-laplacian-aux
      (- remaining 1) (+ 1 (nfix index))
      polynomial zero one add mul)
     add zero)))

(defun putnam-2005-b5-laplacian
    (n polynomial zero one add mul)
  (putnam-2005-b5-laplacian-aux
   n 0 polynomial zero one add mul))

(defun putnam-2005-b5-divides-fuel
    (dividend divisor add mul neg inv zero fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond
   ((endp dividend) t)
   ((or (zp fuel) (endp divisor)) nil)
   ((not
     (putnam-2005-b5-exponents-divide-p
      (cadar divisor) (cadar dividend)))
    nil)
   (t
    (let* ((quotient-coefficient
            (apply$
             mul
             (list
              (caar dividend)
              (apply$ inv (list (caar divisor))))))
           (quotient-exponents
            (putnam-2005-b5-exponents-subtract
             (cadar dividend) (cadar divisor)))
           (multiple
            (putnam-2005-b5-monomial-times-poly
             (list quotient-coefficient quotient-exponents)
             divisor mul add zero))
           (reduced
            (putnam-2005-b5-poly-sub
             dividend multiple add neg zero)))
      (putnam-2005-b5-divides-fuel
       reduced divisor add mul neg inv zero
       (- fuel 1))))))

(defun putnam-2005-b5-divides-p
    (divisor dividend n add mul neg inv zero)
  (let* ((degree
          (putnam-2005-b5-max-total-degree dividend))
         (fuel
          (expt (+ 1 degree) (nfix n))))
    (putnam-2005-b5-divides-fuel
     dividend divisor add mul neg inv zero fuel)))

(defun putnambench-putnam-2005-b5-statement
    (carrier zero one add mul neg inv lt square-root
             evaluate odd-root n polynomial)
  (implies
   (and
    (putnam-2005-b5-real-closed-field-p
     carrier zero one add mul neg inv lt square-root
     evaluate odd-root)
    (natp n)
    (< 0 n)
    (putnam-2005-b5-polynomial-p
     polynomial n carrier zero)
    (equal
     (putnam-2005-b5-laplacian
      n polynomial zero one add mul)
     nil)
    (putnam-2005-b5-divides-p
     (putnam-2005-b5-sum-squares
      n one add zero)
     polynomial n add mul neg inv zero))
   (equal polynomial nil)))

(value-triple :itpeval-statement-checked)
:q
