;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q6783821, "Mason–Stothers theorem": over an
;; arbitrary field, three nonzero polynomials with coprime first two terms
;; and sum zero satisfy the three polynomial-ABC radical degree bounds,
;; unless all three derivatives vanish. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar field and its polynomial algebra are arbitrary tame APPLY$
;; function objects.  COORDINATES and REALIZE give a bijection between the
;; polynomial carrier and canonical ascending finite coefficient lists.
;; Horner's recursion makes this presentation isomorphic to the full
;; univariate polynomial ring, rather than a bounded-degree approximation.
;;
;; Choice selectors for Bezout witnesses, quotients, nontrivial factorizations,
;; and repeated irreducible factors are constrained in both directions.  They
;; therefore package classical choices for internal existentials without
;; turning any theorem witness into an extra hypothesis.

(defun q6783821-quoted (object)
  (list 'quote object))

(defun q6783821-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q6783821-term-list (cdr terms)))
    (q6783821-quoted nil)))

(defun q6783821-static-apply-term (function arguments)
  (list 'apply$
        (q6783821-quoted function)
        (q6783821-term-list arguments)))

(defun q6783821-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q6783821-and-terms (cdr terms))
            (q6783821-quoted nil))
    (q6783821-quoted t)))

(defun q6783821-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q6783821-quoted t)
            (q6783821-or-terms (cdr terms)))
    (q6783821-quoted nil)))

(defun q6783821-not-term (term)
  (list 'if term
        (q6783821-quoted nil)
        (q6783821-quoted t)))

(defun q6783821-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q6783821-quoted t)))

(defun q6783821-iff-term (left right)
  (list 'if left
        (list 'if right
              (q6783821-quoted t)
              (q6783821-quoted nil))
        (list 'if right
              (q6783821-quoted nil)
              (q6783821-quoted t))))

(defun q6783821-true-function (formals)
  (list 'lambda formals (q6783821-quoted t)))

(defun q6783821-universal-p (function formals)
  (let ((always-true (q6783821-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q6783821-member-p (carrier object)
  (if (apply$ carrier (list object)) t nil))

(defun q6783821-unary-value (function object)
  (apply$ function (list object)))

(defun q6783821-binary-value (function left right)
  (apply$ function (list left right)))

(defun q6783821-canonical-coefficients-term
    (coefficients scalarp scalar-zero)
  (q6783821-and-terms
   (list
    (list 'true-listp coefficients)
    (list 'always$ (q6783821-quoted scalarp) coefficients)
    (q6783821-or-terms
     (list
      (list 'equal coefficients (q6783821-quoted nil))
      (q6783821-not-term
       (list
        'equal
        (list 'car (list 'last coefficients))
        (q6783821-quoted scalar-zero))))))))

(defun q6783821-polynomial-term (polyp polynomial)
  (q6783821-static-apply-term polyp (list polynomial)))

(defun q6783821-unit-term (polyp coordinates polynomial)
  (let ((coefficients
         (q6783821-static-apply-term coordinates (list polynomial))))
    (q6783821-and-terms
     (list
      (q6783821-polynomial-term polyp polynomial)
      (list 'consp coefficients)
      (list 'endp (list 'cdr coefficients))))))

;; An arbitrary nontrivial commutative field.

(defun q6783821-field-laws-function
    (scalarp zero one add multiply negate inverse)
  (let* ((add-xy (q6783821-static-apply-term add '(x y)))
         (add-yz (q6783821-static-apply-term add '(y z)))
         (mul-xy (q6783821-static-apply-term multiply '(x y)))
         (mul-yz (q6783821-static-apply-term multiply '(y z)))
         (neg-x (q6783821-static-apply-term negate '(x)))
         (inv-x (q6783821-static-apply-term inverse '(x)))
         (domain
          (q6783821-and-terms
           (list
            (q6783821-static-apply-term scalarp '(x))
            (q6783821-static-apply-term scalarp '(y))
            (q6783821-static-apply-term scalarp '(z))))))
    (list
     'lambda '(x y z)
     (q6783821-implies-term
      domain
      (q6783821-and-terms
       (list
        (q6783821-static-apply-term scalarp (list add-xy))
        (q6783821-static-apply-term scalarp (list mul-xy))
        (q6783821-static-apply-term scalarp (list neg-x))
        (q6783821-static-apply-term scalarp (list inv-x))
        (list 'equal
              (q6783821-static-apply-term add (list add-xy 'z))
              (q6783821-static-apply-term add (list 'x add-yz)))
        (list 'equal add-xy
              (q6783821-static-apply-term add '(y x)))
        (list 'equal
              (q6783821-static-apply-term
               add (list 'x (q6783821-quoted zero)))
              'x)
        (list 'equal
              (q6783821-static-apply-term add (list 'x neg-x))
              (q6783821-quoted zero))
        (list 'equal
              (q6783821-static-apply-term multiply (list mul-xy 'z))
              (q6783821-static-apply-term multiply (list 'x mul-yz)))
        (list 'equal mul-xy
              (q6783821-static-apply-term multiply '(y x)))
        (list 'equal
              (q6783821-static-apply-term
               multiply (list 'x (q6783821-quoted one)))
              'x)
        (list 'equal
              (q6783821-static-apply-term multiply (list 'x add-yz))
              (q6783821-static-apply-term
               add
               (list
                (q6783821-static-apply-term multiply '(x y))
                (q6783821-static-apply-term multiply '(x z)))))
        (q6783821-implies-term
         (list 'equal 'x (q6783821-quoted zero))
         (list 'equal inv-x (q6783821-quoted zero)))
        (q6783821-implies-term
         (q6783821-not-term
          (list 'equal 'x (q6783821-quoted zero)))
         (list 'equal
               (q6783821-static-apply-term multiply (list 'x inv-x))
               (q6783821-quoted one)))))))))

(defun q6783821-field-p
    (scalarp zero one add multiply negate inverse)
  (and
   (tamep-functionp scalarp)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (q6783821-member-p scalarp zero)
   (q6783821-member-p scalarp one)
   (not (equal zero one))
   (q6783821-universal-p
    (q6783821-field-laws-function
     scalarp zero one add multiply negate inverse)
    '(x y z))))

;; A polynomial ring presented by unique canonical coefficient lists.

(defun q6783821-polynomial-algebra-laws-function
    (scalarp scalar-zero scalar-one scalar-add scalar-multiply
     polyp poly-zero poly-one poly-add poly-multiply poly-negate
     constant indeterminate coordinates realize)
  (let* ((p-plus-q
          (q6783821-static-apply-term poly-add '(p q)))
         (q-plus-r
          (q6783821-static-apply-term poly-add '(q r)))
         (p-times-q
          (q6783821-static-apply-term poly-multiply '(p q)))
         (q-times-r
          (q6783821-static-apply-term poly-multiply '(q r)))
         (neg-p
          (q6783821-static-apply-term poly-negate '(p)))
         (const-s
          (q6783821-static-apply-term constant '(scalar)))
         (const-t
          (q6783821-static-apply-term constant '(scalar2)))
         (scalar-sum
          (q6783821-static-apply-term scalar-add '(scalar scalar2)))
         (scalar-product
          (q6783821-static-apply-term
           scalar-multiply '(scalar scalar2)))
         (coordinates-p
          (q6783821-static-apply-term coordinates '(p)))
         (realized
          (q6783821-static-apply-term realize '(coefficients)))
         (realized-tail
          (q6783821-static-apply-term
           realize (list (list 'cdr 'coefficients))))
         (constant-head
          (q6783821-static-apply-term
           constant (list (list 'car 'coefficients))))
         (horner
          (q6783821-static-apply-term
           poly-add
           (list
            constant-head
            (q6783821-static-apply-term
             poly-multiply
             (list (q6783821-quoted indeterminate)
                   realized-tail)))))
         (scalar-domain
          (q6783821-and-terms
           (list
            (q6783821-static-apply-term scalarp '(scalar))
            (q6783821-static-apply-term scalarp '(scalar2)))))
         (poly-domain
          (q6783821-and-terms
           (list
            (q6783821-polynomial-term polyp 'p)
            (q6783821-polynomial-term polyp 'q)
            (q6783821-polynomial-term polyp 'r))))
         (canonical
          (q6783821-canonical-coefficients-term
           'coefficients scalarp scalar-zero)))
    (list
     'lambda '(scalar scalar2 p q r coefficients)
     (q6783821-and-terms
      (list
       (q6783821-polynomial-term
        polyp (q6783821-quoted poly-zero))
       (q6783821-polynomial-term
        polyp (q6783821-quoted poly-one))
       (q6783821-polynomial-term
        polyp (q6783821-quoted indeterminate))
       (q6783821-implies-term
        poly-domain
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp p-plus-q)
          (q6783821-polynomial-term polyp p-times-q)
          (q6783821-polynomial-term polyp neg-p)
          (list 'equal
                (q6783821-static-apply-term
                 poly-add (list p-plus-q 'r))
                (q6783821-static-apply-term
                 poly-add (list 'p q-plus-r)))
          (list 'equal p-plus-q
                (q6783821-static-apply-term poly-add '(q p)))
          (list 'equal
                (q6783821-static-apply-term
                 poly-add
                 (list 'p (q6783821-quoted poly-zero)))
                'p)
          (list 'equal
                (q6783821-static-apply-term poly-add (list 'p neg-p))
                (q6783821-quoted poly-zero))
          (list 'equal
                (q6783821-static-apply-term
                 poly-multiply (list p-times-q 'r))
                (q6783821-static-apply-term
                 poly-multiply (list 'p q-times-r)))
          (list 'equal p-times-q
                (q6783821-static-apply-term
                 poly-multiply '(q p)))
          (list 'equal
                (q6783821-static-apply-term
                 poly-multiply
                 (list 'p (q6783821-quoted poly-one)))
                'p)
          (list 'equal
                (q6783821-static-apply-term
                 poly-multiply (list 'p q-plus-r))
                (q6783821-static-apply-term
                 poly-add
                 (list
                  (q6783821-static-apply-term
                   poly-multiply '(p q))
                  (q6783821-static-apply-term
                   poly-multiply '(p r))))))))
       (q6783821-implies-term
        scalar-domain
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp const-s)
          (list 'equal
                (q6783821-static-apply-term constant (list scalar-sum))
                (q6783821-static-apply-term
                 poly-add (list const-s const-t)))
          (list 'equal
                (q6783821-static-apply-term
                 constant (list scalar-product))
                (q6783821-static-apply-term
                 poly-multiply (list const-s const-t)))
          (q6783821-implies-term
           (list 'equal const-s const-t)
           (list 'equal 'scalar 'scalar2)))))
       (list 'equal
             (q6783821-static-apply-term
              constant (list (q6783821-quoted scalar-zero)))
             (q6783821-quoted poly-zero))
       (list 'equal
             (q6783821-static-apply-term
              constant (list (q6783821-quoted scalar-one)))
             (q6783821-quoted poly-one))
       (q6783821-implies-term
        (q6783821-polynomial-term polyp 'p)
        (q6783821-and-terms
         (list
          (q6783821-canonical-coefficients-term
           coordinates-p scalarp scalar-zero)
          (list 'equal
                (q6783821-static-apply-term
                 realize (list coordinates-p))
                'p))))
       (q6783821-implies-term
        canonical
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp realized)
          (list 'equal
                (q6783821-static-apply-term
                 coordinates (list realized))
                'coefficients)
          (list 'if
                'coefficients
                (list 'equal realized horner)
                (list 'equal
                      realized
                      (q6783821-quoted poly-zero)))))))))))

(defun q6783821-polynomial-algebra-p
    (scalarp scalar-zero scalar-one scalar-add scalar-multiply
     polyp poly-zero poly-one poly-add poly-multiply poly-negate
     constant indeterminate coordinates realize)
  (and
   (tamep-functionp polyp)
   (tamep-functionp poly-add)
   (tamep-functionp poly-multiply)
   (tamep-functionp poly-negate)
   (tamep-functionp constant)
   (tamep-functionp coordinates)
   (tamep-functionp realize)
   (q6783821-universal-p
    (q6783821-polynomial-algebra-laws-function
     scalarp scalar-zero scalar-one scalar-add scalar-multiply
     polyp poly-zero poly-one poly-add poly-multiply poly-negate
     constant indeterminate coordinates realize)
    '(scalar scalar2 p q r coefficients))))

;; The formal derivative is the unique derivation sending X to 1 and every
;; scalar constant to 0.

(defun q6783821-derivative-laws-function
    (scalarp polyp poly-zero poly-one poly-add poly-multiply
     constant indeterminate derivative)
  (let* ((derivative-p
          (q6783821-static-apply-term derivative '(p)))
         (derivative-q
          (q6783821-static-apply-term derivative '(q)))
         (p-plus-q
          (q6783821-static-apply-term poly-add '(p q)))
         (p-times-q
          (q6783821-static-apply-term poly-multiply '(p q))))
    (list
     'lambda '(scalar p q)
     (q6783821-and-terms
      (list
       (q6783821-implies-term
        (q6783821-static-apply-term scalarp '(scalar))
        (list
         'equal
         (q6783821-static-apply-term
          derivative
          (list
           (q6783821-static-apply-term constant '(scalar))))
         (q6783821-quoted poly-zero)))
       (list
        'equal
        (q6783821-static-apply-term
         derivative (list (q6783821-quoted indeterminate)))
        (q6783821-quoted poly-one))
       (q6783821-implies-term
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'p)
          (q6783821-polynomial-term polyp 'q)))
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp derivative-p)
          (list
           'equal
           (q6783821-static-apply-term
            derivative (list p-plus-q))
           (q6783821-static-apply-term
            poly-add (list derivative-p derivative-q)))
          (list
           'equal
           (q6783821-static-apply-term
            derivative (list p-times-q))
           (q6783821-static-apply-term
            poly-add
            (list
             (q6783821-static-apply-term
              poly-multiply (list derivative-p 'q))
             (q6783821-static-apply-term
              poly-multiply (list 'p derivative-q)))))))))))))

(defun q6783821-derivative-p
    (scalarp polyp poly-zero poly-one poly-add poly-multiply
     constant indeterminate derivative)
  (and
   (tamep-functionp derivative)
   (q6783821-universal-p
    (q6783821-derivative-laws-function
     scalarp polyp poly-zero poly-one poly-add poly-multiply
     constant indeterminate derivative)
    '(scalar p q))))

;; Coprimality is exactly the existence of a Bezout identity.

(defun q6783821-coprime-laws-function
    (polyp poly-one poly-add poly-multiply
     coprime left-selector right-selector)
  (let* ((selected-left
          (q6783821-static-apply-term left-selector '(a b)))
         (selected-right
          (q6783821-static-apply-term right-selector '(a b)))
         (selected-bezout
          (list
           'equal
           (q6783821-static-apply-term
            poly-add
            (list
             (q6783821-static-apply-term
              poly-multiply (list selected-left 'a))
             (q6783821-static-apply-term
              poly-multiply (list selected-right 'b))))
           (q6783821-quoted poly-one)))
         (candidate-bezout
          (q6783821-and-terms
           (list
            (q6783821-polynomial-term polyp 'x)
            (q6783821-polynomial-term polyp 'y)
            (list
             'equal
             (q6783821-static-apply-term
              poly-add
              (list
               (q6783821-static-apply-term
                poly-multiply '(x a))
               (q6783821-static-apply-term
                poly-multiply '(y b))))
             (q6783821-quoted poly-one))))))
    (list
     'lambda '(a b x y)
     (q6783821-and-terms
      (list
       (q6783821-implies-term
        (q6783821-static-apply-term coprime '(a b))
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'a)
          (q6783821-polynomial-term polyp 'b)
          (q6783821-polynomial-term polyp selected-left)
          (q6783821-polynomial-term polyp selected-right)
          selected-bezout)))
       (q6783821-implies-term
        candidate-bezout
        (q6783821-static-apply-term coprime '(a b))))))))

(defun q6783821-coprime-package-p
    (polyp poly-one poly-add poly-multiply
     coprime left-selector right-selector)
  (and
   (tamep-functionp coprime)
   (tamep-functionp left-selector)
   (tamep-functionp right-selector)
   (q6783821-universal-p
    (q6783821-coprime-laws-function
     polyp poly-one poly-add poly-multiply
     coprime left-selector right-selector)
    '(a b x y))))

;; Divisibility is exactly multiplication by a polynomial quotient.

(defun q6783821-divisibility-laws-function
    (polyp poly-multiply divides quotient-selector)
  (let* ((selected
          (q6783821-static-apply-term quotient-selector '(divisor dividend)))
         (selected-valid
          (q6783821-and-terms
           (list
            (q6783821-polynomial-term polyp selected)
            (list
             'equal
             (q6783821-static-apply-term
              poly-multiply (list 'divisor selected))
             'dividend))))
         (candidate-valid
          (q6783821-and-terms
           (list
            (q6783821-polynomial-term polyp 'divisor)
            (q6783821-polynomial-term polyp 'dividend)
            (q6783821-polynomial-term polyp 'quotient)
            (list
             'equal
             (q6783821-static-apply-term
              poly-multiply '(divisor quotient))
             'dividend)))))
    (list
     'lambda '(divisor dividend quotient)
     (q6783821-and-terms
      (list
       (q6783821-implies-term
        (q6783821-static-apply-term divides '(divisor dividend))
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'divisor)
          (q6783821-polynomial-term polyp 'dividend)
          selected-valid)))
       (q6783821-implies-term
        candidate-valid
        (q6783821-static-apply-term
         divides '(divisor dividend))))))))

(defun q6783821-divisibility-package-p
    (polyp poly-multiply divides quotient-selector)
  (and
   (tamep-functionp divides)
   (tamep-functionp quotient-selector)
   (q6783821-universal-p
    (q6783821-divisibility-laws-function
     polyp poly-multiply divides quotient-selector)
    '(divisor dividend quotient))))

;; Irreducibility is characterized by its factorization property, with a
;; selected nontrivial factorization for every reducible nonunit.

(defun q6783821-irreducibility-laws-function
    (polyp poly-zero poly-multiply coordinates irreducible
     left-factor-selector right-factor-selector)
  (let* ((unit-p
          (q6783821-unit-term polyp coordinates 'p))
         (unit-left
          (q6783821-unit-term polyp coordinates 'left))
         (unit-right
          (q6783821-unit-term polyp coordinates 'right))
         (factorization
          (q6783821-and-terms
           (list
            (q6783821-polynomial-term polyp 'left)
            (q6783821-polynomial-term polyp 'right)
            (list
             'equal
             (q6783821-static-apply-term
              poly-multiply '(left right))
             'p))))
         (selected-left
          (q6783821-static-apply-term left-factor-selector '(p)))
         (selected-right
          (q6783821-static-apply-term right-factor-selector '(p)))
         (selected-factorization
          (q6783821-and-terms
           (list
            (q6783821-polynomial-term polyp selected-left)
            (q6783821-polynomial-term polyp selected-right)
            (q6783821-not-term
             (q6783821-unit-term
              polyp coordinates selected-left))
            (q6783821-not-term
             (q6783821-unit-term
              polyp coordinates selected-right))
            (list
             'equal
             (q6783821-static-apply-term
              poly-multiply (list selected-left selected-right))
             'p)))))
    (list
     'lambda '(p left right)
     (q6783821-and-terms
      (list
       (q6783821-implies-term
        (q6783821-static-apply-term irreducible '(p))
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'p)
          (q6783821-not-term
           (list 'equal 'p (q6783821-quoted poly-zero)))
          (q6783821-not-term unit-p)
          (q6783821-implies-term
           factorization
           (q6783821-or-terms
            (list unit-left unit-right))))))
       (q6783821-implies-term
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'p)
          (q6783821-not-term
           (list 'equal 'p (q6783821-quoted poly-zero)))
          (q6783821-not-term unit-p)
          (q6783821-not-term
           (q6783821-static-apply-term irreducible '(p)))))
        selected-factorization))))))

(defun q6783821-irreducibility-package-p
    (polyp poly-zero poly-multiply coordinates irreducible
     left-factor-selector right-factor-selector)
  (and
   (tamep-functionp irreducible)
   (tamep-functionp left-factor-selector)
   (tamep-functionp right-factor-selector)
   (q6783821-universal-p
    (q6783821-irreducibility-laws-function
     polyp poly-zero poly-multiply coordinates irreducible
     left-factor-selector right-factor-selector)
    '(p left right))))

;; Squarefreeness excludes squared irreducible divisors, and a selected
;; repeated factor witnesses every failure.

(defun q6783821-squarefree-laws-function
    (polyp poly-zero poly-multiply divides irreducible squarefree
     repeated-factor-selector)
  (let* ((factor-square
          (q6783821-static-apply-term
           poly-multiply '(factor factor)))
         (selected
          (q6783821-static-apply-term repeated-factor-selector '(p)))
         (selected-square
          (q6783821-static-apply-term
           poly-multiply (list selected selected))))
    (list
     'lambda '(p factor)
     (q6783821-and-terms
      (list
       (q6783821-implies-term
        (q6783821-static-apply-term squarefree '(p))
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'p)
          (q6783821-not-term
           (list 'equal 'p (q6783821-quoted poly-zero)))
          (q6783821-implies-term
           (q6783821-static-apply-term irreducible '(factor))
           (q6783821-not-term
            (q6783821-static-apply-term
             divides (list factor-square 'p)))))))
       (q6783821-implies-term
        (q6783821-and-terms
         (list
          (q6783821-polynomial-term polyp 'p)
          (q6783821-not-term
           (list 'equal 'p (q6783821-quoted poly-zero)))
          (q6783821-not-term
           (q6783821-static-apply-term squarefree '(p)))))
        (q6783821-and-terms
         (list
          (q6783821-static-apply-term
           irreducible (list selected))
          (q6783821-static-apply-term
           divides (list selected-square 'p))))))))))

(defun q6783821-squarefree-package-p
    (polyp poly-zero poly-multiply divides irreducible squarefree
     repeated-factor-selector)
  (and
   (tamep-functionp squarefree)
   (tamep-functionp repeated-factor-selector)
   (q6783821-universal-p
    (q6783821-squarefree-laws-function
     polyp poly-zero poly-multiply divides irreducible squarefree
     repeated-factor-selector)
    '(p factor))))

;; For every nonzero polynomial, RADICAL is squarefree and has exactly the
;; same irreducible divisors.  This characterizes it up to a nonzero scalar,
;; which preserves the natDegree used by the theorem.

(defun q6783821-radical-laws-function
    (polyp poly-zero divides irreducible squarefree radical)
  (let ((radical-p
         (q6783821-static-apply-term radical '(p))))
    (list
     'lambda '(p factor)
     (q6783821-implies-term
      (q6783821-and-terms
       (list
        (q6783821-polynomial-term polyp 'p)
        (q6783821-not-term
         (list 'equal 'p (q6783821-quoted poly-zero)))))
      (q6783821-and-terms
       (list
        (q6783821-polynomial-term polyp radical-p)
        (q6783821-not-term
         (list 'equal radical-p (q6783821-quoted poly-zero)))
        (q6783821-static-apply-term squarefree (list radical-p))
        (q6783821-implies-term
         (q6783821-static-apply-term irreducible '(factor))
         (q6783821-iff-term
          (q6783821-static-apply-term
           divides (list 'factor radical-p))
          (q6783821-static-apply-term
           divides '(factor p))))))))))

(defun q6783821-radical-package-p
    (polyp poly-zero divides irreducible squarefree radical)
  (and
   (tamep-functionp radical)
   (q6783821-universal-p
    (q6783821-radical-laws-function
     polyp poly-zero divides irreducible squarefree radical)
    '(p factor))))

(defun q6783821-polynomial-nat-degree
    (coordinates polynomial)
  (let ((coefficients
         (q6783821-unary-value coordinates polynomial)))
    (if (endp coefficients)
        0
      (- (len coefficients) 1))))

(defun thousand-theorems-q6783821-mason-stothers-theorem-statement
    (scalarp scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse
     polyp poly-zero poly-one poly-add poly-multiply poly-negate
     constant indeterminate coordinates realize derivative
     coprime bezout-left bezout-right
     divides quotient-selector
     irreducible left-factor-selector right-factor-selector
     squarefree repeated-factor-selector radical
     a b c)
  (let* ((ab (q6783821-binary-value poly-multiply a b))
         (abc (q6783821-binary-value poly-multiply ab c))
         (sum
          (q6783821-binary-value
           poly-add
           (q6783821-binary-value poly-add a b)
           c))
         (radical-abc
          (q6783821-unary-value radical abc))
         (radical-degree
          (q6783821-polynomial-nat-degree
           coordinates radical-abc)))
    (implies
     (and
      (q6783821-field-p
       scalarp scalar-zero scalar-one scalar-add scalar-multiply
       scalar-negate scalar-inverse)
      (q6783821-polynomial-algebra-p
       scalarp scalar-zero scalar-one scalar-add scalar-multiply
       polyp poly-zero poly-one poly-add poly-multiply poly-negate
       constant indeterminate coordinates realize)
      (q6783821-derivative-p
       scalarp polyp poly-zero poly-one poly-add poly-multiply
       constant indeterminate derivative)
      (q6783821-coprime-package-p
       polyp poly-one poly-add poly-multiply
       coprime bezout-left bezout-right)
      (q6783821-divisibility-package-p
       polyp poly-multiply divides quotient-selector)
      (q6783821-irreducibility-package-p
       polyp poly-zero poly-multiply coordinates irreducible
       left-factor-selector right-factor-selector)
      (q6783821-squarefree-package-p
       polyp poly-zero poly-multiply divides irreducible squarefree
       repeated-factor-selector)
      (q6783821-radical-package-p
       polyp poly-zero divides irreducible squarefree radical)
      (q6783821-member-p polyp a)
      (q6783821-member-p polyp b)
      (q6783821-member-p polyp c)
      (not (equal a poly-zero))
      (not (equal b poly-zero))
      (not (equal c poly-zero))
      (q6783821-binary-value coprime a b)
      (equal sum poly-zero))
     (or
      (and
       (<=
        (+ (q6783821-polynomial-nat-degree coordinates a) 1)
        radical-degree)
       (<=
        (+ (q6783821-polynomial-nat-degree coordinates b) 1)
        radical-degree)
       (<=
        (+ (q6783821-polynomial-nat-degree coordinates c) 1)
        radical-degree))
      (and
       (equal
        (q6783821-unary-value derivative a)
        poly-zero)
       (equal
        (q6783821-unary-value derivative b)
        poly-zero)
       (equal
        (q6783821-unary-value derivative c)
        poly-zero))))))

;; Admission-time audit: every lambda reified for FN-EQUAL contains only ACL2
;; primitives, loop scions, and APPLY$ calls on quoted tame functions.

(defun q6783821-all-reified-functions-tame-p ()
  (let ((unary '(lambda (x) (quote t)))
        (binary '(lambda (x y) x)))
    (and
     (tamep-functionp
      (q6783821-true-function '(x)))
     (tamep-functionp
      (q6783821-field-laws-function
       unary 0 1 binary binary unary unary))
     (tamep-functionp
      (q6783821-polynomial-algebra-laws-function
       unary 0 1 binary binary
       unary 0 1 binary binary unary
       unary 'x unary unary))
     (tamep-functionp
      (q6783821-derivative-laws-function
       unary unary 0 1 binary binary unary 'x unary))
     (tamep-functionp
      (q6783821-coprime-laws-function
       unary 1 binary binary binary binary binary))
     (tamep-functionp
      (q6783821-divisibility-laws-function
       unary binary binary binary))
     (tamep-functionp
      (q6783821-irreducibility-laws-function
       unary 0 binary unary unary unary unary))
     (tamep-functionp
      (q6783821-squarefree-laws-function
       unary 0 binary binary unary unary unary))
     (tamep-functionp
      (q6783821-radical-laws-function
       unary 0 binary unary unary unary)))))

(value-triple
 (if (q6783821-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q6783821-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
