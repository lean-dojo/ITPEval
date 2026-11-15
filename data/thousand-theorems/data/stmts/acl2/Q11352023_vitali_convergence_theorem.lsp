;; Statement-only formalization of thousand-theorems corpus artifact Q11352023,
;; "Vitali convergence theorem": for a finite exponent p at least one on an
;; arbitrary measure space, convergence in measure together with uniform
;; integrability and uniform tightness is equivalent to convergence in Lp.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, functions, sigma algebras, and operations are tame APPLY$
;; function objects. FN-EQUAL supplies unbounded universal quantification, and
;; inequality with a constant-false function supplies internal existential
;; witnesses. The scalar structure is a Dedekind-complete ordered field, hence
;; a presentation of the real field. The measure on an arbitrary subset is
;; characterized as the infimum of the measures of its measurable supersets,
;; so null exceptional sets use outer-measure semantics. The lower integral is
;; the supremum of integrals of measurable finite-range simple minorants.
;; Strong measurability is approximation by measurable finite-range functions,
;; real powers are characterized through the exponential series and logarithm,
;; and all Lp, convergence, integrability, and tightness predicates below are
;; expanded from those objects. Since the source assumes p is finite and at
;; least one, p is represented by its unique real value in [1,infinity).

(defun q11352023-quoted (object)
  (list 'quote object))

(defun q11352023-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q11352023-term-list (cdr terms)))
    (q11352023-quoted nil)))

(defun q11352023-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (q11352023-term-list arguments)))

(defun q11352023-static-apply-term (function arguments)
  (q11352023-apply-term
   (q11352023-quoted function)
   arguments))

(defun q11352023-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q11352023-and-terms (cdr terms))
            (q11352023-quoted nil))
    (q11352023-quoted t)))

(defun q11352023-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q11352023-quoted t)
            (q11352023-or-terms (cdr terms)))
    (q11352023-quoted nil)))

(defun q11352023-not-term (term)
  (list 'if term
        (q11352023-quoted nil)
        (q11352023-quoted t)))

(defun q11352023-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q11352023-quoted t)))

(defun q11352023-iff-term (left right)
  (list 'if left
        (list 'if right
              (q11352023-quoted t)
              (q11352023-quoted nil))
        (list 'if right
              (q11352023-quoted nil)
              (q11352023-quoted t))))

(defun q11352023-true-function (formals)
  (list 'lambda formals (q11352023-quoted t)))

(defun q11352023-false-function (formals)
  (list 'lambda formals (q11352023-quoted nil)))

(defun q11352023-universal-p (function formals)
  (let ((always-true (q11352023-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun q11352023-exists-p (function formals)
  (let ((always-false (q11352023-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun q11352023-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q11352023-unary-value (function object)
  (apply$ function (list object)))

(defun q11352023-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun q11352023-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (q11352023-static-apply-term carrier '(x))
      (q11352023-static-apply-term left '(x))))
    (q11352023-static-apply-term right '(x)))))

(defun q11352023-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q11352023-universal-p
    (q11352023-set-subset-function carrier left right)
    '(x))))

(defun q11352023-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q11352023-set-subset-p carrier set carrier)))

(defun q11352023-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-static-apply-term carrier '(x))
    (q11352023-iff-term
     (q11352023-static-apply-term left '(x))
     (q11352023-static-apply-term right '(x))))))

(defun q11352023-set-equiv-p (carrier left right)
  (and
   (q11352023-valid-set-p carrier left)
   (q11352023-valid-set-p carrier right)
   (q11352023-universal-p
    (q11352023-set-equiv-function carrier left right)
    '(x))))

(defun q11352023-empty-set ()
  (list 'lambda '(x) (q11352023-quoted nil)))

(defun q11352023-full-set (carrier)
  (list 'lambda '(x)
        (q11352023-static-apply-term carrier '(x))))

(defun q11352023-complement-set (carrier set)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term carrier '(x))
     (q11352023-not-term
      (q11352023-static-apply-term set '(x)))))))

(defun q11352023-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-static-apply-term domain-carrier '(x))
    (q11352023-static-apply-term
     codomain-carrier
     (list (q11352023-static-apply-term function '(x)))))))

(defun q11352023-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (q11352023-universal-p
    (q11352023-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q11352023-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (q11352023-static-apply-term add '(x y)))
         (yz-add (q11352023-static-apply-term add '(y z)))
         (xy-mul (q11352023-static-apply-term multiply '(x y)))
         (yz-mul (q11352023-static-apply-term multiply '(y z)))
         (neg-x (q11352023-static-apply-term negate '(x)))
         (inv-x (q11352023-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (q11352023-implies-term
      (q11352023-and-terms
       (list
        (q11352023-static-apply-term carrier '(x))
        (q11352023-static-apply-term carrier '(y))
        (q11352023-static-apply-term carrier '(z))))
      (q11352023-and-terms
       (list
        (q11352023-static-apply-term carrier (list xy-add))
        (q11352023-static-apply-term carrier (list xy-mul))
        (q11352023-static-apply-term carrier (list neg-x))
        (q11352023-static-apply-term carrier (list inv-x))
        (list 'equal
              (q11352023-static-apply-term add (list xy-add 'z))
              (q11352023-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (q11352023-static-apply-term add '(y x)))
        (list 'equal
              (q11352023-static-apply-term
               add (list 'x (q11352023-quoted zero)))
              'x)
        (list 'equal
              (q11352023-static-apply-term add (list 'x neg-x))
              (q11352023-quoted zero))
        (list 'equal
              (q11352023-static-apply-term multiply (list xy-mul 'z))
              (q11352023-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (q11352023-static-apply-term multiply '(y x)))
        (list 'equal
              (q11352023-static-apply-term
               multiply (list 'x (q11352023-quoted one)))
              'x)
        (q11352023-implies-term
         (list 'equal 'x (q11352023-quoted zero))
         (list 'equal inv-x (q11352023-quoted zero)))
        (q11352023-implies-term
         (q11352023-not-term
          (list 'equal 'x (q11352023-quoted zero)))
         (list 'equal
               (q11352023-static-apply-term
                multiply (list 'x inv-x))
               (q11352023-quoted one)))
        (list 'equal
              (q11352023-static-apply-term multiply (list 'x yz-add))
              (q11352023-static-apply-term
               add
               (list
                (q11352023-static-apply-term multiply '(x y))
                (q11352023-static-apply-term multiply '(x z)))))))))))

(defun q11352023-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (q11352023-static-apply-term less '(x y)))
        (yx (q11352023-static-apply-term less '(y x)))
        (yz (q11352023-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (q11352023-implies-term
      (q11352023-and-terms
       (list
        (q11352023-static-apply-term carrier '(x))
        (q11352023-static-apply-term carrier '(y))
        (q11352023-static-apply-term carrier '(z))))
      (q11352023-and-terms
       (list
        (q11352023-not-term
         (q11352023-static-apply-term less '(x x)))
        (q11352023-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q11352023-implies-term
         (q11352023-and-terms (list xy yz))
         (q11352023-static-apply-term less '(x z)))
        (q11352023-implies-term
         xy
         (q11352023-static-apply-term
          less
          (list
           (q11352023-static-apply-term add '(x z))
           (q11352023-static-apply-term add '(y z)))))
        (q11352023-implies-term
         (q11352023-and-terms
          (list
           (q11352023-static-apply-term
            less (list (q11352023-quoted zero) 'x))
           (q11352023-static-apply-term
            less (list (q11352023-quoted zero) 'y))))
         (q11352023-static-apply-term
          less
          (list
           (q11352023-quoted zero)
           (q11352023-static-apply-term multiply '(x y)))))))))))

(defun q11352023-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (q11352023-static-apply-term carrier '(x))
      (q11352023-static-apply-term set '(x))))
    (q11352023-not-term
     (q11352023-static-apply-term
      less (list (q11352023-quoted upper) 'x))))))

(defun q11352023-upper-bound-p
    (carrier less set upper)
  (and
   (q11352023-member-p carrier upper)
   (q11352023-valid-set-p carrier set)
   (q11352023-universal-p
    (q11352023-upper-bound-function carrier less set upper)
    '(x))))

(defun q11352023-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term carrier '(x))
     (q11352023-static-apply-term set '(x))))))

(defun q11352023-set-nonempty-p (carrier set)
  (and
   (q11352023-valid-set-p carrier set)
   (q11352023-exists-p
    (q11352023-set-nonempty-function carrier set)
    '(x))))

(defun q11352023-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'q11352023-upper-bound-p
         (q11352023-quoted carrier)
         (q11352023-quoted less)
         (q11352023-quoted set)
         'upper)))

(defun q11352023-bounded-above-p (carrier less set)
  (q11352023-exists-p
   (q11352023-bounded-above-function carrier less set)
   '(upper)))

(defun q11352023-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (q11352023-implies-term
    (list 'q11352023-upper-bound-p
          (q11352023-quoted carrier)
          (q11352023-quoted less)
          (q11352023-quoted set)
          'upper)
    (q11352023-not-term
     (q11352023-static-apply-term
      less (list 'upper (q11352023-quoted supremum)))))))

(defun q11352023-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q11352023-upper-bound-p carrier less set supremum)
   (q11352023-universal-p
    (q11352023-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q11352023-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-valid-set-p
            (q11352023-quoted carrier) 'set)
      (list 'q11352023-set-nonempty-p
            (q11352023-quoted carrier) 'set)
      (list 'q11352023-bounded-above-p
            (q11352023-quoted carrier)
            (q11352023-quoted less)
            'set)))
    (list 'q11352023-least-upper-bound-p
          (q11352023-quoted carrier)
          (q11352023-quoted less)
          'set
          (q11352023-static-apply-term
           supremum-operation '(set))))))

(defun q11352023-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q11352023-member-p carrier zero)
   (q11352023-member-p carrier one)
   (not (equal zero one))
   (q11352023-universal-p
    (q11352023-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q11352023-universal-p
    (q11352023-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q11352023-universal-p
    (q11352023-completeness-function
     carrier less supremum)
    '(set))
   (q11352023-binary-value less zero one)))

(defun q11352023-scalar-absolute-value
    (less zero negate value)
  (if (q11352023-binary-value less value zero)
      (q11352023-unary-value negate value)
    value))
;; Sigma algebras.

(defun q11352023-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (q11352023-implies-term
    (list 'q11352023-set-equiv-p
          (q11352023-quoted carrier)
          'left 'right)
    (q11352023-iff-term
     (q11352023-static-apply-term family '(left))
     (q11352023-static-apply-term family '(right))))))

(defun q11352023-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (q11352023-implies-term
    (q11352023-static-apply-term family '(set))
    (list 'q11352023-valid-set-p
          (q11352023-quoted carrier)
          'set))))

(defun q11352023-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q11352023-universal-p
    (q11352023-family-extensional-function carrier family)
    '(left right))
   (q11352023-universal-p
    (q11352023-family-members-valid-function carrier family)
    '(set))))

(defun q11352023-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (q11352023-and-terms
    (list
     (list 'natp 'n)
     (q11352023-apply-term
      (q11352023-static-apply-term sequence '(n))
      (list (q11352023-quoted x)))))))

(defun q11352023-sequence-union-member-p (sequence x)
  (q11352023-exists-p
   (q11352023-sequence-union-member-function sequence x)
   '(n)))

(defun q11352023-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term carrier '(x))
     (list 'q11352023-sequence-union-member-p
           (q11352023-quoted sequence)
           'x)))))

(defun q11352023-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (list 'natp 'n)
    (list 'q11352023-valid-set-p
          (q11352023-quoted carrier)
          (q11352023-static-apply-term sequence '(n))))))

(defun q11352023-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (q11352023-universal-p
    (q11352023-sequence-of-sets-function carrier sequence)
    '(n))))

(defun q11352023-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (list 'natp 'n)
    (q11352023-static-apply-term
     family
     (list (q11352023-static-apply-term sequence '(n)))))))

(defun q11352023-sequence-members-family-p
    (carrier family sequence)
  (and
   (q11352023-sequence-of-sets-p carrier sequence)
   (q11352023-universal-p
    (q11352023-sequence-members-family-function family sequence)
    '(n))))

(defun q11352023-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (q11352023-implies-term
    (q11352023-static-apply-term family '(set))
    (q11352023-static-apply-term
     family
     (list
      (list 'q11352023-complement-set
            (q11352023-quoted carrier)
            'set))))))

(defun q11352023-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (q11352023-implies-term
    (list 'q11352023-sequence-members-family-p
          (q11352023-quoted carrier)
          (q11352023-quoted family)
          'sequence)
    (q11352023-static-apply-term
     family
     (list
      (list 'q11352023-sequence-union-set
            (q11352023-quoted carrier)
            'sequence))))))

(defun q11352023-sigma-algebra-p (carrier family)
  (and
   (q11352023-family-of-sets-p carrier family)
   (q11352023-member-p family (q11352023-empty-set))
   (q11352023-universal-p
    (q11352023-sigma-complement-function carrier family)
    '(set))
   (q11352023-universal-p
    (q11352023-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun q11352023-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :q11352023-top)
   (and
    (consp value)
    (equal (car value) :q11352023-finite)
    (q11352023-member-p scalar-carrier (cdr value))
    (not
     (q11352023-binary-value scalar-less (cdr value) scalar-zero)))))

(defun q11352023-ennreal-finite (value)
  (cons :q11352023-finite value))

(defun q11352023-ennreal-zero (scalar-zero)
  (q11352023-ennreal-finite scalar-zero))

(defun q11352023-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :q11352023-top) nil)
   ((equal right :q11352023-top) t)
   (t
    (q11352023-binary-value scalar-less (cdr left) (cdr right)))))

(defun q11352023-ennreal-less-equal-p (left right scalar-less)
  (not (q11352023-ennreal-less-p right left scalar-less)))

(defun q11352023-ennreal-add (left right scalar-add)
  (if (or (equal left :q11352023-top)
          (equal right :q11352023-top))
      :q11352023-top
    (q11352023-ennreal-finite
     (q11352023-binary-value scalar-add (cdr left) (cdr right)))))

(defun q11352023-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (q11352023-ennreal-zero scalar-zero))
        (equal right (q11352023-ennreal-zero scalar-zero)))
    (q11352023-ennreal-zero scalar-zero))
   ((or (equal left :q11352023-top)
        (equal right :q11352023-top))
    :q11352023-top)
   (t
    (q11352023-ennreal-finite
     (q11352023-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun q11352023-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q11352023-ennreal-zero scalar-zero)
    (q11352023-ennreal-add
     (q11352023-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (q11352023-unary-value sequence (- count 1))
     scalar-add)))

(defun q11352023-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (q11352023-implies-term
    (list 'natp 'count)
    (list 'q11352023-ennreal-less-equal-p
          (list 'q11352023-finite-ennreal-sum
                (q11352023-quoted sequence)
                'count
                (q11352023-quoted scalar-zero)
                (q11352023-quoted scalar-add))
          (q11352023-quoted total)
          (q11352023-quoted scalar-less)))))

(defun q11352023-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (q11352023-universal-p
   (q11352023-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun q11352023-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-ennreal-p
            'bound
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted scalar-zero)
            (q11352023-quoted scalar-less))
      (list 'q11352023-sum-upper-bound-p
            (q11352023-quoted sequence)
            'bound
            (q11352023-quoted scalar-zero)
            (q11352023-quoted scalar-add)
            (q11352023-quoted scalar-less))))
    (list 'q11352023-ennreal-less-equal-p
          (q11352023-quoted total)
          'bound
          (q11352023-quoted scalar-less)))))

(defun q11352023-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (q11352023-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (q11352023-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (q11352023-universal-p
    (q11352023-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun q11352023-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (q11352023-implies-term
    (list 'q11352023-set-equiv-p
          (q11352023-quoted carrier)
          'left 'right)
    (list 'equal
          (q11352023-static-apply-term measure '(left))
          (q11352023-static-apply-term measure '(right))))))

(defun q11352023-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (q11352023-implies-term
    (list 'q11352023-valid-set-p
          (q11352023-quoted carrier)
          'set)
    (list 'q11352023-ennreal-p
          (q11352023-static-apply-term measure '(set))
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)))))

(defun q11352023-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (q11352023-static-apply-term
    measure
    (list (q11352023-static-apply-term sequence '(n))))))

(defun q11352023-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-static-apply-term carrier '(x))
    (q11352023-not-term
     (q11352023-and-terms
      (list
       (q11352023-static-apply-term left '(x))
       (q11352023-static-apply-term right '(x))))))))

(defun q11352023-disjoint-sets-p (carrier left right)
  (q11352023-universal-p
   (q11352023-disjoint-sets-function carrier left right)
   '(x)))

(defun q11352023-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (q11352023-not-term (list 'equal 'm 'n))))
    (list 'q11352023-disjoint-sets-p
          (q11352023-quoted carrier)
          (q11352023-static-apply-term sequence '(m))
          (q11352023-static-apply-term sequence '(n))))))

(defun q11352023-pairwise-disjoint-p (carrier sequence)
  (q11352023-universal-p
   (q11352023-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun q11352023-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-sequence-members-family-p
            (q11352023-quoted carrier)
            (q11352023-quoted measurable)
            'sequence)
      (list 'q11352023-pairwise-disjoint-p
            (q11352023-quoted carrier)
            'sequence)))
    (list 'q11352023-countable-sum-p
          (list 'q11352023-measure-sequence-values
                (q11352023-quoted measure)
                'sequence)
          (q11352023-static-apply-term
           measure
           (list
            (list 'q11352023-sequence-union-set
                  (q11352023-quoted carrier)
                  'sequence)))
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-add)
          (q11352023-quoted scalar-less)))))

(defun q11352023-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (q11352023-static-apply-term measurable '(superset))
      (list 'q11352023-set-subset-p
            (q11352023-quoted carrier)
            (q11352023-quoted set)
            'superset)))
    (list 'q11352023-ennreal-less-equal-p
          (q11352023-quoted lower)
          (q11352023-static-apply-term measure '(superset))
          (q11352023-quoted scalar-less)))))

(defun q11352023-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (q11352023-universal-p
   (q11352023-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun q11352023-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-ennreal-p
            'lower
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted scalar-zero)
            (q11352023-quoted scalar-less))
      (list 'q11352023-measurable-superset-lower-bound-p
            (q11352023-quoted carrier)
            (q11352023-quoted measurable)
            (q11352023-quoted measure)
            (q11352023-quoted set)
            'lower
            (q11352023-quoted scalar-less))))
    (list 'q11352023-ennreal-less-equal-p
          'lower
          (q11352023-static-apply-term
           measure (list (q11352023-quoted set)))
          (q11352023-quoted scalar-less)))))

(defun q11352023-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (q11352023-valid-set-p carrier set)
   (q11352023-measurable-superset-lower-bound-p
    carrier measurable measure set
    (q11352023-unary-value measure set)
    scalar-less)
   (q11352023-universal-p
    (q11352023-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun q11352023-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (q11352023-implies-term
    (list 'q11352023-valid-set-p
          (q11352023-quoted carrier)
          'set)
    (list 'q11352023-outer-value-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)
          (q11352023-quoted carrier)
          (q11352023-quoted measurable)
          (q11352023-quoted measure)
          'set))))

(defun q11352023-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (q11352023-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (q11352023-universal-p
    (q11352023-measure-extensional-function carrier measure)
    '(left right))
   (q11352023-universal-p
    (q11352023-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (equal
    (q11352023-unary-value measure (q11352023-empty-set))
    (q11352023-ennreal-zero scalar-zero))
   (q11352023-universal-p
    (q11352023-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (q11352023-universal-p
    (q11352023-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; Function sequences and order-topological convergence.

(defun q11352023-ennreal-carrier
    (scalar-carrier scalar-zero scalar-less)
  (list
   'lambda '(value)
   (list 'q11352023-ennreal-p
         'value
         (q11352023-quoted scalar-carrier)
         (q11352023-quoted scalar-zero)
         (q11352023-quoted scalar-less))))

(defun q11352023-ennreal-less-function (scalar-less)
  (list
   'lambda '(left right)
   (list 'q11352023-ennreal-less-p
         'left 'right
         (q11352023-quoted scalar-less))))

(defun q11352023-less-equal-term (less left right)
  (q11352023-not-term
   (q11352023-static-apply-term less (list right left))))

(defun q11352023-sequence-term-function (sequence n)
  (list
   'lambda '(x)
   (q11352023-apply-term
    (q11352023-static-apply-term
     sequence (list (q11352023-quoted n)))
    '(x))))

(defun q11352023-function-sequence-values-function
    (domain-carrier codomain-carrier sequence)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (list 'natp 'n)
    (list 'q11352023-function-p
          (q11352023-quoted domain-carrier)
          (q11352023-quoted codomain-carrier)
          (q11352023-static-apply-term sequence '(n))))))

(defun q11352023-function-sequence-p
    (domain-carrier codomain-carrier sequence)
  (and
   (tamep-functionp sequence)
   (q11352023-universal-p
    (q11352023-function-sequence-values-function
     domain-carrier codomain-carrier sequence)
    '(n))))

(defun q11352023-natural-values-function
    (carrier values)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (list 'natp 'n)
    (q11352023-static-apply-term
     carrier
     (list (q11352023-static-apply-term values '(n)))))))

(defun q11352023-natural-values-p (carrier values)
  (and
   (tamep-functionp values)
   (q11352023-universal-p
    (q11352023-natural-values-function carrier values)
    '(n))))

(defun q11352023-eventual-lower-function
    (values less lower start)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q11352023-quoted start) 'n)))
    (q11352023-static-apply-term
     less
     (list
      (q11352023-quoted lower)
      (q11352023-static-apply-term values '(n)))))))

(defun q11352023-eventual-lower-p
    (values less lower start)
  (and
   (natp start)
   (q11352023-universal-p
    (q11352023-eventual-lower-function
     values less lower start)
    '(n))))

(defun q11352023-lower-start-function
    (values less lower)
  (list
   'lambda '(start)
   (list 'q11352023-eventual-lower-p
         (q11352023-quoted values)
         (q11352023-quoted less)
         (q11352023-quoted lower)
         'start)))

(defun q11352023-eventually-above-p
    (values less lower)
  (q11352023-exists-p
   (q11352023-lower-start-function values less lower)
   '(start)))

(defun q11352023-eventual-upper-function
    (values less upper start)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q11352023-quoted start) 'n)))
    (q11352023-static-apply-term
     less
     (list
      (q11352023-static-apply-term values '(n))
      (q11352023-quoted upper))))))

(defun q11352023-eventual-upper-p
    (values less upper start)
  (and
   (natp start)
   (q11352023-universal-p
    (q11352023-eventual-upper-function
     values less upper start)
    '(n))))

(defun q11352023-upper-start-function
    (values less upper)
  (list
   'lambda '(start)
   (list 'q11352023-eventual-upper-p
         (q11352023-quoted values)
         (q11352023-quoted less)
         (q11352023-quoted upper)
         'start)))

(defun q11352023-eventually-below-p
    (values less upper)
  (q11352023-exists-p
   (q11352023-upper-start-function values less upper)
   '(start)))

(defun q11352023-order-convergence-bound-function
    (carrier less values limit)
  (list
   'lambda '(bound)
   (q11352023-implies-term
    (q11352023-static-apply-term carrier '(bound))
    (q11352023-and-terms
     (list
      (q11352023-implies-term
       (q11352023-static-apply-term
        less (list 'bound (q11352023-quoted limit)))
       (list 'q11352023-eventually-above-p
             (q11352023-quoted values)
             (q11352023-quoted less)
             'bound))
      (q11352023-implies-term
       (q11352023-static-apply-term
        less (list (q11352023-quoted limit) 'bound))
       (list 'q11352023-eventually-below-p
             (q11352023-quoted values)
             (q11352023-quoted less)
             'bound)))))))

(defun q11352023-tendsto-order-p
    (carrier less values limit)
  (and
   (tamep-functionp carrier)
   (tamep-functionp less)
   (q11352023-natural-values-p carrier values)
   (q11352023-member-p carrier limit)
   (q11352023-universal-p
    (q11352023-order-convergence-bound-function
     carrier less values limit)
    '(bound))))

;; Pointwise monotonicity and almost-everywhere order convergence.

(defun q11352023-pointwise-values-function (sequence x)
  (list
   'lambda '(n)
   (q11352023-apply-term
    (q11352023-static-apply-term sequence '(n))
    (list (q11352023-quoted x)))))

(defun q11352023-pointwise-monotone-index-function
    (sequence less x)
  (let ((left
         (q11352023-apply-term
          (q11352023-static-apply-term sequence '(n))
          (list (q11352023-quoted x))))
        (right
         (q11352023-apply-term
          (q11352023-static-apply-term sequence '(m))
          (list (q11352023-quoted x)))))
    (list
     'lambda '(n m)
     (q11352023-implies-term
      (q11352023-and-terms
       (list
        (list 'natp 'n)
        (list 'natp 'm)
        (list '<= 'n 'm)))
      (q11352023-less-equal-term less left right)))))

(defun q11352023-pointwise-monotone-p
    (sequence less x)
  (q11352023-universal-p
   (q11352023-pointwise-monotone-index-function
    sequence less x)
   '(n m)))

(defun q11352023-pointwise-antitone-index-function
    (sequence less x)
  (let ((left
         (q11352023-apply-term
          (q11352023-static-apply-term sequence '(m))
          (list (q11352023-quoted x))))
        (right
         (q11352023-apply-term
          (q11352023-static-apply-term sequence '(n))
          (list (q11352023-quoted x)))))
    (list
     'lambda '(n m)
     (q11352023-implies-term
      (q11352023-and-terms
       (list
        (list 'natp 'n)
        (list 'natp 'm)
        (list '<= 'n 'm)))
      (q11352023-less-equal-term less left right)))))

(defun q11352023-pointwise-antitone-p
    (sequence less x)
  (q11352023-universal-p
   (q11352023-pointwise-antitone-index-function
    sequence less x)
   '(n m)))

(defun q11352023-monotone-failure-set
    (domain-carrier sequence less)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (q11352023-not-term
      (list 'q11352023-pointwise-monotone-p
            (q11352023-quoted sequence)
            (q11352023-quoted less)
            'x))))))

(defun q11352023-antitone-failure-set
    (domain-carrier sequence less)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (q11352023-not-term
      (list 'q11352023-pointwise-antitone-p
            (q11352023-quoted sequence)
            (q11352023-quoted less)
            'x))))))

(defun q11352023-null-set-p
    (scalar-zero domain-carrier measure set)
  (and
   (q11352023-valid-set-p domain-carrier set)
   (equal
    (q11352023-unary-value measure set)
    (q11352023-ennreal-zero scalar-zero))))

(defun q11352023-ae-monotone-p
    (scalar-zero domain-carrier measure sequence less)
  (q11352023-null-set-p
   scalar-zero domain-carrier measure
   (q11352023-monotone-failure-set
    domain-carrier sequence less)))

(defun q11352023-ae-antitone-p
    (scalar-zero domain-carrier measure sequence less)
  (q11352023-null-set-p
   scalar-zero domain-carrier measure
   (q11352023-antitone-failure-set
    domain-carrier sequence less)))

(defun q11352023-pointwise-tendsto-p
    (carrier less sequence limit x)
  (q11352023-tendsto-order-p
   carrier less
   (q11352023-pointwise-values-function sequence x)
   (q11352023-unary-value limit x)))

(defun q11352023-tendsto-failure-set
    (domain-carrier codomain-carrier less sequence limit)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (q11352023-not-term
      (list 'q11352023-pointwise-tendsto-p
            (q11352023-quoted codomain-carrier)
            (q11352023-quoted less)
            (q11352023-quoted sequence)
            (q11352023-quoted limit)
            'x))))))

(defun q11352023-ae-pointwise-tendsto-p
    (scalar-zero domain-carrier measure
     codomain-carrier less sequence limit)
  (and
   (q11352023-function-sequence-p
    domain-carrier codomain-carrier sequence)
   (q11352023-function-p
    domain-carrier codomain-carrier limit)
   (q11352023-null-set-p
    scalar-zero domain-carrier measure
    (q11352023-tendsto-failure-set
     domain-carrier codomain-carrier less sequence limit))))

;; Equality almost everywhere.

(defun q11352023-disagreement-set
    (domain-carrier left right)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (q11352023-not-term
      (list 'equal
            (q11352023-static-apply-term left '(x))
            (q11352023-static-apply-term right '(x))))))))

(defun q11352023-ae-equal-p
    (scalar-zero domain-carrier measure codomain-carrier left right)
  (and
   (q11352023-function-p domain-carrier codomain-carrier left)
   (q11352023-function-p domain-carrier codomain-carrier right)
   (q11352023-null-set-p
    scalar-zero domain-carrier measure
    (q11352023-disagreement-set domain-carrier left right))))

;; Standard measurability is characterized by measurable upper-ray preimages.

(defun q11352023-upper-ray-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (q11352023-static-apply-term
      less
      (list (q11352023-quoted threshold)
            (q11352023-static-apply-term function '(x))))))))

(defun q11352023-measurable-upper-rays-function
    (domain-carrier measurable codomain-carrier less function)
  (list
   'lambda '(threshold)
   (q11352023-implies-term
    (q11352023-static-apply-term codomain-carrier '(threshold))
    (q11352023-static-apply-term
     measurable
     (list
      (list 'q11352023-upper-ray-preimage-set
            (q11352023-quoted domain-carrier)
            (q11352023-quoted function)
            (q11352023-quoted less)
            'threshold))))))

(defun q11352023-measurable-function-p
    (domain-carrier measurable codomain-carrier less function)
  (and
   (q11352023-function-p domain-carrier codomain-carrier function)
   (q11352023-universal-p
    (q11352023-measurable-upper-rays-function
     domain-carrier measurable codomain-carrier less function)
    '(threshold))))

(defun q11352023-ae-measurable-witness-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (list
   'lambda '(representative)
   (q11352023-and-terms
    (list
     (list 'q11352023-measurable-function-p
           (q11352023-quoted domain-carrier)
           (q11352023-quoted measurable)
           (q11352023-quoted codomain-carrier)
           (q11352023-quoted less)
           'representative)
     (list 'q11352023-ae-equal-p
           (q11352023-quoted scalar-zero)
           (q11352023-quoted domain-carrier)
           (q11352023-quoted measure)
           (q11352023-quoted codomain-carrier)
           (q11352023-quoted function)
           'representative)))))

(defun q11352023-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (and
   (q11352023-function-p domain-carrier codomain-carrier function)
   (q11352023-exists-p
    (q11352023-ae-measurable-witness-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
    '(representative))))

;; The lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple functions below the integrand.

(defun q11352023-fiber-set (domain-carrier function value)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (list 'equal
           (q11352023-static-apply-term function '(x))
           (q11352023-quoted value))))))

(defun q11352023-values-in-carrier-p (carrier values)
  (if (consp values)
      (and
       (q11352023-member-p carrier (car values))
       (q11352023-values-in-carrier-p carrier (cdr values)))
    (equal values nil)))

(defun q11352023-value-attained-function
    (domain-carrier function value)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (list 'equal
           (q11352023-static-apply-term function '(x))
           (q11352023-quoted value))))))

(defun q11352023-value-attained-p
    (domain-carrier function value)
  (q11352023-exists-p
   (q11352023-value-attained-function
    domain-carrier function value)
   '(x)))

(defun q11352023-values-attained-p
    (domain-carrier function values)
  (if (consp values)
      (and
       (q11352023-value-attained-p
        domain-carrier function (car values))
       (q11352023-values-attained-p
        domain-carrier function (cdr values)))
    (equal values nil)))

(defun q11352023-range-in-values-function
    (domain-carrier function values)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-static-apply-term domain-carrier '(x))
    (list 'member-equal
          (q11352023-static-apply-term function '(x))
          (q11352023-quoted values)))))

(defun q11352023-simple-function-p
    (domain-carrier measurable codomain-carrier less function values)
  (and
   (q11352023-measurable-function-p
    domain-carrier measurable codomain-carrier less function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (q11352023-values-in-carrier-p codomain-carrier values)
   (q11352023-values-attained-p domain-carrier function values)
   (q11352023-universal-p
    (q11352023-range-in-values-function
     domain-carrier function values)
    '(x))))

(defun q11352023-finite-simple-integral
    (domain-carrier measure function values
     scalar-zero scalar-add scalar-multiply)
  (if (consp values)
      (q11352023-ennreal-add
       (q11352023-ennreal-multiply
        (car values)
        (q11352023-unary-value
         measure
         (q11352023-fiber-set
          domain-carrier function (car values)))
        scalar-zero scalar-multiply)
       (q11352023-finite-simple-integral
        domain-carrier measure function (cdr values)
        scalar-zero scalar-add scalar-multiply)
       scalar-add)
    (q11352023-ennreal-zero scalar-zero)))

(defun q11352023-simple-below-function
    (domain-carrier simple function scalar-less)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-static-apply-term domain-carrier '(x))
    (list 'q11352023-ennreal-less-equal-p
          (q11352023-static-apply-term simple '(x))
          (q11352023-static-apply-term function '(x))
          (q11352023-quoted scalar-less)))))

(defun q11352023-simple-below-p
    (domain-carrier simple function scalar-less)
  (q11352023-universal-p
   (q11352023-simple-below-function
    domain-carrier simple function scalar-less)
   '(x)))

(defun q11352023-lintegral-upper-bound-function
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (list
   'lambda '(simple values)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-simple-function-p
            (q11352023-quoted domain-carrier)
            (q11352023-quoted measurable)
            (q11352023-quoted ennreal-carrier)
            (q11352023-quoted ennreal-less)
            'simple 'values)
      (list 'q11352023-simple-below-p
            (q11352023-quoted domain-carrier)
            'simple
            (q11352023-quoted function)
            (q11352023-quoted scalar-less))))
    (list 'q11352023-ennreal-less-equal-p
          (list 'q11352023-finite-simple-integral
                (q11352023-quoted domain-carrier)
                (q11352023-quoted measure)
                'simple 'values
                (q11352023-quoted scalar-zero)
                (q11352023-quoted scalar-add)
                (q11352023-quoted scalar-multiply))
          (q11352023-quoted bound)
          (q11352023-quoted scalar-less)))))

(defun q11352023-lintegral-upper-bound-p
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (q11352023-universal-p
   (q11352023-lintegral-upper-bound-function
    domain-carrier measurable measure ennreal-carrier ennreal-less
    function bound scalar-zero scalar-add scalar-multiply scalar-less)
   '(simple values)))

(defun q11352023-lintegral-least-upper-bound-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     function value)
  (list
   'lambda '(bound)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-ennreal-p
            'bound
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted scalar-zero)
            (q11352023-quoted scalar-less))
      (list 'q11352023-lintegral-upper-bound-p
            (q11352023-quoted domain-carrier)
            (q11352023-quoted measurable)
            (q11352023-quoted measure)
            (q11352023-quoted ennreal-carrier)
            (q11352023-quoted ennreal-less)
            (q11352023-quoted function)
            'bound
            (q11352023-quoted scalar-zero)
            (q11352023-quoted scalar-add)
            (q11352023-quoted scalar-multiply)
            (q11352023-quoted scalar-less))))
    (list 'q11352023-ennreal-less-equal-p
          (q11352023-quoted value)
          'bound
          (q11352023-quoted scalar-less)))))

(defun q11352023-lintegral-value-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function value)
  (let ((ennreal-carrier
         (q11352023-ennreal-carrier
          scalar-carrier scalar-zero scalar-less))
        (ennreal-less
         (q11352023-ennreal-less-function scalar-less)))
    (and
     (q11352023-function-p
      domain-carrier ennreal-carrier function)
     (q11352023-member-p ennreal-carrier value)
     (q11352023-lintegral-upper-bound-p
      domain-carrier measurable measure ennreal-carrier ennreal-less
      function value scalar-zero scalar-add scalar-multiply scalar-less)
     (q11352023-universal-p
      (q11352023-lintegral-least-upper-bound-function
       scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
       domain-carrier measurable measure ennreal-carrier ennreal-less
       function value)
      '(bound)))))

(defun q11352023-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (let ((ennreal-carrier
         (q11352023-ennreal-carrier
          scalar-carrier scalar-zero scalar-less)))
    (list
     'lambda '(function)
     (q11352023-implies-term
      (list 'q11352023-function-p
            (q11352023-quoted domain-carrier)
            (q11352023-quoted ennreal-carrier)
            'function)
      (list 'q11352023-lintegral-value-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted scalar-zero)
            (q11352023-quoted scalar-add)
            (q11352023-quoted scalar-multiply)
            (q11352023-quoted scalar-less)
            (q11352023-quoted domain-carrier)
            (q11352023-quoted measurable)
            (q11352023-quoted measure)
            'function
            (q11352023-static-apply-term
             lintegral
             (list
              (q11352023-quoted domain-carrier)
              (q11352023-quoted measurable)
              (q11352023-quoted measure)
              'function)))))))

(defun q11352023-lintegral-operation-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (and
   (tamep-functionp lintegral)
   (q11352023-universal-p
    (q11352023-lintegral-values-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    '(function))))

;; The real exponential is the order-topological limit of its power series.
;; Positive-base real power is exp(exponent * log(base)); only positive
;; exponents are needed because the theorem assumes 1 <= p.

(defun q11352023-scalar-subtract
    (scalar-add scalar-negate left right)
  (q11352023-binary-value
   scalar-add left
   (q11352023-unary-value scalar-negate right)))

(defun q11352023-scalar-from-natural
    (count scalar-zero scalar-one scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      scalar-zero
    (q11352023-binary-value
     scalar-add
     (q11352023-scalar-from-natural
      (- count 1) scalar-zero scalar-one scalar-add)
     scalar-one)))

(defun q11352023-natural-factorial (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* count
       (q11352023-natural-factorial (- count 1)))))

(defun q11352023-scalar-natural-power
    (base exponent scalar-one scalar-multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      scalar-one
    (q11352023-binary-value
     scalar-multiply
     (q11352023-scalar-natural-power
      base (- exponent 1) scalar-one scalar-multiply)
     base)))

(defun q11352023-exponential-partial-sum
    (argument count
     scalar-zero scalar-one scalar-add scalar-multiply scalar-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      scalar-zero
    (let* ((index (- count 1))
           (power
            (q11352023-scalar-natural-power
             argument index scalar-one scalar-multiply))
           (factorial
            (q11352023-scalar-from-natural
             (q11352023-natural-factorial index)
             scalar-zero scalar-one scalar-add))
           (term
            (q11352023-binary-value
             scalar-multiply power
             (q11352023-unary-value scalar-inverse factorial))))
      (q11352023-binary-value
       scalar-add
       (q11352023-exponential-partial-sum
        argument index
        scalar-zero scalar-one scalar-add scalar-multiply scalar-inverse)
       term))))

(defun q11352023-exponential-sequence
    (argument
     scalar-zero scalar-one scalar-add scalar-multiply scalar-inverse)
  (list
   'lambda '(count)
   (list 'q11352023-exponential-partial-sum
         (q11352023-quoted argument)
         'count
         (q11352023-quoted scalar-zero)
         (q11352023-quoted scalar-one)
         (q11352023-quoted scalar-add)
         (q11352023-quoted scalar-multiply)
         (q11352023-quoted scalar-inverse))))

(defun q11352023-exponential-value-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less argument value)
  (and
   (q11352023-member-p scalar-carrier argument)
   (q11352023-member-p scalar-carrier value)
   (q11352023-tendsto-order-p
    scalar-carrier scalar-less
    (q11352023-exponential-sequence
     argument scalar-zero scalar-one scalar-add
     scalar-multiply scalar-inverse)
    value)))

(defun q11352023-positive-power-logarithm-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less power base exponent)
  (list
   'lambda '(logarithm)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term scalar-carrier '(logarithm))
     (list 'q11352023-exponential-value-p
           (q11352023-quoted scalar-carrier)
           (q11352023-quoted scalar-zero)
           (q11352023-quoted scalar-one)
           (q11352023-quoted scalar-add)
           (q11352023-quoted scalar-multiply)
           (q11352023-quoted scalar-inverse)
           (q11352023-quoted scalar-less)
           'logarithm
           (q11352023-quoted base))
     (list 'q11352023-exponential-value-p
           (q11352023-quoted scalar-carrier)
           (q11352023-quoted scalar-zero)
           (q11352023-quoted scalar-one)
           (q11352023-quoted scalar-add)
           (q11352023-quoted scalar-multiply)
           (q11352023-quoted scalar-inverse)
           (q11352023-quoted scalar-less)
           (q11352023-static-apply-term
            scalar-multiply
            (list (q11352023-quoted exponent) 'logarithm))
           (q11352023-static-apply-term
            power
            (list (q11352023-quoted base)
                  (q11352023-quoted exponent))))))))

(defun q11352023-real-power-value-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less power base exponent)
  (and
   (q11352023-member-p scalar-carrier base)
   (q11352023-member-p scalar-carrier exponent)
   (not (q11352023-binary-value scalar-less base scalar-zero))
   (q11352023-binary-value scalar-less scalar-zero exponent)
   (if (equal base scalar-zero)
       (equal
        (q11352023-binary-value power base exponent)
        scalar-zero)
     (q11352023-exists-p
      (q11352023-positive-power-logarithm-function
       scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
       scalar-inverse scalar-less power base exponent)
      '(logarithm)))))

(defun q11352023-real-power-values-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less power)
  (list
   'lambda '(base exponent)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (q11352023-static-apply-term scalar-carrier '(base))
      (q11352023-static-apply-term scalar-carrier '(exponent))
      (q11352023-not-term
       (q11352023-static-apply-term
        scalar-less
        (list 'base (q11352023-quoted scalar-zero))))
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'exponent))))
    (list 'q11352023-real-power-value-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-one)
          (q11352023-quoted scalar-add)
          (q11352023-quoted scalar-multiply)
          (q11352023-quoted scalar-inverse)
          (q11352023-quoted scalar-less)
          (q11352023-quoted power)
          'base 'exponent))))

(defun q11352023-real-power-operation-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less power)
  (and
   (tamep-functionp power)
   (q11352023-universal-p
    (q11352023-real-power-values-function
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less power)
    '(base exponent))))

;; Arbitrary normed additive commutative groups.

(defun q11352023-normed-group-laws-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     vector-carrier vector-zero vector-add vector-negate vector-norm)
  (let* ((xy
          (q11352023-static-apply-term vector-add '(x y)))
         (yz
          (q11352023-static-apply-term vector-add '(y z)))
         (neg-x
          (q11352023-static-apply-term vector-negate '(x)))
         (norm-x
          (q11352023-static-apply-term vector-norm '(x)))
         (norm-y
          (q11352023-static-apply-term vector-norm '(y))))
    (list
     'lambda '(x y z)
     (q11352023-implies-term
      (q11352023-and-terms
       (list
        (q11352023-static-apply-term vector-carrier '(x))
        (q11352023-static-apply-term vector-carrier '(y))
        (q11352023-static-apply-term vector-carrier '(z))))
      (q11352023-and-terms
       (list
        (q11352023-static-apply-term vector-carrier (list xy))
        (q11352023-static-apply-term vector-carrier (list neg-x))
        (q11352023-static-apply-term scalar-carrier (list norm-x))
        (list 'equal
              (q11352023-static-apply-term
               vector-add (list xy 'z))
              (q11352023-static-apply-term
               vector-add (list 'x yz)))
        (list 'equal xy
              (q11352023-static-apply-term vector-add '(y x)))
        (list 'equal
              (q11352023-static-apply-term
               vector-add
               (list 'x (q11352023-quoted vector-zero)))
              'x)
        (list 'equal
              (q11352023-static-apply-term
               vector-add (list 'x neg-x))
              (q11352023-quoted vector-zero))
        (q11352023-not-term
         (q11352023-static-apply-term
          scalar-less
          (list norm-x (q11352023-quoted scalar-zero))))
        (q11352023-iff-term
         (list 'equal norm-x (q11352023-quoted scalar-zero))
         (list 'equal 'x (q11352023-quoted vector-zero)))
        (list 'equal
              (q11352023-static-apply-term
               vector-norm (list neg-x))
              norm-x)
        (q11352023-less-equal-term
         scalar-less
         (q11352023-static-apply-term vector-norm (list xy))
         (q11352023-static-apply-term
          scalar-add (list norm-x norm-y)))))))))

(defun q11352023-normed-add-comm-group-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     vector-carrier vector-zero vector-add vector-negate vector-norm)
  (and
   (tamep-functionp vector-carrier)
   (tamep-functionp vector-add)
   (tamep-functionp vector-negate)
   (tamep-functionp vector-norm)
   (q11352023-member-p vector-carrier vector-zero)
   (q11352023-universal-p
    (q11352023-normed-group-laws-function
     scalar-carrier scalar-zero scalar-add scalar-less
     vector-carrier vector-zero vector-add vector-negate vector-norm)
    '(x y z))))

(defun q11352023-vector-subtract
    (vector-add vector-negate left right)
  (q11352023-binary-value
   vector-add left
   (q11352023-unary-value vector-negate right)))

(defun q11352023-vector-difference-function
    (domain-carrier vector-zero vector-add vector-negate left right)
  (list
   'lambda '(x)
   (list 'if
         (q11352023-static-apply-term domain-carrier '(x))
         (q11352023-static-apply-term
          vector-add
          (list
           (q11352023-static-apply-term left '(x))
           (q11352023-static-apply-term
            vector-negate
            (list
             (q11352023-static-apply-term right '(x))))))
         (q11352023-quoted vector-zero))))

(defun q11352023-eventual-vector-close-function
    (scalar-less vector-add vector-negate vector-norm
     sequence limit epsilon cutoff)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q11352023-quoted cutoff) 'n)))
    (q11352023-static-apply-term
     scalar-less
     (list
      (q11352023-static-apply-term
       vector-norm
       (list
        (q11352023-static-apply-term
         vector-add
         (list
          (q11352023-static-apply-term sequence '(n))
          (q11352023-static-apply-term
           vector-negate
           (list (q11352023-quoted limit)))))))
      (q11352023-quoted epsilon))))))

(defun q11352023-vector-cutoff-p
    (scalar-less vector-add vector-negate vector-norm
     sequence limit epsilon cutoff)
  (and
   (natp cutoff)
   (q11352023-universal-p
    (q11352023-eventual-vector-close-function
     scalar-less vector-add vector-negate vector-norm
     sequence limit epsilon cutoff)
    '(n))))

(defun q11352023-vector-cutoff-function
    (scalar-less vector-add vector-negate vector-norm
     sequence limit epsilon)
  (list
   'lambda '(cutoff)
   (list 'q11352023-vector-cutoff-p
         (q11352023-quoted scalar-less)
         (q11352023-quoted vector-add)
         (q11352023-quoted vector-negate)
         (q11352023-quoted vector-norm)
         (q11352023-quoted sequence)
         (q11352023-quoted limit)
         (q11352023-quoted epsilon)
         'cutoff)))

(defun q11352023-vector-convergence-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     vector-add vector-negate vector-norm
     sequence limit)
  (list
   'lambda '(epsilon)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (q11352023-static-apply-term scalar-carrier '(epsilon))
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'epsilon))))
    (list 'q11352023-exists-p
          (list 'q11352023-vector-cutoff-function
                (q11352023-quoted scalar-less)
                (q11352023-quoted vector-add)
                (q11352023-quoted vector-negate)
                (q11352023-quoted vector-norm)
                (q11352023-quoted sequence)
                (q11352023-quoted limit)
                'epsilon)
          (q11352023-quoted '(cutoff))))))

(defun q11352023-vector-converges-p
    (scalar-carrier scalar-zero scalar-less
     vector-carrier vector-add vector-negate vector-norm
     sequence limit)
  (and
   (q11352023-natural-values-p vector-carrier sequence)
   (q11352023-member-p vector-carrier limit)
   (q11352023-universal-p
    (q11352023-vector-convergence-epsilon-function
     scalar-carrier scalar-zero scalar-less
     vector-add vector-negate vector-norm
     sequence limit)
    '(epsilon))))

;; Strong measurability is pointwise convergence of measurable finite-range
;; functions, and AE strong measurability permits an equal-a.e. representative.

(defun q11352023-vector-simple-values-measurable-p
    (domain-carrier measurable function values)
  (if (consp values)
      (and
       (q11352023-member-p
        measurable
        (q11352023-fiber-set
         domain-carrier function (car values)))
       (q11352023-vector-simple-values-measurable-p
        domain-carrier measurable function (cdr values)))
    (equal values nil)))

(defun q11352023-vector-simple-function-p
    (domain-carrier measurable vector-carrier function values)
  (and
   (q11352023-function-p
    domain-carrier vector-carrier function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (q11352023-values-in-carrier-p vector-carrier values)
   (q11352023-values-attained-p domain-carrier function values)
   (q11352023-universal-p
    (q11352023-range-in-values-function
     domain-carrier function values)
    '(x))
   (q11352023-vector-simple-values-measurable-p
    domain-carrier measurable function values)))

(defun q11352023-simple-approximants-function
    (domain-carrier measurable vector-carrier
     approximants value-lists)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (list 'natp 'n)
    (list 'q11352023-vector-simple-function-p
          (q11352023-quoted domain-carrier)
          (q11352023-quoted measurable)
          (q11352023-quoted vector-carrier)
          (q11352023-static-apply-term approximants '(n))
          (q11352023-static-apply-term value-lists '(n))))))

(defun q11352023-simple-approximants-p
    (domain-carrier measurable vector-carrier
     approximants value-lists)
  (and
   (tamep-functionp approximants)
   (tamep-functionp value-lists)
   (q11352023-universal-p
    (q11352023-simple-approximants-function
     domain-carrier measurable vector-carrier
     approximants value-lists)
    '(n))))

(defun q11352023-pointwise-vector-convergence-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier vector-carrier vector-add vector-negate vector-norm
     approximants limit)
  (list
   'lambda '(x)
   (q11352023-implies-term
    (q11352023-static-apply-term domain-carrier '(x))
    (list 'q11352023-vector-converges-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)
          (q11352023-quoted vector-carrier)
          (q11352023-quoted vector-add)
          (q11352023-quoted vector-negate)
          (q11352023-quoted vector-norm)
          (list 'q11352023-pointwise-values-function
                (q11352023-quoted approximants)
                'x)
          (q11352023-static-apply-term limit '(x))))))

(defun q11352023-strongly-measurable-data-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable
     vector-carrier vector-add vector-negate vector-norm
     function approximants value-lists)
  (and
   (q11352023-function-p
    domain-carrier vector-carrier function)
   (q11352023-function-sequence-p
    domain-carrier vector-carrier approximants)
   (q11352023-simple-approximants-p
    domain-carrier measurable vector-carrier
    approximants value-lists)
   (q11352023-universal-p
    (q11352023-pointwise-vector-convergence-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier vector-carrier vector-add vector-negate vector-norm
     approximants function)
    '(x))))

(defun q11352023-strongly-measurable-witness-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable
     vector-carrier vector-add vector-negate vector-norm function)
  (list
   'lambda '(approximants value-lists)
   (list 'q11352023-strongly-measurable-data-p
         (q11352023-quoted scalar-carrier)
         (q11352023-quoted scalar-zero)
         (q11352023-quoted scalar-less)
         (q11352023-quoted domain-carrier)
         (q11352023-quoted measurable)
         (q11352023-quoted vector-carrier)
         (q11352023-quoted vector-add)
         (q11352023-quoted vector-negate)
         (q11352023-quoted vector-norm)
         (q11352023-quoted function)
         'approximants 'value-lists)))

(defun q11352023-strongly-measurable-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable
     vector-carrier vector-add vector-negate vector-norm function)
  (q11352023-exists-p
   (q11352023-strongly-measurable-witness-function
    scalar-carrier scalar-zero scalar-less
    domain-carrier measurable
    vector-carrier vector-add vector-negate vector-norm function)
   '(approximants value-lists)))

(defun q11352023-ae-strongly-measurable-witness-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure
     vector-carrier vector-add vector-negate vector-norm function)
  (list
   'lambda '(representative)
   (q11352023-and-terms
    (list
     (list 'q11352023-strongly-measurable-p
           (q11352023-quoted scalar-carrier)
           (q11352023-quoted scalar-zero)
           (q11352023-quoted scalar-less)
           (q11352023-quoted domain-carrier)
           (q11352023-quoted measurable)
           (q11352023-quoted vector-carrier)
           (q11352023-quoted vector-add)
           (q11352023-quoted vector-negate)
           (q11352023-quoted vector-norm)
           'representative)
     (list 'q11352023-ae-equal-p
           (q11352023-quoted scalar-zero)
           (q11352023-quoted domain-carrier)
           (q11352023-quoted measure)
           (q11352023-quoted vector-carrier)
           (q11352023-quoted function)
           'representative)))))

(defun q11352023-ae-strongly-measurable-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure
     vector-carrier vector-add vector-negate vector-norm function)
  (and
   (q11352023-function-p
    domain-carrier vector-carrier function)
   (q11352023-exists-p
    (q11352023-ae-strongly-measurable-witness-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure
     vector-carrier vector-add vector-negate vector-norm function)
    '(representative))))

;; Lp seminorm comparisons. For positive finite p,
;; eLpNorm(f,p) <= bound is equivalent to
;; lintegral (x |-> ||f x||^p) <= bound^p.

(defun q11352023-powered-norm-function
    (domain-carrier scalar-zero
     vector-norm power function exponent)
  (list
   'lambda '(x)
   (list 'if
         (q11352023-static-apply-term domain-carrier '(x))
         (list 'q11352023-ennreal-finite
               (q11352023-static-apply-term
                power
                (list
                 (q11352023-static-apply-term
                  vector-norm
                  (list
                   (q11352023-static-apply-term function '(x))))
                 (q11352023-quoted exponent))))
         (list 'q11352023-ennreal-finite
               (q11352023-quoted scalar-zero)))))

(defun q11352023-lp-norm-at-most-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-norm power function exponent bound)
  (and
   (q11352023-member-p scalar-carrier bound)
   (not (q11352023-binary-value scalar-less bound scalar-zero))
   (q11352023-binary-value scalar-less scalar-zero exponent)
   (q11352023-ennreal-less-equal-p
    (apply$
     lintegral
     (list
      domain-carrier measurable measure
      (q11352023-powered-norm-function
       domain-carrier scalar-zero vector-norm power
       function exponent)))
    (q11352023-ennreal-finite
     (q11352023-binary-value power bound exponent))
    scalar-less)))

(defun q11352023-mem-lp-bound-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-norm power function exponent)
  (list
   'lambda '(bound)
   (q11352023-and-terms
    (list
     (list 'q11352023-member-p
           (q11352023-quoted scalar-carrier)
           'bound)
     (q11352023-not-term
      (q11352023-static-apply-term
       scalar-less
       (list 'bound (q11352023-quoted scalar-zero))))
     (list 'q11352023-lp-norm-at-most-p
           (q11352023-quoted scalar-carrier)
           (q11352023-quoted scalar-zero)
           (q11352023-quoted scalar-less)
           (q11352023-quoted domain-carrier)
           (q11352023-quoted measurable)
           (q11352023-quoted measure)
           (q11352023-quoted lintegral)
           (q11352023-quoted vector-norm)
           (q11352023-quoted power)
           (q11352023-quoted function)
           (q11352023-quoted exponent)
           'bound)))))

(defun q11352023-mem-lp-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-carrier vector-add vector-negate vector-norm power
     function exponent)
  (and
   (q11352023-ae-strongly-measurable-p
    scalar-carrier scalar-zero scalar-less
    domain-carrier measurable measure
    vector-carrier vector-add vector-negate vector-norm function)
   (q11352023-exists-p
    (q11352023-mem-lp-bound-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-norm power function exponent)
    '(bound))))

(defun q11352023-sequence-mem-lp-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-carrier vector-add vector-negate vector-norm power
     sequence exponent)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (list 'natp 'n)
    (list 'q11352023-mem-lp-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)
          (q11352023-quoted domain-carrier)
          (q11352023-quoted measurable)
          (q11352023-quoted measure)
          (q11352023-quoted lintegral)
          (q11352023-quoted vector-carrier)
          (q11352023-quoted vector-add)
          (q11352023-quoted vector-negate)
          (q11352023-quoted vector-norm)
          (q11352023-quoted power)
          (q11352023-static-apply-term sequence '(n))
          (q11352023-quoted exponent)))))

(defun q11352023-sequence-mem-lp-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-carrier vector-add vector-negate vector-norm power
     sequence exponent)
  (q11352023-universal-p
   (q11352023-sequence-mem-lp-function
    scalar-carrier scalar-zero scalar-less
    domain-carrier measurable measure lintegral
    vector-carrier vector-add vector-negate vector-norm power
    sequence exponent)
   '(n)))

(defun q11352023-indicator-function
    (domain-carrier set vector-zero function)
  (list
   'lambda '(x)
   (list 'if
         (q11352023-and-terms
          (list
           (q11352023-static-apply-term domain-carrier '(x))
           (q11352023-static-apply-term set '(x))))
         (q11352023-static-apply-term function '(x))
         (q11352023-quoted vector-zero))))

(defun q11352023-error-exceeds-set
    (scalar-carrier domain-carrier scalar-less
     vector-add vector-negate vector-norm
     left right threshold)
  (list
   'lambda '(x)
   (q11352023-and-terms
    (list
     (q11352023-static-apply-term domain-carrier '(x))
     (list 'q11352023-member-p
           (q11352023-quoted scalar-carrier)
           (q11352023-quoted threshold))
     (q11352023-less-equal-term
      scalar-less
      (q11352023-quoted threshold)
      (q11352023-static-apply-term
       vector-norm
       (list
        (q11352023-static-apply-term
         vector-add
         (list
          (q11352023-static-apply-term left '(x))
          (q11352023-static-apply-term
           vector-negate
           (list
            (q11352023-static-apply-term right '(x)))))))))))))

;; Convergence in measure.

(defun q11352023-in-measure-eventual-function
    (scalar-carrier scalar-less domain-carrier measure
     vector-add vector-negate vector-norm sequence limit
     error-threshold measure-tolerance cutoff)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted error-threshold))
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted measure-tolerance))
      (list 'natp 'n)
      (list '<= (q11352023-quoted cutoff) 'n)))
    (list 'q11352023-ennreal-less-equal-p
          (q11352023-static-apply-term
           measure
            (list
            (list 'q11352023-error-exceeds-set
                  (q11352023-quoted scalar-carrier)
                  (q11352023-quoted domain-carrier)
                  (q11352023-quoted scalar-less)
                  (q11352023-quoted vector-add)
                  (q11352023-quoted vector-negate)
                  (q11352023-quoted vector-norm)
                  (q11352023-static-apply-term sequence '(n))
                  (q11352023-quoted limit)
                  (q11352023-quoted error-threshold))))
          (list 'q11352023-ennreal-finite
                (q11352023-quoted measure-tolerance))
          (q11352023-quoted scalar-less)))))

(defun q11352023-in-measure-cutoff-p
    (scalar-carrier scalar-less domain-carrier measure
     vector-add vector-negate vector-norm sequence limit
     error-threshold measure-tolerance cutoff)
  (and
   (q11352023-member-p scalar-carrier error-threshold)
   (q11352023-member-p scalar-carrier measure-tolerance)
   (natp cutoff)
   (q11352023-universal-p
    (q11352023-in-measure-eventual-function
     scalar-carrier scalar-less domain-carrier measure
     vector-add vector-negate vector-norm sequence limit
     error-threshold measure-tolerance cutoff)
    '(n))))

(defun q11352023-in-measure-cutoff-function
    (scalar-carrier scalar-less domain-carrier measure
     vector-add vector-negate vector-norm sequence limit
     error-threshold measure-tolerance)
  (list
   'lambda '(cutoff)
   (list 'q11352023-in-measure-cutoff-p
         (q11352023-quoted scalar-carrier)
         (q11352023-quoted scalar-less)
         (q11352023-quoted domain-carrier)
         (q11352023-quoted measure)
         (q11352023-quoted vector-add)
         (q11352023-quoted vector-negate)
         (q11352023-quoted vector-norm)
         (q11352023-quoted sequence)
         (q11352023-quoted limit)
         (q11352023-quoted error-threshold)
         (q11352023-quoted measure-tolerance)
         'cutoff)))

(defun q11352023-in-measure-tolerances-function
    (scalar-carrier scalar-zero scalar-less domain-carrier measure
     vector-add vector-negate vector-norm sequence limit)
  (list
   'lambda '(error-threshold measure-tolerance)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            'error-threshold)
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            'measure-tolerance)
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'error-threshold))
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'measure-tolerance))))
    (list 'q11352023-exists-p
          (list 'q11352023-in-measure-cutoff-function
                (q11352023-quoted scalar-carrier)
                (q11352023-quoted scalar-less)
                (q11352023-quoted domain-carrier)
                (q11352023-quoted measure)
                (q11352023-quoted vector-add)
                (q11352023-quoted vector-negate)
                (q11352023-quoted vector-norm)
                (q11352023-quoted sequence)
                (q11352023-quoted limit)
                'error-threshold 'measure-tolerance)
          (q11352023-quoted '(cutoff))))))

(defun q11352023-tendsto-in-measure-p
    (scalar-carrier scalar-zero scalar-less domain-carrier measure
     vector-add vector-negate vector-norm sequence limit)
  (q11352023-universal-p
   (q11352023-in-measure-tolerances-function
    scalar-carrier scalar-zero scalar-less domain-carrier measure
    vector-add vector-negate vector-norm sequence limit)
   '(error-threshold measure-tolerance)))

;; Uniform integrability.

(defun q11352023-unif-integrable-small-set-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent
     epsilon delta)
  (list
   'lambda '(n set)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted epsilon))
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted delta))
      (list 'natp 'n)
      (q11352023-static-apply-term measurable '(set))
      (list 'q11352023-ennreal-less-equal-p
            (q11352023-static-apply-term measure '(set))
            (list 'q11352023-ennreal-finite
                  (q11352023-quoted delta))
            (q11352023-quoted scalar-less))))
    (list 'q11352023-lp-norm-at-most-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)
          (q11352023-quoted domain-carrier)
          (q11352023-quoted measurable)
          (q11352023-quoted measure)
          (q11352023-quoted lintegral)
          (q11352023-quoted vector-norm)
          (q11352023-quoted power)
          (list 'q11352023-indicator-function
                (q11352023-quoted domain-carrier)
                'set
                (q11352023-quoted vector-zero)
                (q11352023-static-apply-term sequence '(n)))
          (q11352023-quoted exponent)
          (q11352023-quoted epsilon)))))

(defun q11352023-unif-integrable-delta-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent
     epsilon delta)
  (and
   (q11352023-member-p scalar-carrier epsilon)
   (q11352023-member-p scalar-carrier delta)
   (q11352023-binary-value scalar-less scalar-zero delta)
   (q11352023-universal-p
    (q11352023-unif-integrable-small-set-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent
     epsilon delta)
    '(n set))))

(defun q11352023-unif-integrable-delta-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent epsilon)
  (list
   'lambda '(delta)
   (list 'q11352023-unif-integrable-delta-p
         (q11352023-quoted scalar-carrier)
         (q11352023-quoted scalar-zero)
         (q11352023-quoted scalar-less)
         (q11352023-quoted domain-carrier)
         (q11352023-quoted measurable)
         (q11352023-quoted measure)
         (q11352023-quoted lintegral)
         (q11352023-quoted vector-zero)
         (q11352023-quoted vector-norm)
         (q11352023-quoted power)
         (q11352023-quoted sequence)
         (q11352023-quoted exponent)
         (q11352023-quoted epsilon)
         'delta)))

(defun q11352023-unif-integrable-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent)
  (list
   'lambda '(epsilon)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            'epsilon)
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'epsilon))))
    (list 'q11352023-exists-p
          (list 'q11352023-unif-integrable-delta-function
                (q11352023-quoted scalar-carrier)
                (q11352023-quoted scalar-zero)
                (q11352023-quoted scalar-less)
                (q11352023-quoted domain-carrier)
                (q11352023-quoted measurable)
                (q11352023-quoted measure)
                (q11352023-quoted lintegral)
                (q11352023-quoted vector-zero)
                (q11352023-quoted vector-norm)
                (q11352023-quoted power)
                (q11352023-quoted sequence)
                (q11352023-quoted exponent)
                'epsilon)
          (q11352023-quoted '(delta))))))

(defun q11352023-unif-integrable-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent)
  (q11352023-universal-p
   (q11352023-unif-integrable-epsilon-function
    scalar-carrier scalar-zero scalar-less
    domain-carrier measurable measure lintegral
    vector-zero vector-norm power sequence exponent)
   '(epsilon)))

;; Uniform tightness. The witnessing set need not be measurable, matching the
;; source definition; the measure predicate already gives outer-measure values
;; on arbitrary subsets.

(defun q11352023-unif-tight-sequence-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent epsilon set)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted epsilon))
      (list 'natp 'n)))
    (list 'q11352023-lp-norm-at-most-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)
          (q11352023-quoted domain-carrier)
          (q11352023-quoted measurable)
          (q11352023-quoted measure)
          (q11352023-quoted lintegral)
          (q11352023-quoted vector-norm)
          (q11352023-quoted power)
          (list 'q11352023-indicator-function
                (q11352023-quoted domain-carrier)
                (list 'q11352023-complement-set
                      (q11352023-quoted domain-carrier)
                      (q11352023-quoted set))
                (q11352023-quoted vector-zero)
                (q11352023-static-apply-term sequence '(n)))
          (q11352023-quoted exponent)
          (q11352023-quoted epsilon)))))

(defun q11352023-unif-tight-set-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent epsilon set)
  (and
   (q11352023-member-p scalar-carrier epsilon)
   (q11352023-valid-set-p domain-carrier set)
   (not (equal
         (q11352023-unary-value measure set)
         :q11352023-top))
   (q11352023-universal-p
    (q11352023-unif-tight-sequence-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent epsilon set)
    '(n))))

(defun q11352023-unif-tight-set-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent epsilon)
  (list
   'lambda '(set)
   (list 'q11352023-unif-tight-set-p
         (q11352023-quoted scalar-carrier)
         (q11352023-quoted scalar-zero)
         (q11352023-quoted scalar-less)
         (q11352023-quoted domain-carrier)
         (q11352023-quoted measurable)
         (q11352023-quoted measure)
         (q11352023-quoted lintegral)
         (q11352023-quoted vector-zero)
         (q11352023-quoted vector-norm)
         (q11352023-quoted power)
         (q11352023-quoted sequence)
         (q11352023-quoted exponent)
         (q11352023-quoted epsilon)
         'set)))

(defun q11352023-unif-tight-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent)
  (list
   'lambda '(epsilon)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            'epsilon)
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'epsilon))))
    (list 'q11352023-exists-p
          (list 'q11352023-unif-tight-set-function
                (q11352023-quoted scalar-carrier)
                (q11352023-quoted scalar-zero)
                (q11352023-quoted scalar-less)
                (q11352023-quoted domain-carrier)
                (q11352023-quoted measurable)
                (q11352023-quoted measure)
                (q11352023-quoted lintegral)
                (q11352023-quoted vector-zero)
                (q11352023-quoted vector-norm)
                (q11352023-quoted power)
                (q11352023-quoted sequence)
                (q11352023-quoted exponent)
                'epsilon)
          (q11352023-quoted '(set))))))

(defun q11352023-unif-tight-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-norm power sequence exponent)
  (q11352023-universal-p
   (q11352023-unif-tight-epsilon-function
    scalar-carrier scalar-zero scalar-less
    domain-carrier measurable measure lintegral
    vector-zero vector-norm power sequence exponent)
   '(epsilon)))

;; Convergence of eLpNorm(f_n - g,p) to zero.

(defun q11352023-lp-eventual-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm power
     sequence limit exponent epsilon cutoff)
  (list
   'lambda '(n)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            (q11352023-quoted epsilon))
      (list 'natp 'n)
      (list '<= (q11352023-quoted cutoff) 'n)))
    (list 'q11352023-lp-norm-at-most-p
          (q11352023-quoted scalar-carrier)
          (q11352023-quoted scalar-zero)
          (q11352023-quoted scalar-less)
          (q11352023-quoted domain-carrier)
          (q11352023-quoted measurable)
          (q11352023-quoted measure)
          (q11352023-quoted lintegral)
          (q11352023-quoted vector-norm)
          (q11352023-quoted power)
          (list 'q11352023-vector-difference-function
                (q11352023-quoted domain-carrier)
                (q11352023-quoted vector-zero)
                (q11352023-quoted vector-add)
                (q11352023-quoted vector-negate)
                (q11352023-static-apply-term sequence '(n))
                (q11352023-quoted limit))
          (q11352023-quoted exponent)
          (q11352023-quoted epsilon)))))

(defun q11352023-lp-cutoff-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm power
     sequence limit exponent epsilon cutoff)
  (and
   (q11352023-member-p scalar-carrier epsilon)
   (natp cutoff)
   (q11352023-universal-p
    (q11352023-lp-eventual-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm power
     sequence limit exponent epsilon cutoff)
    '(n))))

(defun q11352023-lp-cutoff-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm power
     sequence limit exponent epsilon)
  (list
   'lambda '(cutoff)
   (list 'q11352023-lp-cutoff-p
         (q11352023-quoted scalar-carrier)
         (q11352023-quoted scalar-zero)
         (q11352023-quoted scalar-less)
         (q11352023-quoted domain-carrier)
         (q11352023-quoted measurable)
         (q11352023-quoted measure)
         (q11352023-quoted lintegral)
         (q11352023-quoted vector-zero)
         (q11352023-quoted vector-add)
         (q11352023-quoted vector-negate)
         (q11352023-quoted vector-norm)
         (q11352023-quoted power)
         (q11352023-quoted sequence)
         (q11352023-quoted limit)
         (q11352023-quoted exponent)
         (q11352023-quoted epsilon)
         'cutoff)))

(defun q11352023-lp-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm power
     sequence limit exponent)
  (list
   'lambda '(epsilon)
   (q11352023-implies-term
    (q11352023-and-terms
     (list
      (list 'q11352023-member-p
            (q11352023-quoted scalar-carrier)
            'epsilon)
      (q11352023-static-apply-term
       scalar-less
       (list (q11352023-quoted scalar-zero) 'epsilon))))
    (list 'q11352023-exists-p
          (list 'q11352023-lp-cutoff-function
                (q11352023-quoted scalar-carrier)
                (q11352023-quoted scalar-zero)
                (q11352023-quoted scalar-less)
                (q11352023-quoted domain-carrier)
                (q11352023-quoted measurable)
                (q11352023-quoted measure)
                (q11352023-quoted lintegral)
                (q11352023-quoted vector-zero)
                (q11352023-quoted vector-add)
                (q11352023-quoted vector-negate)
                (q11352023-quoted vector-norm)
                (q11352023-quoted power)
                (q11352023-quoted sequence)
                (q11352023-quoted limit)
                (q11352023-quoted exponent)
                'epsilon)
          (q11352023-quoted '(cutoff))))))

(defun q11352023-tendsto-lp-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm power
     sequence limit exponent)
  (q11352023-universal-p
   (q11352023-lp-epsilon-function
    scalar-carrier scalar-zero scalar-less
    domain-carrier measurable measure lintegral
    vector-zero vector-add vector-negate vector-norm power
    sequence limit exponent)
   '(epsilon)))

(defun thousand-theorems-q11352023-vitali-convergence-theorem-statement
    (scalar-carrier scalar-zero scalar-one
     scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-less scalar-supremum scalar-power
     domain-carrier measurable measure lintegral
     vector-carrier vector-zero vector-add vector-negate vector-norm
     exponent sequence limit)
  (implies
   (and
    (q11352023-real-field-p
     scalar-carrier scalar-zero scalar-one
     scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-less scalar-supremum)
    (q11352023-real-power-operation-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-inverse scalar-less scalar-power)
    (q11352023-measure-space-p
     scalar-carrier scalar-zero scalar-add scalar-less
     domain-carrier measurable measure)
    (q11352023-lintegral-operation-p
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    (q11352023-normed-add-comm-group-p
     scalar-carrier scalar-zero scalar-add scalar-less
     vector-carrier vector-zero vector-add vector-negate vector-norm)
    (q11352023-member-p scalar-carrier exponent)
    (not (q11352023-binary-value scalar-less exponent scalar-one))
    (q11352023-function-sequence-p
     domain-carrier vector-carrier sequence)
    (q11352023-function-p
     domain-carrier vector-carrier limit)
    (q11352023-sequence-mem-lp-p
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-carrier vector-add vector-negate vector-norm scalar-power
     sequence exponent)
    (q11352023-mem-lp-p
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-carrier vector-add vector-negate vector-norm scalar-power
     limit exponent))
   (iff
    (and
     (q11352023-tendsto-in-measure-p
      scalar-carrier scalar-zero scalar-less domain-carrier measure
      vector-add vector-negate vector-norm sequence limit)
     (q11352023-unif-integrable-p
      scalar-carrier scalar-zero scalar-less
      domain-carrier measurable measure lintegral
      vector-zero vector-norm scalar-power sequence exponent)
     (q11352023-unif-tight-p
      scalar-carrier scalar-zero scalar-less
      domain-carrier measurable measure lintegral
      vector-zero vector-norm scalar-power sequence exponent))
    (q11352023-tendsto-lp-p
     scalar-carrier scalar-zero scalar-less
     domain-carrier measurable measure lintegral
     vector-zero vector-add vector-negate vector-norm scalar-power
     sequence limit exponent))))

(value-triple :itpeval-statement-checked)
:q
