;; Statement-only formalization of thousand-theorems corpus artifact Q190391,
;; "Central limit theorem": square-integrable independent identically
;; distributed real random variables have centered partial sums, normalized
;; by the square root of the sample size, converging in distribution to a
;; centered Gaussian variable with the variance of the first summand,
;; including the zero-variance case. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, functions, sigma algebras, and operations are tame APPLY$
;; function objects. FN-EQUAL supplies unbounded universal quantification, and
;; inequality with a constant-false function supplies internal existential
;; witnesses. The scalar structure is a Dedekind-complete ordered field, hence
;; a presentation of the real field. The measure on an arbitrary subset is
;; characterized as the infimum of the measures of its measurable supersets,
;; so null exceptional sets use outer-measure semantics. Measurability is
;; defined through upper-ray preimages, lintegral is the supremum of integrals
;; of measurable finite-range simple functions below the integrand, and the
;; real integral is defined from positive and negative parts. Weak convergence
;; is rendered by its equivalent bounded-continuous-test-function
;; characterization along the sequential filter.

(defun q190391-quoted (object)
  (list 'quote object))

(defun q190391-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q190391-term-list (cdr terms)))
    (q190391-quoted nil)))

(defun q190391-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (q190391-term-list arguments)))

(defun q190391-static-apply-term (function arguments)
  (q190391-apply-term
   (q190391-quoted function)
   arguments))

(defun q190391-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q190391-and-terms (cdr terms))
            (q190391-quoted nil))
    (q190391-quoted t)))

(defun q190391-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q190391-quoted t)
            (q190391-or-terms (cdr terms)))
    (q190391-quoted nil)))

(defun q190391-not-term (term)
  (list 'if term
        (q190391-quoted nil)
        (q190391-quoted t)))

(defun q190391-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q190391-quoted t)))

(defun q190391-iff-term (left right)
  (list 'if left
        (list 'if right
              (q190391-quoted t)
              (q190391-quoted nil))
        (list 'if right
              (q190391-quoted nil)
              (q190391-quoted t))))

(defun q190391-true-function (formals)
  (list 'lambda formals (q190391-quoted t)))

(defun q190391-false-function (formals)
  (list 'lambda formals (q190391-quoted nil)))

(defun q190391-universal-p (function formals)
  (let ((always-true (q190391-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun q190391-exists-p (function formals)
  (let ((always-false (q190391-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun q190391-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q190391-unary-value (function object)
  (apply$ function (list object)))

(defun q190391-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun q190391-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term carrier '(x))
      (q190391-static-apply-term left '(x))))
    (q190391-static-apply-term right '(x)))))

(defun q190391-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q190391-universal-p
    (q190391-set-subset-function carrier left right)
    '(x))))

(defun q190391-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q190391-set-subset-p carrier set carrier)))

(defun q190391-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term carrier '(x))
    (q190391-iff-term
     (q190391-static-apply-term left '(x))
     (q190391-static-apply-term right '(x))))))

(defun q190391-set-equiv-p (carrier left right)
  (and
   (q190391-valid-set-p carrier left)
   (q190391-valid-set-p carrier right)
   (q190391-universal-p
    (q190391-set-equiv-function carrier left right)
    '(x))))

(defun q190391-empty-set ()
  (list 'lambda '(x) (q190391-quoted nil)))

(defun q190391-full-set (carrier)
  (list 'lambda '(x)
        (q190391-static-apply-term carrier '(x))))

(defun q190391-complement-set (carrier set)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term carrier '(x))
     (q190391-not-term
      (q190391-static-apply-term set '(x)))))))

(defun q190391-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term domain-carrier '(x))
    (q190391-static-apply-term
     codomain-carrier
     (list (q190391-static-apply-term function '(x)))))))

(defun q190391-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (q190391-universal-p
    (q190391-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q190391-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (q190391-static-apply-term add '(x y)))
         (yz-add (q190391-static-apply-term add '(y z)))
         (xy-mul (q190391-static-apply-term multiply '(x y)))
         (yz-mul (q190391-static-apply-term multiply '(y z)))
         (neg-x (q190391-static-apply-term negate '(x)))
         (inv-x (q190391-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (q190391-implies-term
      (q190391-and-terms
       (list
        (q190391-static-apply-term carrier '(x))
        (q190391-static-apply-term carrier '(y))
        (q190391-static-apply-term carrier '(z))))
      (q190391-and-terms
       (list
        (q190391-static-apply-term carrier (list xy-add))
        (q190391-static-apply-term carrier (list xy-mul))
        (q190391-static-apply-term carrier (list neg-x))
        (q190391-static-apply-term carrier (list inv-x))
        (list 'equal
              (q190391-static-apply-term add (list xy-add 'z))
              (q190391-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (q190391-static-apply-term add '(y x)))
        (list 'equal
              (q190391-static-apply-term
               add (list 'x (q190391-quoted zero)))
              'x)
        (list 'equal
              (q190391-static-apply-term add (list 'x neg-x))
              (q190391-quoted zero))
        (list 'equal
              (q190391-static-apply-term multiply (list xy-mul 'z))
              (q190391-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (q190391-static-apply-term multiply '(y x)))
        (list 'equal
              (q190391-static-apply-term
               multiply (list 'x (q190391-quoted one)))
              'x)
        (q190391-implies-term
         (list 'equal 'x (q190391-quoted zero))
         (list 'equal inv-x (q190391-quoted zero)))
        (q190391-implies-term
         (q190391-not-term
          (list 'equal 'x (q190391-quoted zero)))
         (list 'equal
               (q190391-static-apply-term
                multiply (list 'x inv-x))
               (q190391-quoted one)))
        (list 'equal
              (q190391-static-apply-term multiply (list 'x yz-add))
              (q190391-static-apply-term
               add
               (list
                (q190391-static-apply-term multiply '(x y))
                (q190391-static-apply-term multiply '(x z)))))))))))

(defun q190391-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (q190391-static-apply-term less '(x y)))
        (yx (q190391-static-apply-term less '(y x)))
        (yz (q190391-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (q190391-implies-term
      (q190391-and-terms
       (list
        (q190391-static-apply-term carrier '(x))
        (q190391-static-apply-term carrier '(y))
        (q190391-static-apply-term carrier '(z))))
      (q190391-and-terms
       (list
        (q190391-not-term
         (q190391-static-apply-term less '(x x)))
        (q190391-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q190391-implies-term
         (q190391-and-terms (list xy yz))
         (q190391-static-apply-term less '(x z)))
        (q190391-implies-term
         xy
         (q190391-static-apply-term
          less
          (list
           (q190391-static-apply-term add '(x z))
           (q190391-static-apply-term add '(y z)))))
        (q190391-implies-term
         (q190391-and-terms
          (list
           (q190391-static-apply-term
            less (list (q190391-quoted zero) 'x))
           (q190391-static-apply-term
            less (list (q190391-quoted zero) 'y))))
         (q190391-static-apply-term
          less
          (list
           (q190391-quoted zero)
           (q190391-static-apply-term multiply '(x y)))))))))))

(defun q190391-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term carrier '(x))
      (q190391-static-apply-term set '(x))))
    (q190391-not-term
     (q190391-static-apply-term
      less (list (q190391-quoted upper) 'x))))))

(defun q190391-upper-bound-p
    (carrier less set upper)
  (and
   (q190391-member-p carrier upper)
   (q190391-valid-set-p carrier set)
   (q190391-universal-p
    (q190391-upper-bound-function carrier less set upper)
    '(x))))

(defun q190391-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term carrier '(x))
     (q190391-static-apply-term set '(x))))))

(defun q190391-set-nonempty-p (carrier set)
  (and
   (q190391-valid-set-p carrier set)
   (q190391-exists-p
    (q190391-set-nonempty-function carrier set)
    '(x))))

(defun q190391-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'q190391-upper-bound-p
         (q190391-quoted carrier)
         (q190391-quoted less)
         (q190391-quoted set)
         'upper)))

(defun q190391-bounded-above-p (carrier less set)
  (q190391-exists-p
   (q190391-bounded-above-function carrier less set)
   '(upper)))

(defun q190391-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (q190391-implies-term
    (list 'q190391-upper-bound-p
          (q190391-quoted carrier)
          (q190391-quoted less)
          (q190391-quoted set)
          'upper)
    (q190391-not-term
     (q190391-static-apply-term
      less (list 'upper (q190391-quoted supremum)))))))

(defun q190391-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q190391-upper-bound-p carrier less set supremum)
   (q190391-universal-p
    (q190391-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q190391-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-valid-set-p
            (q190391-quoted carrier) 'set)
      (list 'q190391-set-nonempty-p
            (q190391-quoted carrier) 'set)
      (list 'q190391-bounded-above-p
            (q190391-quoted carrier)
            (q190391-quoted less)
            'set)))
    (list 'q190391-least-upper-bound-p
          (q190391-quoted carrier)
          (q190391-quoted less)
          'set
          (q190391-static-apply-term
           supremum-operation '(set))))))

(defun q190391-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q190391-member-p carrier zero)
   (q190391-member-p carrier one)
   (not (equal zero one))
   (q190391-universal-p
    (q190391-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q190391-universal-p
    (q190391-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q190391-universal-p
    (q190391-completeness-function
     carrier less supremum)
    '(set))
   (q190391-binary-value less zero one)))

(defun q190391-scalar-absolute-value
    (less zero negate value)
  (if (q190391-binary-value less value zero)
      (q190391-unary-value negate value)
    value))
;; Sigma algebras.

(defun q190391-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (q190391-implies-term
    (list 'q190391-set-equiv-p
          (q190391-quoted carrier)
          'left 'right)
    (q190391-iff-term
     (q190391-static-apply-term family '(left))
     (q190391-static-apply-term family '(right))))))

(defun q190391-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term family '(set))
    (list 'q190391-valid-set-p
          (q190391-quoted carrier)
          'set))))

(defun q190391-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q190391-universal-p
    (q190391-family-extensional-function carrier family)
    '(left right))
   (q190391-universal-p
    (q190391-family-members-valid-function carrier family)
    '(set))))

(defun q190391-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (q190391-and-terms
    (list
     (list 'natp 'n)
     (q190391-apply-term
      (q190391-static-apply-term sequence '(n))
      (list (q190391-quoted x)))))))

(defun q190391-sequence-union-member-p (sequence x)
  (q190391-exists-p
   (q190391-sequence-union-member-function sequence x)
   '(n)))

(defun q190391-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term carrier '(x))
     (list 'q190391-sequence-union-member-p
           (q190391-quoted sequence)
           'x)))))

(defun q190391-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (q190391-implies-term
    (list 'natp 'n)
    (list 'q190391-valid-set-p
          (q190391-quoted carrier)
          (q190391-static-apply-term sequence '(n))))))

(defun q190391-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (q190391-universal-p
    (q190391-sequence-of-sets-function carrier sequence)
    '(n))))

(defun q190391-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (q190391-implies-term
    (list 'natp 'n)
    (q190391-static-apply-term
     family
     (list (q190391-static-apply-term sequence '(n)))))))

(defun q190391-sequence-members-family-p
    (carrier family sequence)
  (and
   (q190391-sequence-of-sets-p carrier sequence)
   (q190391-universal-p
    (q190391-sequence-members-family-function family sequence)
    '(n))))

(defun q190391-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term family '(set))
    (q190391-static-apply-term
     family
     (list
      (list 'q190391-complement-set
            (q190391-quoted carrier)
            'set))))))

(defun q190391-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (q190391-implies-term
    (list 'q190391-sequence-members-family-p
          (q190391-quoted carrier)
          (q190391-quoted family)
          'sequence)
    (q190391-static-apply-term
     family
     (list
      (list 'q190391-sequence-union-set
            (q190391-quoted carrier)
            'sequence))))))

(defun q190391-sigma-algebra-p (carrier family)
  (and
   (q190391-family-of-sets-p carrier family)
   (q190391-member-p family (q190391-empty-set))
   (q190391-universal-p
    (q190391-sigma-complement-function carrier family)
    '(set))
   (q190391-universal-p
    (q190391-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun q190391-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :q190391-top)
   (and
    (consp value)
    (equal (car value) :q190391-finite)
    (q190391-member-p scalar-carrier (cdr value))
    (not
     (q190391-binary-value scalar-less (cdr value) scalar-zero)))))

(defun q190391-ennreal-finite (value)
  (cons :q190391-finite value))

(defun q190391-ennreal-zero (scalar-zero)
  (q190391-ennreal-finite scalar-zero))

(defun q190391-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :q190391-top) nil)
   ((equal right :q190391-top) t)
   (t
    (q190391-binary-value scalar-less (cdr left) (cdr right)))))

(defun q190391-ennreal-less-equal-p (left right scalar-less)
  (not (q190391-ennreal-less-p right left scalar-less)))

(defun q190391-ennreal-add (left right scalar-add)
  (if (or (equal left :q190391-top)
          (equal right :q190391-top))
      :q190391-top
    (q190391-ennreal-finite
     (q190391-binary-value scalar-add (cdr left) (cdr right)))))

(defun q190391-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (q190391-ennreal-zero scalar-zero))
        (equal right (q190391-ennreal-zero scalar-zero)))
    (q190391-ennreal-zero scalar-zero))
   ((or (equal left :q190391-top)
        (equal right :q190391-top))
    :q190391-top)
   (t
    (q190391-ennreal-finite
     (q190391-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun q190391-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q190391-ennreal-zero scalar-zero)
    (q190391-ennreal-add
     (q190391-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (q190391-unary-value sequence (- count 1))
     scalar-add)))

(defun q190391-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (q190391-implies-term
    (list 'natp 'count)
    (list 'q190391-ennreal-less-equal-p
          (list 'q190391-finite-ennreal-sum
                (q190391-quoted sequence)
                'count
                (q190391-quoted scalar-zero)
                (q190391-quoted scalar-add))
          (q190391-quoted total)
          (q190391-quoted scalar-less)))))

(defun q190391-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (q190391-universal-p
   (q190391-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun q190391-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-ennreal-p
            'bound
            (q190391-quoted scalar-carrier)
            (q190391-quoted scalar-zero)
            (q190391-quoted scalar-less))
      (list 'q190391-sum-upper-bound-p
            (q190391-quoted sequence)
            'bound
            (q190391-quoted scalar-zero)
            (q190391-quoted scalar-add)
            (q190391-quoted scalar-less))))
    (list 'q190391-ennreal-less-equal-p
          (q190391-quoted total)
          'bound
          (q190391-quoted scalar-less)))))

(defun q190391-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (q190391-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (q190391-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (q190391-universal-p
    (q190391-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun q190391-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (q190391-implies-term
    (list 'q190391-set-equiv-p
          (q190391-quoted carrier)
          'left 'right)
    (list 'equal
          (q190391-static-apply-term measure '(left))
          (q190391-static-apply-term measure '(right))))))

(defun q190391-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (q190391-implies-term
    (list 'q190391-valid-set-p
          (q190391-quoted carrier)
          'set)
    (list 'q190391-ennreal-p
          (q190391-static-apply-term measure '(set))
          (q190391-quoted scalar-carrier)
          (q190391-quoted scalar-zero)
          (q190391-quoted scalar-less)))))

(defun q190391-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (q190391-static-apply-term
    measure
    (list (q190391-static-apply-term sequence '(n))))))

(defun q190391-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term carrier '(x))
    (q190391-not-term
     (q190391-and-terms
      (list
       (q190391-static-apply-term left '(x))
       (q190391-static-apply-term right '(x))))))))

(defun q190391-disjoint-sets-p (carrier left right)
  (q190391-universal-p
   (q190391-disjoint-sets-function carrier left right)
   '(x)))

(defun q190391-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (q190391-not-term (list 'equal 'm 'n))))
    (list 'q190391-disjoint-sets-p
          (q190391-quoted carrier)
          (q190391-static-apply-term sequence '(m))
          (q190391-static-apply-term sequence '(n))))))

(defun q190391-pairwise-disjoint-p (carrier sequence)
  (q190391-universal-p
   (q190391-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun q190391-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-sequence-members-family-p
            (q190391-quoted carrier)
            (q190391-quoted measurable)
            'sequence)
      (list 'q190391-pairwise-disjoint-p
            (q190391-quoted carrier)
            'sequence)))
    (list 'q190391-countable-sum-p
          (list 'q190391-measure-sequence-values
                (q190391-quoted measure)
                'sequence)
          (q190391-static-apply-term
           measure
           (list
            (list 'q190391-sequence-union-set
                  (q190391-quoted carrier)
                  'sequence)))
          (q190391-quoted scalar-carrier)
          (q190391-quoted scalar-zero)
          (q190391-quoted scalar-add)
          (q190391-quoted scalar-less)))))

(defun q190391-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term measurable '(superset))
      (list 'q190391-set-subset-p
            (q190391-quoted carrier)
            (q190391-quoted set)
            'superset)))
    (list 'q190391-ennreal-less-equal-p
          (q190391-quoted lower)
          (q190391-static-apply-term measure '(superset))
          (q190391-quoted scalar-less)))))

(defun q190391-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (q190391-universal-p
   (q190391-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun q190391-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-ennreal-p
            'lower
            (q190391-quoted scalar-carrier)
            (q190391-quoted scalar-zero)
            (q190391-quoted scalar-less))
      (list 'q190391-measurable-superset-lower-bound-p
            (q190391-quoted carrier)
            (q190391-quoted measurable)
            (q190391-quoted measure)
            (q190391-quoted set)
            'lower
            (q190391-quoted scalar-less))))
    (list 'q190391-ennreal-less-equal-p
          'lower
          (q190391-static-apply-term
           measure (list (q190391-quoted set)))
          (q190391-quoted scalar-less)))))

(defun q190391-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (q190391-valid-set-p carrier set)
   (q190391-measurable-superset-lower-bound-p
    carrier measurable measure set
    (q190391-unary-value measure set)
    scalar-less)
   (q190391-universal-p
    (q190391-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun q190391-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (q190391-implies-term
    (list 'q190391-valid-set-p
          (q190391-quoted carrier)
          'set)
    (list 'q190391-outer-value-p
          (q190391-quoted scalar-carrier)
          (q190391-quoted scalar-zero)
          (q190391-quoted scalar-less)
          (q190391-quoted carrier)
          (q190391-quoted measurable)
          (q190391-quoted measure)
          'set))))

(defun q190391-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (q190391-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (q190391-universal-p
    (q190391-measure-extensional-function carrier measure)
    '(left right))
   (q190391-universal-p
    (q190391-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (equal
    (q190391-unary-value measure (q190391-empty-set))
    (q190391-ennreal-zero scalar-zero))
   (q190391-universal-p
    (q190391-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (q190391-universal-p
    (q190391-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; The extended-nonnegative-real carrier and order used by lower integrals.

(defun q190391-ennreal-carrier
    (scalar-carrier scalar-zero scalar-less)
  (list
   'lambda '(value)
   (list 'q190391-ennreal-p
         'value
         (q190391-quoted scalar-carrier)
         (q190391-quoted scalar-zero)
         (q190391-quoted scalar-less))))

(defun q190391-ennreal-less-function (scalar-less)
  (list
   'lambda '(left right)
   (list 'q190391-ennreal-less-p
         'left 'right
         (q190391-quoted scalar-less))))

(defun q190391-null-set-p
    (scalar-zero domain-carrier measure set)
  (and
   (q190391-valid-set-p domain-carrier set)
   (equal
    (q190391-unary-value measure set)
    (q190391-ennreal-zero scalar-zero))))

;; Equality almost everywhere.

(defun q190391-disagreement-set
    (domain-carrier left right)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term domain-carrier '(x))
     (q190391-not-term
      (list 'equal
            (q190391-static-apply-term left '(x))
            (q190391-static-apply-term right '(x))))))))

(defun q190391-ae-equal-p
    (scalar-zero domain-carrier measure codomain-carrier left right)
  (and
   (q190391-function-p domain-carrier codomain-carrier left)
   (q190391-function-p domain-carrier codomain-carrier right)
   (q190391-null-set-p
    scalar-zero domain-carrier measure
    (q190391-disagreement-set domain-carrier left right))))

;; Standard measurability is characterized by measurable upper-ray preimages.

(defun q190391-upper-ray-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term domain-carrier '(x))
     (q190391-static-apply-term
      less
      (list (q190391-quoted threshold)
            (q190391-static-apply-term function '(x))))))))

(defun q190391-measurable-upper-rays-function
    (domain-carrier measurable codomain-carrier less function)
  (list
   'lambda '(threshold)
   (q190391-implies-term
    (q190391-static-apply-term codomain-carrier '(threshold))
    (q190391-static-apply-term
     measurable
     (list
      (list 'q190391-upper-ray-preimage-set
            (q190391-quoted domain-carrier)
            (q190391-quoted function)
            (q190391-quoted less)
            'threshold))))))

(defun q190391-measurable-function-p
    (domain-carrier measurable codomain-carrier less function)
  (and
   (q190391-function-p domain-carrier codomain-carrier function)
   (q190391-universal-p
    (q190391-measurable-upper-rays-function
     domain-carrier measurable codomain-carrier less function)
    '(threshold))))

(defun q190391-ae-measurable-witness-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (list
   'lambda '(representative)
   (q190391-and-terms
    (list
     (list 'q190391-measurable-function-p
           (q190391-quoted domain-carrier)
           (q190391-quoted measurable)
           (q190391-quoted codomain-carrier)
           (q190391-quoted less)
           'representative)
     (list 'q190391-ae-equal-p
           (q190391-quoted scalar-zero)
           (q190391-quoted domain-carrier)
           (q190391-quoted measure)
           (q190391-quoted codomain-carrier)
           (q190391-quoted function)
           'representative)))))

(defun q190391-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (and
   (q190391-function-p domain-carrier codomain-carrier function)
   (q190391-exists-p
    (q190391-ae-measurable-witness-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
    '(representative))))

;; The lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple functions below the integrand.

(defun q190391-fiber-set (domain-carrier function value)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term domain-carrier '(x))
     (list 'equal
           (q190391-static-apply-term function '(x))
           (q190391-quoted value))))))

(defun q190391-values-in-carrier-p (carrier values)
  (if (consp values)
      (and
       (q190391-member-p carrier (car values))
       (q190391-values-in-carrier-p carrier (cdr values)))
    (equal values nil)))

(defun q190391-value-attained-function
    (domain-carrier function value)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term domain-carrier '(x))
     (list 'equal
           (q190391-static-apply-term function '(x))
           (q190391-quoted value))))))

(defun q190391-value-attained-p
    (domain-carrier function value)
  (q190391-exists-p
   (q190391-value-attained-function
    domain-carrier function value)
   '(x)))

(defun q190391-values-attained-p
    (domain-carrier function values)
  (if (consp values)
      (and
       (q190391-value-attained-p
        domain-carrier function (car values))
       (q190391-values-attained-p
        domain-carrier function (cdr values)))
    (equal values nil)))

(defun q190391-range-in-values-function
    (domain-carrier function values)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term domain-carrier '(x))
    (list 'member-equal
          (q190391-static-apply-term function '(x))
          (q190391-quoted values)))))

(defun q190391-simple-function-p
    (domain-carrier measurable codomain-carrier less function values)
  (and
   (q190391-measurable-function-p
    domain-carrier measurable codomain-carrier less function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (q190391-values-in-carrier-p codomain-carrier values)
   (q190391-values-attained-p domain-carrier function values)
   (q190391-universal-p
    (q190391-range-in-values-function
     domain-carrier function values)
    '(x))))

(defun q190391-finite-simple-integral
    (domain-carrier measure function values
     scalar-zero scalar-add scalar-multiply)
  (if (consp values)
      (q190391-ennreal-add
       (q190391-ennreal-multiply
        (car values)
        (q190391-unary-value
         measure
         (q190391-fiber-set
          domain-carrier function (car values)))
        scalar-zero scalar-multiply)
       (q190391-finite-simple-integral
        domain-carrier measure function (cdr values)
        scalar-zero scalar-add scalar-multiply)
       scalar-add)
    (q190391-ennreal-zero scalar-zero)))

(defun q190391-simple-below-function
    (domain-carrier simple function scalar-less)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term domain-carrier '(x))
    (list 'q190391-ennreal-less-equal-p
          (q190391-static-apply-term simple '(x))
          (q190391-static-apply-term function '(x))
          (q190391-quoted scalar-less)))))

(defun q190391-simple-below-p
    (domain-carrier simple function scalar-less)
  (q190391-universal-p
   (q190391-simple-below-function
    domain-carrier simple function scalar-less)
   '(x)))

(defun q190391-lintegral-upper-bound-function
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (list
   'lambda '(simple values)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-simple-function-p
            (q190391-quoted domain-carrier)
            (q190391-quoted measurable)
            (q190391-quoted ennreal-carrier)
            (q190391-quoted ennreal-less)
            'simple 'values)
      (list 'q190391-simple-below-p
            (q190391-quoted domain-carrier)
            'simple
            (q190391-quoted function)
            (q190391-quoted scalar-less))))
    (list 'q190391-ennreal-less-equal-p
          (list 'q190391-finite-simple-integral
                (q190391-quoted domain-carrier)
                (q190391-quoted measure)
                'simple 'values
                (q190391-quoted scalar-zero)
                (q190391-quoted scalar-add)
                (q190391-quoted scalar-multiply))
          (q190391-quoted bound)
          (q190391-quoted scalar-less)))))

(defun q190391-lintegral-upper-bound-p
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (q190391-universal-p
   (q190391-lintegral-upper-bound-function
    domain-carrier measurable measure ennreal-carrier ennreal-less
    function bound scalar-zero scalar-add scalar-multiply scalar-less)
   '(simple values)))

(defun q190391-lintegral-least-upper-bound-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     function value)
  (list
   'lambda '(bound)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-ennreal-p
            'bound
            (q190391-quoted scalar-carrier)
            (q190391-quoted scalar-zero)
            (q190391-quoted scalar-less))
      (list 'q190391-lintegral-upper-bound-p
            (q190391-quoted domain-carrier)
            (q190391-quoted measurable)
            (q190391-quoted measure)
            (q190391-quoted ennreal-carrier)
            (q190391-quoted ennreal-less)
            (q190391-quoted function)
            'bound
            (q190391-quoted scalar-zero)
            (q190391-quoted scalar-add)
            (q190391-quoted scalar-multiply)
            (q190391-quoted scalar-less))))
    (list 'q190391-ennreal-less-equal-p
          (q190391-quoted value)
          'bound
          (q190391-quoted scalar-less)))))

(defun q190391-lintegral-value-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function value)
  (let ((ennreal-carrier
         (q190391-ennreal-carrier
          scalar-carrier scalar-zero scalar-less))
        (ennreal-less
         (q190391-ennreal-less-function scalar-less)))
    (and
     (q190391-function-p
      domain-carrier ennreal-carrier function)
     (q190391-member-p ennreal-carrier value)
     (q190391-lintegral-upper-bound-p
      domain-carrier measurable measure ennreal-carrier ennreal-less
      function value scalar-zero scalar-add scalar-multiply scalar-less)
     (q190391-universal-p
      (q190391-lintegral-least-upper-bound-function
       scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
       domain-carrier measurable measure ennreal-carrier ennreal-less
       function value)
      '(bound)))))

(defun q190391-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (let ((ennreal-carrier
         (q190391-ennreal-carrier
          scalar-carrier scalar-zero scalar-less)))
    (list
     'lambda '(function)
     (q190391-implies-term
      (list 'q190391-function-p
            (q190391-quoted domain-carrier)
            (q190391-quoted ennreal-carrier)
            'function)
      (list 'q190391-lintegral-value-p
            (q190391-quoted scalar-carrier)
            (q190391-quoted scalar-zero)
            (q190391-quoted scalar-add)
            (q190391-quoted scalar-multiply)
            (q190391-quoted scalar-less)
            (q190391-quoted domain-carrier)
            (q190391-quoted measurable)
            (q190391-quoted measure)
            'function
            (q190391-static-apply-term
             lintegral
             (list
              (q190391-quoted domain-carrier)
              (q190391-quoted measurable)
              (q190391-quoted measure)
              'function)))))))

(defun q190391-lintegral-operation-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (and
   (tamep-functionp lintegral)
   (q190391-universal-p
    (q190391-lintegral-values-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    '(function))))

;; For real functions, AE strong measurability is the preceding AE
;; measurability because the real line is separable. Integrability and the
;; Bochner integral are then defined from the exact lower integral.

(defun q190391-real-enorm-function
    (real-zero real-negate real-less function)
  (list
   'lambda '(x)
   (list 'q190391-ennreal-finite
         (list 'q190391-scalar-absolute-value
               (q190391-quoted real-less)
               (q190391-quoted real-zero)
               (q190391-quoted real-negate)
               (q190391-static-apply-term function '(x))))))

(defun q190391-real-positive-part-function
    (real-zero real-less function)
  (list
   'lambda '(x)
   (list 'q190391-ennreal-finite
         (list 'if
               (q190391-static-apply-term
                real-less
                (list
                 (q190391-static-apply-term function '(x))
                 (q190391-quoted real-zero)))
               (q190391-quoted real-zero)
               (q190391-static-apply-term function '(x))))))

(defun q190391-real-negative-part-function
    (real-zero real-negate real-less function)
  (let ((negative-value
         (q190391-static-apply-term
          real-negate
          (list (q190391-static-apply-term function '(x))))))
    (list
     'lambda '(x)
     (list 'q190391-ennreal-finite
           (list 'if
                 (q190391-static-apply-term
                  real-less
                  (list negative-value
                        (q190391-quoted real-zero)))
                 (q190391-quoted real-zero)
                 negative-value)))))

(defun q190391-ennreal-to-real (value real-zero)
  (if (equal value :q190391-top)
      real-zero
    (if (and (consp value)
             (equal (car value) :q190391-finite))
        (cdr value)
      real-zero)))

(defun q190391-integrable-p
    (real-zero real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (and
   (q190391-ae-measurable-p
    real-zero domain-carrier measurable measure
    real-carrier real-less function)
   (q190391-ennreal-less-p
    (apply$
     lintegral
     (list
      domain-carrier measurable measure
      (q190391-real-enorm-function
       real-zero real-negate real-less function)))
    :q190391-top
    real-less)))

(defun q190391-real-integral-value
    (real-zero real-add real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (if
      (q190391-integrable-p
       real-zero real-negate real-less
       domain-carrier measurable measure real-carrier function lintegral)
      (q190391-binary-value
       real-add
       (q190391-ennreal-to-real
        (apply$
         lintegral
         (list
          domain-carrier measurable measure
          (q190391-real-positive-part-function
           real-zero real-less function)))
        real-zero)
       (q190391-unary-value
        real-negate
        (q190391-ennreal-to-real
         (apply$
          lintegral
          (list
           domain-carrier measurable measure
           (q190391-real-negative-part-function
            real-zero real-negate real-less function)))
         real-zero)))
    real-zero))

;; General topologies and continuous maps.

(defun q190391-union-member-function (family x)
  (list
   'lambda '(set)
   (q190391-and-terms
    (list
     (q190391-static-apply-term family '(set))
     (q190391-apply-term 'set (list (q190391-quoted x)))))))

(defun q190391-union-member-p (family x)
  (q190391-exists-p
   (q190391-union-member-function family x)
   '(set)))

(defun q190391-union-set (carrier family)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term carrier '(x))
     (list 'q190391-union-member-p
           (q190391-quoted family) 'x)))))

(defun q190391-family-members-open-function (topology family)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term family '(set))
    (q190391-static-apply-term topology '(set)))))

(defun q190391-family-members-open-p (topology family)
  (and
   (tamep-functionp family)
   (q190391-universal-p
    (q190391-family-members-open-function topology family)
    '(set))))

(defun q190391-topology-intersection-function
    (carrier topology)
  (list
   'lambda '(left right)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term topology '(left))
      (q190391-static-apply-term topology '(right))))
    (q190391-static-apply-term
     topology
     (list
      (list 'lambda '(x)
            (q190391-and-terms
             (list
              (q190391-static-apply-term
               (q190391-quoted carrier) '(x))
              (q190391-apply-term 'left '(x))
              (q190391-apply-term 'right '(x))))))))))

(defun q190391-topology-union-function
    (carrier topology)
  (list
   'lambda '(family)
   (q190391-implies-term
    (list 'q190391-family-members-open-p
          (q190391-quoted topology) 'family)
    (q190391-static-apply-term
     topology
     (list
      (list 'q190391-union-set
            (q190391-quoted carrier) 'family))))))

(defun q190391-topological-space-p (carrier topology)
  (and
   (q190391-family-of-sets-p carrier topology)
   (q190391-member-p topology (q190391-empty-set))
   (q190391-member-p topology (q190391-full-set carrier))
   (q190391-universal-p
    (q190391-topology-intersection-function carrier topology)
    '(left right))
   (q190391-universal-p
    (q190391-topology-union-function carrier topology)
    '(family))))

(defun q190391-preimage-set
    (domain-carrier function target-set)
  (list
   'lambda '(x)
   (q190391-and-terms
    (list
     (q190391-static-apply-term domain-carrier '(x))
     (q190391-static-apply-term
      target-set
      (list (q190391-static-apply-term function '(x))))))))

(defun q190391-continuity-function
    (domain-carrier domain-topology target-topology function)
  (list
   'lambda '(open-set)
   (q190391-implies-term
    (q190391-static-apply-term target-topology '(open-set))
    (q190391-static-apply-term
     domain-topology
     (list
      (list 'q190391-preimage-set
            (q190391-quoted domain-carrier)
            (q190391-quoted function)
            'open-set))))))

(defun q190391-continuous-p
    (domain-carrier domain-topology
     target-carrier target-topology function)
  (and
   (q190391-function-p domain-carrier target-carrier function)
   (q190391-universal-p
    (q190391-continuity-function
     domain-carrier domain-topology target-topology function)
    '(open-set))))

(defun q190391-opens-measurable-function
    (topology measurable)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term topology '(set))
    (q190391-static-apply-term measurable '(set)))))

(defun q190391-opens-measurable-space-p
    (topology measurable)
  (q190391-universal-p
   (q190391-opens-measurable-function topology measurable)
   '(set)))

(defun q190391-topology-subset-sigma-function
    (topology sigma)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term topology '(set))
    (q190391-static-apply-term sigma '(set)))))

(defun q190391-topology-subset-sigma-p (topology sigma)
  (q190391-universal-p
   (q190391-topology-subset-sigma-function topology sigma)
   '(set)))

(defun q190391-borel-member-function
    (carrier topology set)
  (list
   'lambda '(sigma)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'q190391-sigma-algebra-p
            (q190391-quoted carrier) 'sigma)
      (list 'q190391-topology-subset-sigma-p
            (q190391-quoted topology) 'sigma)))
    (q190391-apply-term
     'sigma (list (q190391-quoted set))))))

(defun q190391-borel-member-p (carrier topology set)
  (and
   (q190391-valid-set-p carrier set)
   (q190391-universal-p
    (q190391-borel-member-function carrier topology set)
    '(sigma))))

(defun q190391-borel-space-function
    (carrier topology measurable)
  (list
   'lambda '(set)
   (q190391-implies-term
    (list 'q190391-valid-set-p
          (q190391-quoted carrier) 'set)
    (q190391-iff-term
     (q190391-static-apply-term measurable '(set))
     (list 'q190391-borel-member-p
           (q190391-quoted carrier)
           (q190391-quoted topology)
           'set)))))

(defun q190391-borel-space-p
    (carrier topology measurable)
  (and
   (q190391-sigma-algebra-p carrier measurable)
   (q190391-universal-p
    (q190391-borel-space-function
     carrier topology measurable)
    '(set))))

;; The exact order topology on the represented real field.

(defun q190391-open-interval-subset-function
    (real-carrier real-less lower upper set)
  (list
   'lambda '(y)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term real-carrier '(y))
      (q190391-static-apply-term
       real-less (list (q190391-quoted lower) 'y))
      (q190391-static-apply-term
       real-less (list 'y (q190391-quoted upper)))))
    (q190391-static-apply-term set '(y)))))

(defun q190391-open-interval-subset-p
    (real-carrier real-less lower upper set)
  (q190391-universal-p
   (q190391-open-interval-subset-function
    real-carrier real-less lower upper set)
   '(y)))

(defun q190391-order-neighborhood-witness-function
    (real-carrier real-less set x)
  (list
   'lambda '(bounds)
   (q190391-and-terms
    (list
     (list 'true-listp 'bounds)
     (list 'equal (list 'len 'bounds) '2)
     (q190391-static-apply-term
      real-carrier (list (list 'car 'bounds)))
     (q190391-static-apply-term
      real-carrier (list (list 'cadr 'bounds)))
     (q190391-static-apply-term
      real-less
      (list (list 'car 'bounds) (q190391-quoted x)))
     (q190391-static-apply-term
      real-less
      (list (q190391-quoted x) (list 'cadr 'bounds)))
     (list 'q190391-open-interval-subset-p
           (q190391-quoted real-carrier)
           (q190391-quoted real-less)
           (list 'car 'bounds)
           (list 'cadr 'bounds)
           (q190391-quoted set))))))

(defun q190391-order-neighborhood-p
    (real-carrier real-less set x)
  (q190391-exists-p
   (q190391-order-neighborhood-witness-function
    real-carrier real-less set x)
   '(bounds)))

(defun q190391-order-open-points-function
    (real-carrier real-less set)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term real-carrier '(x))
      (q190391-static-apply-term set '(x))))
    (list 'q190391-order-neighborhood-p
          (q190391-quoted real-carrier)
          (q190391-quoted real-less)
          (q190391-quoted set)
          'x))))

(defun q190391-order-open-p
    (real-carrier real-less set)
  (and
   (q190391-valid-set-p real-carrier set)
   (q190391-universal-p
    (q190391-order-open-points-function
     real-carrier real-less set)
    '(x))))

(defun q190391-order-topology-function
    (real-carrier real-less topology)
  (list
   'lambda '(set)
   (q190391-implies-term
    (list 'q190391-valid-set-p
          (q190391-quoted real-carrier) 'set)
    (q190391-iff-term
     (q190391-static-apply-term topology '(set))
     (list 'q190391-order-open-p
           (q190391-quoted real-carrier)
           (q190391-quoted real-less)
           'set)))))

(defun q190391-order-topology-p
    (real-carrier real-less topology)
  (and
   (q190391-topological-space-p real-carrier topology)
   (q190391-universal-p
    (q190391-order-topology-function
     real-carrier real-less topology)
    '(set))))

;; Arbitrary filters and scalar convergence along them.

(defun q190391-filter-upward-function
    (carrier filter)
  (list
   'lambda '(left right)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term filter '(left))
      (list 'q190391-valid-set-p
            (q190391-quoted carrier) 'right)
      (list 'q190391-set-subset-p
            (q190391-quoted carrier) 'left 'right)))
    (q190391-static-apply-term filter '(right)))))

(defun q190391-filter-intersection-function
    (carrier filter)
  (list
   'lambda '(left right)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term filter '(left))
      (q190391-static-apply-term filter '(right))))
    (q190391-static-apply-term
     filter
     (list
      (list 'lambda '(x)
            (q190391-and-terms
             (list
              (q190391-static-apply-term
               (q190391-quoted carrier) '(x))
              (q190391-apply-term 'left '(x))
              (q190391-apply-term 'right '(x))))))))))

(defun q190391-filter-p (carrier filter)
  (and
   (q190391-family-of-sets-p carrier filter)
   (q190391-member-p filter (q190391-full-set carrier))
   (q190391-universal-p
    (q190391-filter-upward-function carrier filter)
    '(left right))
   (q190391-universal-p
    (q190391-filter-intersection-function carrier filter)
    '(left right))))

(defun q190391-real-ball-event-set
    (index-carrier real-zero real-add real-negate real-less
     values limit epsilon)
  (list
   'lambda '(i)
   (q190391-and-terms
    (list
     (q190391-static-apply-term index-carrier '(i))
     (q190391-static-apply-term
      real-less
      (list
       (list 'q190391-scalar-absolute-value
             (q190391-quoted real-less)
             (q190391-quoted real-zero)
             (q190391-quoted real-negate)
             (q190391-static-apply-term
              real-add
              (list
               (q190391-static-apply-term values '(i))
               (q190391-static-apply-term
                real-negate
                (list (q190391-quoted limit))))))
       (q190391-quoted epsilon)))))))

(defun q190391-real-tendsto-filter-function
    (index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
  (list
   'lambda '(epsilon)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (q190391-static-apply-term real-carrier '(epsilon))
      (q190391-static-apply-term
       real-less
       (list (q190391-quoted real-zero) 'epsilon))))
    (q190391-static-apply-term
     filter
     (list
      (list 'q190391-real-ball-event-set
            (q190391-quoted index-carrier)
            (q190391-quoted real-zero)
            (q190391-quoted real-add)
            (q190391-quoted real-negate)
            (q190391-quoted real-less)
            (q190391-quoted values)
            (q190391-quoted limit)
            'epsilon))))))

(defun q190391-real-tendsto-filter-p
    (index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
  (and
   (q190391-function-p index-carrier real-carrier values)
   (q190391-member-p real-carrier limit)
   (q190391-universal-p
    (q190391-real-tendsto-filter-function
     index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
    '(epsilon))))

;; Generic measurability and almost-everywhere measurability.

(defun q190391-generic-measurability-function
    (domain-carrier domain-measurable
     target-measurable function)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term target-measurable '(set))
    (q190391-static-apply-term
     domain-measurable
     (list
      (list 'q190391-preimage-set
            (q190391-quoted domain-carrier)
            (q190391-quoted function)
            'set))))))

(defun q190391-generic-measurable-function-p
    (domain-carrier domain-measurable
     target-carrier target-measurable function)
  (and
   (q190391-function-p domain-carrier target-carrier function)
   (q190391-universal-p
    (q190391-generic-measurability-function
     domain-carrier domain-measurable target-measurable function)
    '(set))))

(defun q190391-generic-ae-measurable-witness-function
    (real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
  (list
   'lambda '(representative)
   (q190391-and-terms
    (list
     (list 'q190391-generic-measurable-function-p
           (q190391-quoted domain-carrier)
           (q190391-quoted domain-measurable)
           (q190391-quoted target-carrier)
           (q190391-quoted target-measurable)
           'representative)
     (list 'q190391-ae-equal-p
           (q190391-quoted real-zero)
           (q190391-quoted domain-carrier)
           (q190391-quoted measure)
           (q190391-quoted target-carrier)
           (q190391-quoted function)
           'representative)))))

(defun q190391-generic-ae-measurable-p
    (real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
  (and
   (q190391-function-p domain-carrier target-carrier function)
   (q190391-exists-p
    (q190391-generic-ae-measurable-witness-function
     real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
    '(representative))))

;; Dependent source spaces and probability measures.

(defun q190391-fiber-carrier (omega-carrier i)
  (list
   'lambda '(x)
   (q190391-static-apply-term
    omega-carrier
    (list (q190391-quoted i) 'x))))

(defun q190391-fiber-measurable (omega-measurable i)
  (list
   'lambda '(set)
   (q190391-static-apply-term
    omega-measurable
    (list (q190391-quoted i) 'set))))

(defun q190391-fiber-measure (mu i)
  (list
   'lambda '(set)
   (q190391-static-apply-term
    mu
    (list (q190391-quoted i) 'set))))

(defun q190391-fiber-random-variable (x-family i)
  (list
   'lambda '(x)
   (q190391-static-apply-term
    x-family
    (list (q190391-quoted i) 'x))))

(defun q190391-probability-measure-p
    (real-carrier real-zero real-one real-add real-less
     carrier measurable measure)
  (and
   (q190391-measure-space-p
    real-carrier real-zero real-add real-less
    carrier measurable measure)
   (equal
    (q190391-unary-value
     measure (q190391-full-set carrier))
    (q190391-ennreal-finite real-one))))

(defun q190391-source-measure-family-function
    (real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
  (list
   'lambda '(i)
   (q190391-implies-term
    (q190391-static-apply-term index-carrier '(i))
    (q190391-and-terms
     (list
      (list 'q190391-probability-measure-p
            (q190391-quoted real-carrier)
            (q190391-quoted real-zero)
            (q190391-quoted real-one)
            (q190391-quoted real-add)
            (q190391-quoted real-less)
            (list 'q190391-fiber-carrier
                  (q190391-quoted omega-carrier) 'i)
            (list 'q190391-fiber-measurable
                  (q190391-quoted omega-measurable) 'i)
            (list 'q190391-fiber-measure
                  (q190391-quoted mu) 'i))
      (list 'q190391-lintegral-operation-p
            (q190391-quoted real-carrier)
            (q190391-quoted real-zero)
            (q190391-quoted real-add)
            (q190391-quoted real-multiply)
            (q190391-quoted real-less)
            (list 'q190391-fiber-carrier
                  (q190391-quoted omega-carrier) 'i)
            (list 'q190391-fiber-measurable
                  (q190391-quoted omega-measurable) 'i)
            (list 'q190391-fiber-measure
                  (q190391-quoted mu) 'i)
            (q190391-quoted lintegral)))))))

(defun q190391-source-measure-family-p
    (real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
  (and
   (tamep-functionp omega-carrier)
   (tamep-functionp omega-measurable)
   (tamep-functionp mu)
   (tamep-functionp lintegral)
   (q190391-universal-p
    (q190391-source-measure-family-function
     real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
    '(i))))

(defun q190391-family-ae-measurable-function
    (real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
  (list
   'lambda '(i)
   (q190391-implies-term
    (q190391-static-apply-term index-carrier '(i))
    (list 'q190391-generic-ae-measurable-p
          (q190391-quoted real-zero)
          (list 'q190391-fiber-carrier
                (q190391-quoted omega-carrier) 'i)
          (list 'q190391-fiber-measurable
                (q190391-quoted omega-measurable) 'i)
          (list 'q190391-fiber-measure
                (q190391-quoted mu) 'i)
          (q190391-quoted target-carrier)
          (q190391-quoted target-measurable)
          (list 'q190391-fiber-random-variable
                (q190391-quoted x-family) 'i)))))

(defun q190391-family-ae-measurable-p
    (real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
  (and
   (tamep-functionp x-family)
   (q190391-universal-p
    (q190391-family-ae-measurable-function
     real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
    '(i))))

;; Bounded continuous test functions and their integrals.

(defun q190391-bound-function
    (domain-carrier real-zero real-negate real-less function bound)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term domain-carrier '(x))
    (q190391-not-term
     (q190391-static-apply-term
      real-less
      (list
       (q190391-quoted bound)
       (list 'q190391-scalar-absolute-value
             (q190391-quoted real-less)
             (q190391-quoted real-zero)
             (q190391-quoted real-negate)
             (q190391-static-apply-term function '(x)))))))))

(defun q190391-bound-witness-function
    (domain-carrier real-carrier real-zero real-negate real-less function)
  (list
   'lambda '(bound)
   (q190391-and-terms
    (list
     (q190391-static-apply-term real-carrier '(bound))
     (q190391-not-term
      (q190391-static-apply-term
       real-less
       (list 'bound (q190391-quoted real-zero))))
     (list 'q190391-universal-p
           (list 'q190391-bound-function
                 (q190391-quoted domain-carrier)
                 (q190391-quoted real-zero)
                 (q190391-quoted real-negate)
                 (q190391-quoted real-less)
                 (q190391-quoted function)
                 'bound)
           (q190391-quoted '(x)))))))

(defun q190391-bounded-continuous-p
    (domain-carrier domain-topology
     real-carrier real-topology real-zero real-negate real-less function)
  (and
   (q190391-continuous-p
    domain-carrier domain-topology
    real-carrier real-topology function)
   (q190391-exists-p
    (q190391-bound-witness-function
     domain-carrier real-carrier real-zero real-negate real-less function)
    '(bound))))

(defun q190391-compose (outer inner)
  (list
   'lambda '(x)
   (q190391-static-apply-term
    outer
    (list (q190391-static-apply-term inner '(x))))))

(defun q190391-compose-family (outer x-family)
  (list
   'lambda '(i x)
   (q190391-static-apply-term
    outer
    (list
     (q190391-static-apply-term x-family '(i x))))))

(defun q190391-test-integral-values
    (real-zero real-add real-negate real-less real-carrier
     omega-carrier omega-measurable mu lintegral x-family test)
  (list
   'lambda '(i)
   (list 'q190391-real-integral-value
         (q190391-quoted real-zero)
         (q190391-quoted real-add)
         (q190391-quoted real-negate)
         (q190391-quoted real-less)
         (list 'q190391-fiber-carrier
               (q190391-quoted omega-carrier) 'i)
         (list 'q190391-fiber-measurable
               (q190391-quoted omega-measurable) 'i)
         (list 'q190391-fiber-measure
               (q190391-quoted mu) 'i)
         (q190391-quoted real-carrier)
         (list 'q190391-compose
               (q190391-quoted test)
               (list 'q190391-fiber-random-variable
                     (q190391-quoted x-family) 'i))
         (q190391-quoted lintegral))))

(defun q190391-test-limit-integral
    (real-zero real-add real-negate real-less real-carrier
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function test)
  (q190391-real-integral-value
   real-zero real-add real-negate real-less
   limit-carrier limit-measurable limit-measure
   real-carrier
   (q190391-compose test limit-function)
   limit-lintegral))

(defun q190391-weak-convergence-test-function
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology)
  (list
   'lambda '(test)
   (q190391-implies-term
    (list 'q190391-bounded-continuous-p
          (q190391-quoted target-carrier)
          (q190391-quoted target-topology)
          (q190391-quoted real-carrier)
          (q190391-quoted real-topology)
          (q190391-quoted real-zero)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          'test)
    (list 'q190391-real-tendsto-filter-p
          (q190391-quoted index-carrier)
          (q190391-quoted filter)
          (q190391-quoted real-carrier)
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (list 'q190391-test-integral-values
                (q190391-quoted real-zero)
                (q190391-quoted real-add)
                (q190391-quoted real-negate)
                (q190391-quoted real-less)
                (q190391-quoted real-carrier)
                (q190391-quoted omega-carrier)
                (q190391-quoted omega-measurable)
                (q190391-quoted mu)
                (q190391-quoted lintegral)
                (q190391-quoted x-family)
                'test)
          (list 'q190391-test-limit-integral
                (q190391-quoted real-zero)
                (q190391-quoted real-add)
                (q190391-quoted real-negate)
                (q190391-quoted real-less)
                (q190391-quoted real-carrier)
                (q190391-quoted limit-carrier)
                (q190391-quoted limit-measurable)
                (q190391-quoted limit-measure)
                (q190391-quoted limit-lintegral)
                (q190391-quoted limit-function)
                'test)))))

(defun q190391-weak-convergence-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology)
  (q190391-universal-p
   (q190391-weak-convergence-test-function
    real-carrier real-zero real-add real-negate real-less real-topology
    index-carrier filter
    omega-carrier omega-measurable mu lintegral x-family
    limit-carrier limit-measurable limit-measure
    limit-lintegral limit-function
    target-carrier target-topology)
   '(test)))

(defun q190391-tendsto-in-distribution-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology target-measurable)
  (and
   (q190391-family-ae-measurable-p
    real-zero index-carrier omega-carrier omega-measurable mu
    target-carrier target-measurable x-family)
   (q190391-generic-ae-measurable-p
    real-zero limit-carrier limit-measurable limit-measure
    target-carrier target-measurable limit-function)
   (q190391-weak-convergence-p
    real-carrier real-zero real-add real-negate real-less real-topology
    index-carrier filter
    omega-carrier omega-measurable mu lintegral x-family
    limit-carrier limit-measurable limit-measure
    limit-lintegral limit-function
    target-carrier target-topology)))

;; Natural indices and the sequential filter.

(defun q190391-natural-carrier ()
  (list 'lambda '(n) (list 'natp 'n)))

(defun q190391-eventually-from-function (set start)
  (list
   'lambda '(n)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q190391-quoted start) 'n)))
    (q190391-static-apply-term set '(n)))))

(defun q190391-eventually-at-top-p (set)
  (and
   (tamep-functionp set)
   (q190391-exists-p
    (list
     'lambda '(start)
     (q190391-and-terms
      (list
       (list 'natp 'start)
       (list 'q190391-universal-p
             (list 'q190391-eventually-from-function
                   (q190391-quoted set) 'start)
             (q190391-quoted '(n))))))
    '(start))))

(defun q190391-sequential-filter ()
  (list
   'lambda '(set)
   (list 'q190391-eventually-at-top-p 'set)))

;; Exact real powers, factorials, and Taylor partial sums.

(defun q190391-real-nat-value (n real-zero real-one real-add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (q190391-binary-value
     real-add
     (q190391-real-nat-value
      (- n 1) real-zero real-one real-add)
     real-one)))

(defun q190391-real-power
    (value exponent real-one real-multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      real-one
    (q190391-binary-value
     real-multiply
     value
     (q190391-real-power
      value (- exponent 1) real-one real-multiply))))

(defun q190391-real-factorial
    (n real-zero real-one real-add real-multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-one
    (q190391-binary-value
     real-multiply
     (q190391-real-nat-value n real-zero real-one real-add)
     (q190391-real-factorial
      (- n 1)
      real-zero real-one real-add real-multiply))))

(defun q190391-real-divide
    (numerator denominator real-multiply real-inverse)
  (q190391-binary-value
   real-multiply
   numerator
   (q190391-unary-value real-inverse denominator)))

(defun q190391-alternating-value (k value real-negate)
  (if (equal (mod (nfix k) 2) 0)
      value
    (q190391-unary-value real-negate value)))

(defun q190391-exp-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (term
            (q190391-real-divide
             (q190391-real-power x k real-one real-multiply)
             (q190391-real-factorial
              k real-zero real-one real-add real-multiply)
             real-multiply real-inverse)))
      (q190391-binary-value
       real-add
       (q190391-exp-partial-sum
        k x
        real-zero real-one real-add real-multiply real-inverse)
       term))))

(defun q190391-cos-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-negate real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (exponent (* 2 k))
           (unsigned
            (q190391-real-divide
             (q190391-real-power
              x exponent real-one real-multiply)
             (q190391-real-factorial
              exponent real-zero real-one real-add real-multiply)
             real-multiply real-inverse))
           (term
            (q190391-alternating-value k unsigned real-negate)))
      (q190391-binary-value
       real-add
       (q190391-cos-partial-sum
        k x
        real-zero real-one real-add real-multiply
        real-negate real-inverse)
       term))))

(defun q190391-sin-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-negate real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (exponent (+ 1 (* 2 k)))
           (unsigned
            (q190391-real-divide
             (q190391-real-power
              x exponent real-one real-multiply)
             (q190391-real-factorial
              exponent real-zero real-one real-add real-multiply)
             real-multiply real-inverse))
           (term
            (q190391-alternating-value k unsigned real-negate)))
      (q190391-binary-value
       real-add
       (q190391-sin-partial-sum
        k x
        real-zero real-one real-add real-multiply
        real-negate real-inverse)
       term))))

(defun q190391-exp-partial-sum-sequence
    (x real-zero real-one real-add real-multiply real-inverse)
  (list
   'lambda '(n)
   (list
    'q190391-exp-partial-sum
    'n
    (q190391-quoted x)
    (q190391-quoted real-zero)
    (q190391-quoted real-one)
    (q190391-quoted real-add)
    (q190391-quoted real-multiply)
    (q190391-quoted real-inverse))))

(defun q190391-cos-partial-sum-sequence
    (x real-zero real-one real-add real-multiply
       real-negate real-inverse)
  (list
   'lambda '(n)
   (list
    'q190391-cos-partial-sum
    'n
    (q190391-quoted x)
    (q190391-quoted real-zero)
    (q190391-quoted real-one)
    (q190391-quoted real-add)
    (q190391-quoted real-multiply)
    (q190391-quoted real-negate)
    (q190391-quoted real-inverse))))

(defun q190391-sin-partial-sum-sequence
    (x real-zero real-one real-add real-multiply
       real-negate real-inverse)
  (list
   'lambda '(n)
   (list
    'q190391-sin-partial-sum
    'n
    (q190391-quoted x)
    (q190391-quoted real-zero)
    (q190391-quoted real-one)
    (q190391-quoted real-add)
    (q190391-quoted real-multiply)
    (q190391-quoted real-negate)
    (q190391-quoted real-inverse))))

(defun q190391-exp-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term real-carrier '(x))
    (list
     'q190391-real-tendsto-filter-p
     (list 'q190391-natural-carrier)
     (list 'q190391-sequential-filter)
     (q190391-quoted real-carrier)
     (q190391-quoted real-zero)
     (q190391-quoted real-add)
     (q190391-quoted real-negate)
     (q190391-quoted real-less)
     (list
      'q190391-exp-partial-sum-sequence
      'x
      (q190391-quoted real-zero)
      (q190391-quoted real-one)
      (q190391-quoted real-add)
      (q190391-quoted real-multiply)
      (q190391-quoted real-inverse))
     (q190391-static-apply-term exp '(x))))))

(defun q190391-cos-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term real-carrier '(x))
    (list
     'q190391-real-tendsto-filter-p
     (list 'q190391-natural-carrier)
     (list 'q190391-sequential-filter)
     (q190391-quoted real-carrier)
     (q190391-quoted real-zero)
     (q190391-quoted real-add)
     (q190391-quoted real-negate)
     (q190391-quoted real-less)
     (list
      'q190391-cos-partial-sum-sequence
      'x
      (q190391-quoted real-zero)
      (q190391-quoted real-one)
      (q190391-quoted real-add)
      (q190391-quoted real-multiply)
      (q190391-quoted real-negate)
      (q190391-quoted real-inverse))
     (q190391-static-apply-term cos '(x))))))

(defun q190391-sin-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term real-carrier '(x))
    (list
     'q190391-real-tendsto-filter-p
     (list 'q190391-natural-carrier)
     (list 'q190391-sequential-filter)
     (q190391-quoted real-carrier)
     (q190391-quoted real-zero)
     (q190391-quoted real-add)
     (q190391-quoted real-negate)
     (q190391-quoted real-less)
     (list
      'q190391-sin-partial-sum-sequence
      'x
      (q190391-quoted real-zero)
      (q190391-quoted real-one)
      (q190391-quoted real-add)
      (q190391-quoted real-multiply)
      (q190391-quoted real-negate)
      (q190391-quoted real-inverse))
     (q190391-static-apply-term sin '(x))))))

(defun q190391-analytic-functions-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp sin cos)
  (and
   (q190391-function-p real-carrier real-carrier exp)
   (q190391-function-p real-carrier real-carrier sin)
   (q190391-function-p real-carrier real-carrier cos)
   (q190391-universal-p
    (q190391-exp-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp)
    '(x))
   (q190391-universal-p
    (q190391-sin-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
    '(x))
   (q190391-universal-p
    (q190391-cos-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
    '(x))))

;; The total square-root operation agrees with the nonnegative root on
;; nonnegative inputs and is zero on negative inputs.

(defun q190391-square-root-laws-function
    (real-carrier real-zero real-multiply real-less square-root)
  (list
   'lambda '(x)
   (q190391-implies-term
    (q190391-static-apply-term real-carrier '(x))
    (let ((root (q190391-static-apply-term square-root '(x))))
      (q190391-and-terms
       (list
        (q190391-implies-term
         (q190391-static-apply-term
          real-less
          (list 'x (q190391-quoted real-zero)))
         (list 'equal root (q190391-quoted real-zero)))
        (q190391-implies-term
         (q190391-not-term
          (q190391-static-apply-term
           real-less
           (list 'x (q190391-quoted real-zero))))
         (q190391-and-terms
          (list
           (q190391-not-term
            (q190391-static-apply-term
             real-less
             (list root (q190391-quoted real-zero))))
           (list 'equal
                 (q190391-static-apply-term
                  real-multiply (list root root))
                 'x))))))))))

(defun q190391-square-root-operation-p
    (real-carrier real-zero real-multiply real-less square-root)
  (and
   (q190391-function-p real-carrier real-carrier square-root)
   (q190391-universal-p
    (q190391-square-root-laws-function
     real-carrier real-zero real-multiply real-less square-root)
    '(x))))

;; Real random-variable families and their laws.

(defun q190391-random-variable-family-function
    (sample-carrier sample-measurable
     real-carrier real-borel x-family)
  (list
   'lambda '(n)
   (q190391-implies-term
    (list 'natp 'n)
    (list
     'q190391-generic-measurable-function-p
     (q190391-quoted sample-carrier)
     (q190391-quoted sample-measurable)
     (q190391-quoted real-carrier)
     (q190391-quoted real-borel)
     (list
      'q190391-fiber-random-variable
      (q190391-quoted x-family)
      'n)))))

(defun q190391-random-variable-family-p
    (sample-carrier sample-measurable
     real-carrier real-borel x-family)
  (and
   (tamep-functionp x-family)
   (q190391-universal-p
    (q190391-random-variable-family-function
     sample-carrier sample-measurable
     real-carrier real-borel x-family)
    '(n))))

(defun q190391-distribution-equality-function
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure random-variable)
  (declare (ignore sample-measurable real-carrier))
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term real-borel '(set))
    (list
     'equal
     (q190391-static-apply-term
      sample-measure
      (list
       (list
        'q190391-preimage-set
        (q190391-quoted sample-carrier)
        (q190391-quoted random-variable)
        'set)))
     (q190391-static-apply-term target-measure '(set))))))

(defun q190391-distribution-equal-p
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure random-variable)
  (and
   (q190391-generic-measurable-function-p
    sample-carrier sample-measurable
    real-carrier real-borel random-variable)
   (q190391-universal-p
    (q190391-distribution-equality-function
     sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure random-variable)
    '(set))))

(defun q190391-common-distribution-family-function
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure x-family)
  (list
   'lambda '(n)
   (q190391-implies-term
    (list 'natp 'n)
    (list
     'q190391-distribution-equal-p
     (q190391-quoted sample-carrier)
     (q190391-quoted sample-measurable)
     (q190391-quoted sample-measure)
     (q190391-quoted real-carrier)
     (q190391-quoted real-borel)
     (q190391-quoted target-measure)
     (list
      'q190391-fiber-random-variable
      (q190391-quoted x-family)
      'n)))))

(defun q190391-common-distribution-family-p
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure x-family)
  (q190391-universal-p
   (q190391-common-distribution-family-function
    sample-carrier sample-measurable sample-measure
    real-carrier real-borel target-measure x-family)
   '(n)))

(defun q190391-natural-list-p (indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (q190391-natural-list-p (cdr indices)))
    (equal indices nil)))

(defun q190391-measurable-set-list-p (sets real-borel)
  (if (consp sets)
      (and
       (tamep-functionp (car sets))
       (q190391-member-p real-borel (car sets))
       (q190391-measurable-set-list-p (cdr sets) real-borel))
    (equal sets nil)))

(defun q190391-joint-event-set
    (sample-carrier x-family indices sets)
  (if (and (consp indices) (consp sets))
      (let ((tail
             (q190391-joint-event-set
              sample-carrier x-family
              (cdr indices) (cdr sets))))
        (list
         'lambda '(x)
         (q190391-and-terms
          (list
           (q190391-static-apply-term sample-carrier '(x))
           (q190391-static-apply-term
            (car sets)
            (list
             (q190391-static-apply-term
              x-family
              (list
               (q190391-quoted (car indices))
               'x))))
           (q190391-static-apply-term tail '(x))))))
    (q190391-full-set sample-carrier)))

(defun q190391-marginal-event-set
    (sample-carrier x-family index set)
  (q190391-preimage-set
   sample-carrier
   (q190391-fiber-random-variable x-family index)
   set))

(defun q190391-marginal-product
    (sample-carrier sample-measure x-family indices sets
     real-zero real-one real-multiply)
  (if (and (consp indices) (consp sets))
      (q190391-ennreal-multiply
       (q190391-unary-value
        sample-measure
        (q190391-marginal-event-set
         sample-carrier x-family
         (car indices) (car sets)))
       (q190391-marginal-product
        sample-carrier sample-measure x-family
        (cdr indices) (cdr sets)
        real-zero real-one real-multiply)
       real-zero real-multiply)
    (q190391-ennreal-finite real-one)))

(defun q190391-finite-independence-p
    (sample-carrier sample-measure x-family indices sets
     real-zero real-one real-multiply)
  (equal
   (q190391-unary-value
    sample-measure
    (q190391-joint-event-set
     sample-carrier x-family indices sets))
   (q190391-marginal-product
    sample-carrier sample-measure x-family indices sets
    real-zero real-one real-multiply)))

(defun q190391-independence-function
    (sample-carrier sample-measure real-borel x-family
     real-zero real-one real-multiply)
  (list
   'lambda '(indices sets)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'true-listp 'indices)
      (list 'no-duplicatesp-equal 'indices)
      (list 'q190391-natural-list-p 'indices)
      (list 'true-listp 'sets)
      (list 'equal (list 'len 'indices) (list 'len 'sets))
      (list
       'q190391-measurable-set-list-p
       'sets
       (q190391-quoted real-borel))))
    (list
     'q190391-finite-independence-p
     (q190391-quoted sample-carrier)
     (q190391-quoted sample-measure)
     (q190391-quoted x-family)
     'indices
     'sets
     (q190391-quoted real-zero)
     (q190391-quoted real-one)
     (q190391-quoted real-multiply)))))

(defun q190391-independent-random-variables-p
    (sample-carrier sample-measure real-borel x-family
     real-zero real-one real-multiply)
  (q190391-universal-p
   (q190391-independence-function
    sample-carrier sample-measure real-borel x-family
    real-zero real-one real-multiply)
   '(indices sets)))

;; Expectations, square integrability, and variance.

(defun q190391-square-function (function real-multiply)
  (list
   'lambda '(x)
   (q190391-static-apply-term
    real-multiply
    (list
     (q190391-static-apply-term function '(x))
     (q190391-static-apply-term function '(x))))))

(defun q190391-centered-square-function
    (function mean real-add real-multiply real-negate)
  (let ((centered
         (q190391-static-apply-term
          real-add
          (list
           (q190391-static-apply-term function '(x))
           (q190391-static-apply-term
            real-negate
            (list (q190391-quoted mean)))))))
    (list
     'lambda '(x)
     (q190391-static-apply-term
      real-multiply
      (list centered centered)))))

(defun q190391-expectation-value
    (real-zero real-add real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier function lintegral)
  (q190391-real-integral-value
   real-zero real-add real-negate real-less
   sample-carrier sample-measurable sample-measure
   real-carrier function lintegral))

(defun q190391-variance-value
    (real-zero real-add real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier function lintegral)
  (let ((mean
         (q190391-expectation-value
          real-zero real-add real-negate real-less
          sample-carrier sample-measurable sample-measure
          real-carrier function lintegral)))
    (q190391-real-integral-value
     real-zero real-add real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier
     (q190391-centered-square-function
      function mean real-add real-multiply real-negate)
     lintegral)))

(defun q190391-moment-laws-function
    (real-zero real-add real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier x-family lintegral mean sigma)
  (list
   'lambda '(n)
   (q190391-implies-term
    (list 'natp 'n)
    (let ((xn
           (list
            'q190391-fiber-random-variable
            (q190391-quoted x-family)
            'n)))
      (q190391-and-terms
       (list
        (list
         'equal
         (list
          'q190391-expectation-value
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (q190391-quoted sample-carrier)
          (q190391-quoted sample-measurable)
          (q190391-quoted sample-measure)
          (q190391-quoted real-carrier)
          xn
          (q190391-quoted lintegral))
         (q190391-quoted mean))
        (list
         'q190391-integrable-p
         (q190391-quoted real-zero)
         (q190391-quoted real-negate)
         (q190391-quoted real-less)
         (q190391-quoted sample-carrier)
         (q190391-quoted sample-measurable)
         (q190391-quoted sample-measure)
         (q190391-quoted real-carrier)
         (list
          'q190391-square-function
          xn
          (q190391-quoted real-multiply))
         (q190391-quoted lintegral))
        (list
         'equal
         (list
          'q190391-variance-value
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-multiply)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (q190391-quoted sample-carrier)
          (q190391-quoted sample-measurable)
          (q190391-quoted sample-measure)
          (q190391-quoted real-carrier)
          xn
          (q190391-quoted lintegral))
         (q190391-static-apply-term
          real-multiply
          (list
           (q190391-quoted sigma)
           (q190391-quoted sigma))))))))))

(defun q190391-moment-laws-p
    (real-zero real-add real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier x-family lintegral mean sigma)
  (q190391-universal-p
   (q190391-moment-laws-function
    real-zero real-add real-multiply real-negate real-less
    sample-carrier sample-measurable sample-measure
    real-carrier x-family lintegral mean sigma)
   '(n)))

;; Partial sums, centering, and normalization.

(defun q190391-partial-sum-value
    (x-family n x real-zero real-add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (q190391-binary-value
     real-add
     (q190391-partial-sum-value
      x-family (- n 1) x real-zero real-add)
     (q190391-binary-value
      x-family (- n 1) x))))

(defun q190391-centered-partial-sum-value
    (x-family n x mean real-zero real-add real-negate)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (q190391-binary-value
     real-add
     (q190391-centered-partial-sum-value
      x-family (- n 1) x mean
      real-zero real-add real-negate)
     (q190391-binary-value
      real-add
      (q190391-binary-value x-family (- n 1) x)
      (q190391-unary-value real-negate mean)))))

(defun q190391-partial-sum-family
    (x-family real-zero real-add)
  (list
   'lambda '(n x)
   (list
    'q190391-partial-sum-value
    (q190391-quoted x-family)
    'n 'x
    (q190391-quoted real-zero)
    (q190391-quoted real-add))))

(defun q190391-partial-sum-family-equality-function
    (sample-carrier x-family s-family real-zero real-add)
  (list
   'lambda '(n x)
   (q190391-implies-term
    (q190391-and-terms
     (list
      (list 'natp 'n)
      (q190391-static-apply-term sample-carrier '(x))))
    (list
     'equal
     (q190391-static-apply-term s-family '(n x))
     (list
      'q190391-partial-sum-value
      (q190391-quoted x-family)
      'n 'x
      (q190391-quoted real-zero)
      (q190391-quoted real-add))))))

(defun q190391-partial-sum-family-p
    (sample-carrier x-family s-family real-zero real-add)
  (and
   (tamep-functionp s-family)
   (q190391-universal-p
    (q190391-partial-sum-family-equality-function
     sample-carrier x-family s-family real-zero real-add)
    '(n x))))

(defun q190391-normalized-value
    (sum-value n sigma
     real-zero real-one real-add real-multiply real-inverse square-root)
  (let* ((n-real
          (q190391-real-nat-value
           n real-zero real-one real-add))
         (sigma-square
          (q190391-binary-value real-multiply sigma sigma))
         (scale-square
          (q190391-binary-value real-multiply n-real sigma-square))
         (scale
          (q190391-unary-value square-root scale-square)))
    (q190391-binary-value
     real-multiply
     sum-value
     (q190391-unary-value real-inverse scale))))

(defun q190391-normalized-s-family
    (s-family sigma
     real-zero real-one real-add real-multiply real-inverse square-root)
  (list
   'lambda '(n x)
   (list
    'q190391-normalized-value
    (q190391-static-apply-term s-family '(n x))
    'n
    (q190391-quoted sigma)
    (q190391-quoted real-zero)
    (q190391-quoted real-one)
    (q190391-quoted real-add)
    (q190391-quoted real-multiply)
    (q190391-quoted real-inverse)
    (q190391-quoted square-root))))

(defun q190391-centered-normalized-x-family
    (x-family mean sigma
     real-zero real-one real-add real-multiply
     real-negate real-inverse square-root)
  (list
   'lambda '(n x)
   (list
    'q190391-normalized-value
    (list
     'q190391-centered-partial-sum-value
     (q190391-quoted x-family)
     'n 'x
     (q190391-quoted mean)
     (q190391-quoted real-zero)
     (q190391-quoted real-add)
     (q190391-quoted real-negate))
    'n
    (q190391-quoted sigma)
    (q190391-quoted real-zero)
    (q190391-quoted real-one)
    (q190391-quoted real-add)
    (q190391-quoted real-multiply)
    (q190391-quoted real-inverse)
    (q190391-quoted square-root))))

;; The standard normal law is characterized exactly by its characteristic
;; function: cosine integral exp(-t^2/2) and sine integral zero.

(defun q190391-characteristic-cos-function
    (t-value real-multiply cos)
  (list
   'lambda '(x)
   (q190391-static-apply-term
    cos
    (list
     (q190391-static-apply-term
      real-multiply
      (list (q190391-quoted t-value) 'x))))))

(defun q190391-characteristic-sin-function
    (t-value real-multiply sin)
  (list
   'lambda '(x)
   (q190391-static-apply-term
    sin
    (list
     (q190391-static-apply-term
      real-multiply
      (list (q190391-quoted t-value) 'x))))))

(defun q190391-standard-normal-characteristic-function
    (real-zero real-one real-add real-multiply real-negate
     real-inverse real-less real-carrier real-borel
     standard-normal-measure lintegral exp sin cos)
  (list
   'lambda '(t-value)
   (q190391-implies-term
    (q190391-static-apply-term real-carrier '(t-value))
    (let* ((two
            (q190391-real-nat-value
             2 real-zero real-one real-add))
           (t-square
            (q190391-static-apply-term
             real-multiply '(t-value t-value)))
           (minus-half-square
            (q190391-static-apply-term
             real-negate
             (list
              (q190391-static-apply-term
               real-multiply
               (list
                t-square
                (q190391-static-apply-term
                 real-inverse
                 (list (q190391-quoted two)))))))))
      (q190391-and-terms
       (list
        (list
         'equal
         (list
          'q190391-real-integral-value
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (q190391-quoted real-carrier)
          (q190391-quoted real-borel)
          (q190391-quoted standard-normal-measure)
          (q190391-quoted real-carrier)
          (list
           'q190391-characteristic-cos-function
           't-value
           (q190391-quoted real-multiply)
           (q190391-quoted cos))
          (q190391-quoted lintegral))
         (q190391-static-apply-term exp (list minus-half-square)))
        (list
         'equal
         (list
          'q190391-real-integral-value
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (q190391-quoted real-carrier)
          (q190391-quoted real-borel)
          (q190391-quoted standard-normal-measure)
          (q190391-quoted real-carrier)
          (list
           'q190391-characteristic-sin-function
           't-value
           (q190391-quoted real-multiply)
           (q190391-quoted sin))
          (q190391-quoted lintegral))
         (q190391-quoted real-zero))))))))

(defun q190391-standard-normal-distribution-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-borel
     standard-normal-measure lintegral exp sin cos)
  (and
   (q190391-probability-measure-p
    real-carrier real-zero real-one real-add real-less
    real-carrier real-borel standard-normal-measure)
   (q190391-lintegral-operation-p
    real-carrier real-zero real-add real-multiply real-less
    real-carrier real-borel standard-normal-measure lintegral)
   (q190391-universal-p
    (q190391-standard-normal-characteristic-function
     real-zero real-one real-add real-multiply real-negate
     real-inverse real-less real-carrier real-borel
     standard-normal-measure lintegral exp sin cos)
    '(t-value))))

;; Constant source-space families let the general weak-convergence definition
;; express weak convergence of the laws of random variables on one space.

(defun q190391-constant-source-carrier-family (sample-carrier)
  (list
   'lambda '(n x)
   (q190391-static-apply-term sample-carrier '(x))))

(defun q190391-constant-source-measurable-family (sample-measurable)
  (list
   'lambda '(n set)
   (q190391-static-apply-term sample-measurable '(set))))

(defun q190391-constant-source-measure-family (sample-measure)
  (list
   'lambda '(n set)
   (q190391-static-apply-term sample-measure '(set))))

(defun q190391-real-identity-function ()
  (list 'lambda '(x) 'x))

(defun q190391-weak-convergence-to-standard-normal-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     sample-carrier sample-measurable sample-measure lintegral
     normalized-family real-borel standard-normal-measure)
  (q190391-weak-convergence-p
   real-carrier real-zero real-add real-negate real-less real-topology
   (q190391-natural-carrier)
   (q190391-sequential-filter)
   (q190391-constant-source-carrier-family sample-carrier)
   (q190391-constant-source-measurable-family sample-measurable)
   (q190391-constant-source-measure-family sample-measure)
   lintegral
   normalized-family
   real-carrier
   real-borel
   standard-normal-measure
   lintegral
   (q190391-real-identity-function)
   real-carrier
   real-topology))

;; Almost-everywhere pushforward laws.  Equality on all Borel sets is exactly
;; equality of the corresponding image measures.

(defun q190391-map-equality-function
    (domain-carrier domain-measure real-borel
     left-function right-measure)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term real-borel '(set))
    (list
     'equal
     (q190391-static-apply-term
      domain-measure
      (list
       (list
        'q190391-preimage-set
        (q190391-quoted domain-carrier)
        (q190391-quoted left-function)
        'set)))
     (q190391-static-apply-term right-measure '(set))))))

(defun q190391-has-law-p
    (real-zero domain-carrier domain-measurable domain-measure
     real-carrier real-borel function law)
  (and
   (q190391-generic-ae-measurable-p
    real-zero domain-carrier domain-measurable domain-measure
    real-carrier real-borel function)
   (q190391-universal-p
    (q190391-map-equality-function
     domain-carrier domain-measure real-borel function law)
    '(set))))

(defun q190391-ident-distrib-function
    (domain-carrier domain-measure real-borel left right)
  (list
   'lambda '(set)
   (q190391-implies-term
    (q190391-static-apply-term real-borel '(set))
    (list
     'equal
     (q190391-static-apply-term
      domain-measure
      (list
       (list
        'q190391-preimage-set
        (q190391-quoted domain-carrier)
        (q190391-quoted left)
        'set)))
     (q190391-static-apply-term
      domain-measure
      (list
       (list
        'q190391-preimage-set
        (q190391-quoted domain-carrier)
        (q190391-quoted right)
        'set)))))))

(defun q190391-ident-distrib-p
    (real-zero domain-carrier domain-measurable domain-measure
     real-carrier real-borel left right)
  (and
   (q190391-generic-ae-measurable-p
    real-zero domain-carrier domain-measurable domain-measure
    real-carrier real-borel left)
   (q190391-generic-ae-measurable-p
    real-zero domain-carrier domain-measurable domain-measure
    real-carrier real-borel right)
   (q190391-universal-p
    (q190391-ident-distrib-function
     domain-carrier domain-measure real-borel left right)
    '(set))))

(defun q190391-identically-distributed-family-function
    (real-zero sample-carrier sample-measurable sample-measure
     real-carrier real-borel x-family)
  (list
   'lambda '(n)
   (q190391-implies-term
    (list 'natp 'n)
    (list
     'q190391-ident-distrib-p
     (q190391-quoted real-zero)
     (q190391-quoted sample-carrier)
     (q190391-quoted sample-measurable)
     (q190391-quoted sample-measure)
     (q190391-quoted real-carrier)
     (q190391-quoted real-borel)
     (list
      'q190391-fiber-random-variable
      (q190391-quoted x-family)
      'n)
     (list
      'q190391-fiber-random-variable
      (q190391-quoted x-family)
      '0)))))

(defun q190391-identically-distributed-family-p
    (real-zero sample-carrier sample-measurable sample-measure
     real-carrier real-borel x-family)
  (and
   (tamep-functionp x-family)
   (q190391-universal-p
    (q190391-identically-distributed-family-function
     real-zero sample-carrier sample-measurable sample-measure
     real-carrier real-borel x-family)
    '(n))))

;; For real-valued functions, MemLp at exponent two is equivalent to
;; almost-everywhere measurability together with integrability of the square.

(defun q190391-mem-lp-two-p
    (real-zero real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier function lintegral)
  (and
   (q190391-ae-measurable-p
    real-zero sample-carrier sample-measurable sample-measure
    real-carrier real-less function)
   (q190391-integrable-p
    real-zero real-negate real-less
    sample-carrier sample-measurable sample-measure
    real-carrier
    (q190391-square-function function real-multiply)
    lintegral)))

;; This is the real value underlying Real.toNNReal.  Variance is nonnegative
;; in the represented probability model, while the totalized definition also
;; matches Lean's behavior without adding a nonzero-variance assumption.

(defun q190391-to-nonnegative-real
    (real-zero real-less value)
  (if (q190391-binary-value real-less value real-zero)
      real-zero
    value))

(defun q190391-centered-gaussian-characteristic-function
    (variance
     real-zero real-one real-add real-multiply real-negate
     real-inverse real-less real-carrier real-borel
     gaussian-measure lintegral exp sin cos)
  (list
   'lambda '(t-value)
   (q190391-implies-term
    (q190391-static-apply-term real-carrier '(t-value))
    (let* ((two
            (q190391-real-nat-value
             2 real-zero real-one real-add))
           (nonnegative-variance
            (q190391-to-nonnegative-real
             real-zero real-less variance))
           (t-square
            (q190391-static-apply-term
             real-multiply '(t-value t-value)))
           (variance-times-square
            (q190391-static-apply-term
             real-multiply
             (list
              (q190391-quoted nonnegative-variance)
              t-square)))
           (minus-half-variance-square
            (q190391-static-apply-term
             real-negate
             (list
              (q190391-static-apply-term
               real-multiply
               (list
                variance-times-square
                (q190391-static-apply-term
                 real-inverse
                 (list (q190391-quoted two)))))))))
      (q190391-and-terms
       (list
        (list
         'equal
         (list
          'q190391-real-integral-value
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (q190391-quoted real-carrier)
          (q190391-quoted real-borel)
          (q190391-quoted gaussian-measure)
          (q190391-quoted real-carrier)
          (list
           'q190391-characteristic-cos-function
           't-value
           (q190391-quoted real-multiply)
           (q190391-quoted cos))
          (q190391-quoted lintegral))
         (q190391-static-apply-term
          exp (list minus-half-variance-square)))
        (list
         'equal
         (list
          'q190391-real-integral-value
          (q190391-quoted real-zero)
          (q190391-quoted real-add)
          (q190391-quoted real-negate)
          (q190391-quoted real-less)
          (q190391-quoted real-carrier)
          (q190391-quoted real-borel)
          (q190391-quoted gaussian-measure)
          (q190391-quoted real-carrier)
          (list
           'q190391-characteristic-sin-function
           't-value
           (q190391-quoted real-multiply)
           (q190391-quoted sin))
          (q190391-quoted lintegral))
         (q190391-quoted real-zero))))))))

(defun q190391-centered-gaussian-distribution-p
    (variance
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-borel
     gaussian-measure lintegral exp sin cos)
  (and
   (q190391-probability-measure-p
    real-carrier real-zero real-one real-add real-less
    real-carrier real-borel gaussian-measure)
   (q190391-lintegral-operation-p
    real-carrier real-zero real-add real-multiply real-less
    real-carrier real-borel gaussian-measure lintegral)
   (q190391-universal-p
    (q190391-centered-gaussian-characteristic-function
     variance
     real-zero real-one real-add real-multiply real-negate
     real-inverse real-less real-carrier real-borel
     gaussian-measure lintegral exp sin cos)
    '(t-value))))

;; The source sequence is exactly
;; n ↦ (sqrt n)^-1 * (sum_{k<n} X_k - n * E[X_0]).

(defun q190391-centered-sqrt-normalized-value
    (x-family n x mean
     real-zero real-one real-add real-multiply
     real-negate real-inverse square-root)
  (let* ((centered-sum
          (q190391-centered-partial-sum-value
           x-family n x mean real-zero real-add real-negate))
         (n-real
          (q190391-real-nat-value
           n real-zero real-one real-add))
         (scale
          (q190391-unary-value square-root n-real)))
    (q190391-binary-value
     real-multiply
     (q190391-unary-value real-inverse scale)
     centered-sum)))

(defun q190391-centered-sqrt-normalized-family
    (x-family mean
     real-zero real-one real-add real-multiply
     real-negate real-inverse square-root)
  (list
   'lambda '(n x)
   (list
    'q190391-centered-sqrt-normalized-value
    (q190391-quoted x-family)
    'n 'x
    (q190391-quoted mean)
    (q190391-quoted real-zero)
    (q190391-quoted real-one)
    (q190391-quoted real-add)
    (q190391-quoted real-multiply)
    (q190391-quoted real-negate)
    (q190391-quoted real-inverse)
    (q190391-quoted square-root))))

(defun q190391-canonical-context-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology real-borel exp sin cos square-root
     sample-carrier sample-measurable sample-measure
     limit-carrier limit-measurable limit-measure
     gaussian-measure lintegral x-family y)
  (let* ((x-zero
          (q190391-fiber-random-variable x-family 0))
         (variance
          (q190391-variance-value
           real-zero real-add real-multiply real-negate real-less
           sample-carrier sample-measurable sample-measure
           real-carrier x-zero lintegral)))
    (and
     (q190391-real-field-p
      real-carrier real-zero real-one real-add real-multiply
      real-negate real-inverse real-less real-supremum)
     (q190391-order-topology-p
      real-carrier real-less real-topology)
     (q190391-borel-space-p
      real-carrier real-topology real-borel)
     (q190391-filter-p
      (q190391-natural-carrier)
      (q190391-sequential-filter))
     (q190391-analytic-functions-p
      real-carrier real-zero real-one real-add real-multiply
      real-negate real-inverse real-less exp sin cos)
     (q190391-square-root-operation-p
      real-carrier real-zero real-multiply real-less square-root)
     (q190391-probability-measure-p
      real-carrier real-zero real-one real-add real-less
      sample-carrier sample-measurable sample-measure)
     (q190391-lintegral-operation-p
      real-carrier real-zero real-add real-multiply real-less
      sample-carrier sample-measurable sample-measure lintegral)
     (q190391-probability-measure-p
      real-carrier real-zero real-one real-add real-less
      limit-carrier limit-measurable limit-measure)
     (q190391-lintegral-operation-p
      real-carrier real-zero real-add real-multiply real-less
      limit-carrier limit-measurable limit-measure lintegral)
     (q190391-centered-gaussian-distribution-p
      variance
      real-carrier real-zero real-one real-add real-multiply
      real-negate real-inverse real-less real-borel
      gaussian-measure lintegral exp sin cos)
     (q190391-has-law-p
      real-zero limit-carrier limit-measurable limit-measure
      real-carrier real-borel y gaussian-measure)
     (q190391-mem-lp-two-p
      real-zero real-multiply real-negate real-less
      sample-carrier sample-measurable sample-measure
      real-carrier x-zero lintegral)
     (q190391-independent-random-variables-p
      sample-carrier sample-measure real-borel x-family
      real-zero real-one real-multiply)
     (q190391-identically-distributed-family-p
      real-zero sample-carrier sample-measurable sample-measure
      real-carrier real-borel x-family))))

(defun thousand-theorems-q190391-canonical-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology real-borel exp sin cos square-root
     sample-carrier sample-measurable sample-measure
     limit-carrier limit-measurable limit-measure
     gaussian-measure lintegral x-family y)
  (let* ((x-zero
          (q190391-fiber-random-variable x-family 0))
         (mean
          (q190391-expectation-value
           real-zero real-add real-negate real-less
           sample-carrier sample-measurable sample-measure
           real-carrier x-zero lintegral)))
    (implies
     (q190391-canonical-context-p
      real-carrier real-zero real-one real-add real-multiply
      real-negate real-inverse real-less real-supremum
      real-topology real-borel exp sin cos square-root
      sample-carrier sample-measurable sample-measure
      limit-carrier limit-measurable limit-measure
      gaussian-measure lintegral x-family y)
     (q190391-tendsto-in-distribution-p
      real-carrier real-zero real-add real-negate real-less real-topology
      (q190391-natural-carrier)
      (q190391-sequential-filter)
      (q190391-constant-source-carrier-family sample-carrier)
      (q190391-constant-source-measurable-family sample-measurable)
      (q190391-constant-source-measure-family sample-measure)
      lintegral
      (q190391-centered-sqrt-normalized-family
       x-family mean
       real-zero real-one real-add real-multiply
       real-negate real-inverse square-root)
      limit-carrier
      limit-measurable
      limit-measure
      lintegral
      y
      real-carrier
      real-topology
      real-borel))))

(value-triple :itpeval-statement-checked)
:q
