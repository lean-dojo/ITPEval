;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__047, "The Central Limit Theorem": independent,
;; identically distributed real random variables with positive finite
;; variance have normalized zero-mean or centered partial-sum laws converging
;; weakly to the standard normal distribution. This file contains no proof.

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

(defun ht047-quoted (object)
  (list 'quote object))

(defun ht047-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (ht047-term-list (cdr terms)))
    (ht047-quoted nil)))

(defun ht047-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (ht047-term-list arguments)))

(defun ht047-static-apply-term (function arguments)
  (ht047-apply-term
   (ht047-quoted function)
   arguments))

(defun ht047-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht047-and-terms (cdr terms))
            (ht047-quoted nil))
    (ht047-quoted t)))

(defun ht047-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht047-quoted t)
            (ht047-or-terms (cdr terms)))
    (ht047-quoted nil)))

(defun ht047-not-term (term)
  (list 'if term
        (ht047-quoted nil)
        (ht047-quoted t)))

(defun ht047-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (ht047-quoted t)))

(defun ht047-iff-term (left right)
  (list 'if left
        (list 'if right
              (ht047-quoted t)
              (ht047-quoted nil))
        (list 'if right
              (ht047-quoted nil)
              (ht047-quoted t))))

(defun ht047-true-function (formals)
  (list 'lambda formals (ht047-quoted t)))

(defun ht047-false-function (formals)
  (list 'lambda formals (ht047-quoted nil)))

(defun ht047-universal-p (function formals)
  (let ((always-true (ht047-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun ht047-exists-p (function formals)
  (let ((always-false (ht047-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun ht047-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht047-unary-value (function object)
  (apply$ function (list object)))

(defun ht047-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun ht047-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term carrier '(x))
      (ht047-static-apply-term left '(x))))
    (ht047-static-apply-term right '(x)))))

(defun ht047-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (ht047-universal-p
    (ht047-set-subset-function carrier left right)
    '(x))))

(defun ht047-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (ht047-set-subset-p carrier set carrier)))

(defun ht047-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term carrier '(x))
    (ht047-iff-term
     (ht047-static-apply-term left '(x))
     (ht047-static-apply-term right '(x))))))

(defun ht047-set-equiv-p (carrier left right)
  (and
   (ht047-valid-set-p carrier left)
   (ht047-valid-set-p carrier right)
   (ht047-universal-p
    (ht047-set-equiv-function carrier left right)
    '(x))))

(defun ht047-empty-set ()
  (list 'lambda '(x) (ht047-quoted nil)))

(defun ht047-full-set (carrier)
  (list 'lambda '(x)
        (ht047-static-apply-term carrier '(x))))

(defun ht047-complement-set (carrier set)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term carrier '(x))
     (ht047-not-term
      (ht047-static-apply-term set '(x)))))))

(defun ht047-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term domain-carrier '(x))
    (ht047-static-apply-term
     codomain-carrier
     (list (ht047-static-apply-term function '(x)))))))

(defun ht047-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (ht047-universal-p
    (ht047-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun ht047-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (ht047-static-apply-term add '(x y)))
         (yz-add (ht047-static-apply-term add '(y z)))
         (xy-mul (ht047-static-apply-term multiply '(x y)))
         (yz-mul (ht047-static-apply-term multiply '(y z)))
         (neg-x (ht047-static-apply-term negate '(x)))
         (inv-x (ht047-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (ht047-implies-term
      (ht047-and-terms
       (list
        (ht047-static-apply-term carrier '(x))
        (ht047-static-apply-term carrier '(y))
        (ht047-static-apply-term carrier '(z))))
      (ht047-and-terms
       (list
        (ht047-static-apply-term carrier (list xy-add))
        (ht047-static-apply-term carrier (list xy-mul))
        (ht047-static-apply-term carrier (list neg-x))
        (ht047-static-apply-term carrier (list inv-x))
        (list 'equal
              (ht047-static-apply-term add (list xy-add 'z))
              (ht047-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (ht047-static-apply-term add '(y x)))
        (list 'equal
              (ht047-static-apply-term
               add (list 'x (ht047-quoted zero)))
              'x)
        (list 'equal
              (ht047-static-apply-term add (list 'x neg-x))
              (ht047-quoted zero))
        (list 'equal
              (ht047-static-apply-term multiply (list xy-mul 'z))
              (ht047-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (ht047-static-apply-term multiply '(y x)))
        (list 'equal
              (ht047-static-apply-term
               multiply (list 'x (ht047-quoted one)))
              'x)
        (ht047-implies-term
         (list 'equal 'x (ht047-quoted zero))
         (list 'equal inv-x (ht047-quoted zero)))
        (ht047-implies-term
         (ht047-not-term
          (list 'equal 'x (ht047-quoted zero)))
         (list 'equal
               (ht047-static-apply-term
                multiply (list 'x inv-x))
               (ht047-quoted one)))
        (list 'equal
              (ht047-static-apply-term multiply (list 'x yz-add))
              (ht047-static-apply-term
               add
               (list
                (ht047-static-apply-term multiply '(x y))
                (ht047-static-apply-term multiply '(x z)))))))))))

(defun ht047-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (ht047-static-apply-term less '(x y)))
        (yx (ht047-static-apply-term less '(y x)))
        (yz (ht047-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (ht047-implies-term
      (ht047-and-terms
       (list
        (ht047-static-apply-term carrier '(x))
        (ht047-static-apply-term carrier '(y))
        (ht047-static-apply-term carrier '(z))))
      (ht047-and-terms
       (list
        (ht047-not-term
         (ht047-static-apply-term less '(x x)))
        (ht047-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (ht047-implies-term
         (ht047-and-terms (list xy yz))
         (ht047-static-apply-term less '(x z)))
        (ht047-implies-term
         xy
         (ht047-static-apply-term
          less
          (list
           (ht047-static-apply-term add '(x z))
           (ht047-static-apply-term add '(y z)))))
        (ht047-implies-term
         (ht047-and-terms
          (list
           (ht047-static-apply-term
            less (list (ht047-quoted zero) 'x))
           (ht047-static-apply-term
            less (list (ht047-quoted zero) 'y))))
         (ht047-static-apply-term
          less
          (list
           (ht047-quoted zero)
           (ht047-static-apply-term multiply '(x y)))))))))))

(defun ht047-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term carrier '(x))
      (ht047-static-apply-term set '(x))))
    (ht047-not-term
     (ht047-static-apply-term
      less (list (ht047-quoted upper) 'x))))))

(defun ht047-upper-bound-p
    (carrier less set upper)
  (and
   (ht047-member-p carrier upper)
   (ht047-valid-set-p carrier set)
   (ht047-universal-p
    (ht047-upper-bound-function carrier less set upper)
    '(x))))

(defun ht047-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term carrier '(x))
     (ht047-static-apply-term set '(x))))))

(defun ht047-set-nonempty-p (carrier set)
  (and
   (ht047-valid-set-p carrier set)
   (ht047-exists-p
    (ht047-set-nonempty-function carrier set)
    '(x))))

(defun ht047-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'ht047-upper-bound-p
         (ht047-quoted carrier)
         (ht047-quoted less)
         (ht047-quoted set)
         'upper)))

(defun ht047-bounded-above-p (carrier less set)
  (ht047-exists-p
   (ht047-bounded-above-function carrier less set)
   '(upper)))

(defun ht047-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (ht047-implies-term
    (list 'ht047-upper-bound-p
          (ht047-quoted carrier)
          (ht047-quoted less)
          (ht047-quoted set)
          'upper)
    (ht047-not-term
     (ht047-static-apply-term
      less (list 'upper (ht047-quoted supremum)))))))

(defun ht047-least-upper-bound-p
    (carrier less set supremum)
  (and
   (ht047-upper-bound-p carrier less set supremum)
   (ht047-universal-p
    (ht047-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun ht047-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-valid-set-p
            (ht047-quoted carrier) 'set)
      (list 'ht047-set-nonempty-p
            (ht047-quoted carrier) 'set)
      (list 'ht047-bounded-above-p
            (ht047-quoted carrier)
            (ht047-quoted less)
            'set)))
    (list 'ht047-least-upper-bound-p
          (ht047-quoted carrier)
          (ht047-quoted less)
          'set
          (ht047-static-apply-term
           supremum-operation '(set))))))

(defun ht047-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (ht047-member-p carrier zero)
   (ht047-member-p carrier one)
   (not (equal zero one))
   (ht047-universal-p
    (ht047-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (ht047-universal-p
    (ht047-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (ht047-universal-p
    (ht047-completeness-function
     carrier less supremum)
    '(set))
   (ht047-binary-value less zero one)))

(defun ht047-scalar-absolute-value
    (less zero negate value)
  (if (ht047-binary-value less value zero)
      (ht047-unary-value negate value)
    value))
;; Sigma algebras.

(defun ht047-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (ht047-implies-term
    (list 'ht047-set-equiv-p
          (ht047-quoted carrier)
          'left 'right)
    (ht047-iff-term
     (ht047-static-apply-term family '(left))
     (ht047-static-apply-term family '(right))))))

(defun ht047-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term family '(set))
    (list 'ht047-valid-set-p
          (ht047-quoted carrier)
          'set))))

(defun ht047-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (ht047-universal-p
    (ht047-family-extensional-function carrier family)
    '(left right))
   (ht047-universal-p
    (ht047-family-members-valid-function carrier family)
    '(set))))

(defun ht047-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (ht047-and-terms
    (list
     (list 'natp 'n)
     (ht047-apply-term
      (ht047-static-apply-term sequence '(n))
      (list (ht047-quoted x)))))))

(defun ht047-sequence-union-member-p (sequence x)
  (ht047-exists-p
   (ht047-sequence-union-member-function sequence x)
   '(n)))

(defun ht047-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term carrier '(x))
     (list 'ht047-sequence-union-member-p
           (ht047-quoted sequence)
           'x)))))

(defun ht047-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (ht047-implies-term
    (list 'natp 'n)
    (list 'ht047-valid-set-p
          (ht047-quoted carrier)
          (ht047-static-apply-term sequence '(n))))))

(defun ht047-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (ht047-universal-p
    (ht047-sequence-of-sets-function carrier sequence)
    '(n))))

(defun ht047-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (ht047-implies-term
    (list 'natp 'n)
    (ht047-static-apply-term
     family
     (list (ht047-static-apply-term sequence '(n)))))))

(defun ht047-sequence-members-family-p
    (carrier family sequence)
  (and
   (ht047-sequence-of-sets-p carrier sequence)
   (ht047-universal-p
    (ht047-sequence-members-family-function family sequence)
    '(n))))

(defun ht047-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term family '(set))
    (ht047-static-apply-term
     family
     (list
      (list 'ht047-complement-set
            (ht047-quoted carrier)
            'set))))))

(defun ht047-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (ht047-implies-term
    (list 'ht047-sequence-members-family-p
          (ht047-quoted carrier)
          (ht047-quoted family)
          'sequence)
    (ht047-static-apply-term
     family
     (list
      (list 'ht047-sequence-union-set
            (ht047-quoted carrier)
            'sequence))))))

(defun ht047-sigma-algebra-p (carrier family)
  (and
   (ht047-family-of-sets-p carrier family)
   (ht047-member-p family (ht047-empty-set))
   (ht047-universal-p
    (ht047-sigma-complement-function carrier family)
    '(set))
   (ht047-universal-p
    (ht047-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun ht047-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :ht047-top)
   (and
    (consp value)
    (equal (car value) :ht047-finite)
    (ht047-member-p scalar-carrier (cdr value))
    (not
     (ht047-binary-value scalar-less (cdr value) scalar-zero)))))

(defun ht047-ennreal-finite (value)
  (cons :ht047-finite value))

(defun ht047-ennreal-zero (scalar-zero)
  (ht047-ennreal-finite scalar-zero))

(defun ht047-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :ht047-top) nil)
   ((equal right :ht047-top) t)
   (t
    (ht047-binary-value scalar-less (cdr left) (cdr right)))))

(defun ht047-ennreal-less-equal-p (left right scalar-less)
  (not (ht047-ennreal-less-p right left scalar-less)))

(defun ht047-ennreal-add (left right scalar-add)
  (if (or (equal left :ht047-top)
          (equal right :ht047-top))
      :ht047-top
    (ht047-ennreal-finite
     (ht047-binary-value scalar-add (cdr left) (cdr right)))))

(defun ht047-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (ht047-ennreal-zero scalar-zero))
        (equal right (ht047-ennreal-zero scalar-zero)))
    (ht047-ennreal-zero scalar-zero))
   ((or (equal left :ht047-top)
        (equal right :ht047-top))
    :ht047-top)
   (t
    (ht047-ennreal-finite
     (ht047-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun ht047-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht047-ennreal-zero scalar-zero)
    (ht047-ennreal-add
     (ht047-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (ht047-unary-value sequence (- count 1))
     scalar-add)))

(defun ht047-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (ht047-implies-term
    (list 'natp 'count)
    (list 'ht047-ennreal-less-equal-p
          (list 'ht047-finite-ennreal-sum
                (ht047-quoted sequence)
                'count
                (ht047-quoted scalar-zero)
                (ht047-quoted scalar-add))
          (ht047-quoted total)
          (ht047-quoted scalar-less)))))

(defun ht047-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (ht047-universal-p
   (ht047-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun ht047-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-ennreal-p
            'bound
            (ht047-quoted scalar-carrier)
            (ht047-quoted scalar-zero)
            (ht047-quoted scalar-less))
      (list 'ht047-sum-upper-bound-p
            (ht047-quoted sequence)
            'bound
            (ht047-quoted scalar-zero)
            (ht047-quoted scalar-add)
            (ht047-quoted scalar-less))))
    (list 'ht047-ennreal-less-equal-p
          (ht047-quoted total)
          'bound
          (ht047-quoted scalar-less)))))

(defun ht047-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (ht047-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (ht047-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (ht047-universal-p
    (ht047-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun ht047-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (ht047-implies-term
    (list 'ht047-set-equiv-p
          (ht047-quoted carrier)
          'left 'right)
    (list 'equal
          (ht047-static-apply-term measure '(left))
          (ht047-static-apply-term measure '(right))))))

(defun ht047-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (ht047-implies-term
    (list 'ht047-valid-set-p
          (ht047-quoted carrier)
          'set)
    (list 'ht047-ennreal-p
          (ht047-static-apply-term measure '(set))
          (ht047-quoted scalar-carrier)
          (ht047-quoted scalar-zero)
          (ht047-quoted scalar-less)))))

(defun ht047-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (ht047-static-apply-term
    measure
    (list (ht047-static-apply-term sequence '(n))))))

(defun ht047-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term carrier '(x))
    (ht047-not-term
     (ht047-and-terms
      (list
       (ht047-static-apply-term left '(x))
       (ht047-static-apply-term right '(x))))))))

(defun ht047-disjoint-sets-p (carrier left right)
  (ht047-universal-p
   (ht047-disjoint-sets-function carrier left right)
   '(x)))

(defun ht047-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (ht047-not-term (list 'equal 'm 'n))))
    (list 'ht047-disjoint-sets-p
          (ht047-quoted carrier)
          (ht047-static-apply-term sequence '(m))
          (ht047-static-apply-term sequence '(n))))))

(defun ht047-pairwise-disjoint-p (carrier sequence)
  (ht047-universal-p
   (ht047-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun ht047-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-sequence-members-family-p
            (ht047-quoted carrier)
            (ht047-quoted measurable)
            'sequence)
      (list 'ht047-pairwise-disjoint-p
            (ht047-quoted carrier)
            'sequence)))
    (list 'ht047-countable-sum-p
          (list 'ht047-measure-sequence-values
                (ht047-quoted measure)
                'sequence)
          (ht047-static-apply-term
           measure
           (list
            (list 'ht047-sequence-union-set
                  (ht047-quoted carrier)
                  'sequence)))
          (ht047-quoted scalar-carrier)
          (ht047-quoted scalar-zero)
          (ht047-quoted scalar-add)
          (ht047-quoted scalar-less)))))

(defun ht047-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term measurable '(superset))
      (list 'ht047-set-subset-p
            (ht047-quoted carrier)
            (ht047-quoted set)
            'superset)))
    (list 'ht047-ennreal-less-equal-p
          (ht047-quoted lower)
          (ht047-static-apply-term measure '(superset))
          (ht047-quoted scalar-less)))))

(defun ht047-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (ht047-universal-p
   (ht047-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun ht047-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-ennreal-p
            'lower
            (ht047-quoted scalar-carrier)
            (ht047-quoted scalar-zero)
            (ht047-quoted scalar-less))
      (list 'ht047-measurable-superset-lower-bound-p
            (ht047-quoted carrier)
            (ht047-quoted measurable)
            (ht047-quoted measure)
            (ht047-quoted set)
            'lower
            (ht047-quoted scalar-less))))
    (list 'ht047-ennreal-less-equal-p
          'lower
          (ht047-static-apply-term
           measure (list (ht047-quoted set)))
          (ht047-quoted scalar-less)))))

(defun ht047-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (ht047-valid-set-p carrier set)
   (ht047-measurable-superset-lower-bound-p
    carrier measurable measure set
    (ht047-unary-value measure set)
    scalar-less)
   (ht047-universal-p
    (ht047-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun ht047-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (ht047-implies-term
    (list 'ht047-valid-set-p
          (ht047-quoted carrier)
          'set)
    (list 'ht047-outer-value-p
          (ht047-quoted scalar-carrier)
          (ht047-quoted scalar-zero)
          (ht047-quoted scalar-less)
          (ht047-quoted carrier)
          (ht047-quoted measurable)
          (ht047-quoted measure)
          'set))))

(defun ht047-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (ht047-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (ht047-universal-p
    (ht047-measure-extensional-function carrier measure)
    '(left right))
   (ht047-universal-p
    (ht047-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (equal
    (ht047-unary-value measure (ht047-empty-set))
    (ht047-ennreal-zero scalar-zero))
   (ht047-universal-p
    (ht047-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (ht047-universal-p
    (ht047-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; The extended-nonnegative-real carrier and order used by lower integrals.

(defun ht047-ennreal-carrier
    (scalar-carrier scalar-zero scalar-less)
  (list
   'lambda '(value)
   (list 'ht047-ennreal-p
         'value
         (ht047-quoted scalar-carrier)
         (ht047-quoted scalar-zero)
         (ht047-quoted scalar-less))))

(defun ht047-ennreal-less-function (scalar-less)
  (list
   'lambda '(left right)
   (list 'ht047-ennreal-less-p
         'left 'right
         (ht047-quoted scalar-less))))

(defun ht047-null-set-p
    (scalar-zero domain-carrier measure set)
  (and
   (ht047-valid-set-p domain-carrier set)
   (equal
    (ht047-unary-value measure set)
    (ht047-ennreal-zero scalar-zero))))

;; Equality almost everywhere.

(defun ht047-disagreement-set
    (domain-carrier left right)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term domain-carrier '(x))
     (ht047-not-term
      (list 'equal
            (ht047-static-apply-term left '(x))
            (ht047-static-apply-term right '(x))))))))

(defun ht047-ae-equal-p
    (scalar-zero domain-carrier measure codomain-carrier left right)
  (and
   (ht047-function-p domain-carrier codomain-carrier left)
   (ht047-function-p domain-carrier codomain-carrier right)
   (ht047-null-set-p
    scalar-zero domain-carrier measure
    (ht047-disagreement-set domain-carrier left right))))

;; Standard measurability is characterized by measurable upper-ray preimages.

(defun ht047-upper-ray-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term domain-carrier '(x))
     (ht047-static-apply-term
      less
      (list (ht047-quoted threshold)
            (ht047-static-apply-term function '(x))))))))

(defun ht047-measurable-upper-rays-function
    (domain-carrier measurable codomain-carrier less function)
  (list
   'lambda '(threshold)
   (ht047-implies-term
    (ht047-static-apply-term codomain-carrier '(threshold))
    (ht047-static-apply-term
     measurable
     (list
      (list 'ht047-upper-ray-preimage-set
            (ht047-quoted domain-carrier)
            (ht047-quoted function)
            (ht047-quoted less)
            'threshold))))))

(defun ht047-measurable-function-p
    (domain-carrier measurable codomain-carrier less function)
  (and
   (ht047-function-p domain-carrier codomain-carrier function)
   (ht047-universal-p
    (ht047-measurable-upper-rays-function
     domain-carrier measurable codomain-carrier less function)
    '(threshold))))

(defun ht047-ae-measurable-witness-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (list
   'lambda '(representative)
   (ht047-and-terms
    (list
     (list 'ht047-measurable-function-p
           (ht047-quoted domain-carrier)
           (ht047-quoted measurable)
           (ht047-quoted codomain-carrier)
           (ht047-quoted less)
           'representative)
     (list 'ht047-ae-equal-p
           (ht047-quoted scalar-zero)
           (ht047-quoted domain-carrier)
           (ht047-quoted measure)
           (ht047-quoted codomain-carrier)
           (ht047-quoted function)
           'representative)))))

(defun ht047-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (and
   (ht047-function-p domain-carrier codomain-carrier function)
   (ht047-exists-p
    (ht047-ae-measurable-witness-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
    '(representative))))

;; The lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple functions below the integrand.

(defun ht047-fiber-set (domain-carrier function value)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term domain-carrier '(x))
     (list 'equal
           (ht047-static-apply-term function '(x))
           (ht047-quoted value))))))

(defun ht047-values-in-carrier-p (carrier values)
  (if (consp values)
      (and
       (ht047-member-p carrier (car values))
       (ht047-values-in-carrier-p carrier (cdr values)))
    (equal values nil)))

(defun ht047-value-attained-function
    (domain-carrier function value)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term domain-carrier '(x))
     (list 'equal
           (ht047-static-apply-term function '(x))
           (ht047-quoted value))))))

(defun ht047-value-attained-p
    (domain-carrier function value)
  (ht047-exists-p
   (ht047-value-attained-function
    domain-carrier function value)
   '(x)))

(defun ht047-values-attained-p
    (domain-carrier function values)
  (if (consp values)
      (and
       (ht047-value-attained-p
        domain-carrier function (car values))
       (ht047-values-attained-p
        domain-carrier function (cdr values)))
    (equal values nil)))

(defun ht047-range-in-values-function
    (domain-carrier function values)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term domain-carrier '(x))
    (list 'member-equal
          (ht047-static-apply-term function '(x))
          (ht047-quoted values)))))

(defun ht047-simple-function-p
    (domain-carrier measurable codomain-carrier less function values)
  (and
   (ht047-measurable-function-p
    domain-carrier measurable codomain-carrier less function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (ht047-values-in-carrier-p codomain-carrier values)
   (ht047-values-attained-p domain-carrier function values)
   (ht047-universal-p
    (ht047-range-in-values-function
     domain-carrier function values)
    '(x))))

(defun ht047-finite-simple-integral
    (domain-carrier measure function values
     scalar-zero scalar-add scalar-multiply)
  (if (consp values)
      (ht047-ennreal-add
       (ht047-ennreal-multiply
        (car values)
        (ht047-unary-value
         measure
         (ht047-fiber-set
          domain-carrier function (car values)))
        scalar-zero scalar-multiply)
       (ht047-finite-simple-integral
        domain-carrier measure function (cdr values)
        scalar-zero scalar-add scalar-multiply)
       scalar-add)
    (ht047-ennreal-zero scalar-zero)))

(defun ht047-simple-below-function
    (domain-carrier simple function scalar-less)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term domain-carrier '(x))
    (list 'ht047-ennreal-less-equal-p
          (ht047-static-apply-term simple '(x))
          (ht047-static-apply-term function '(x))
          (ht047-quoted scalar-less)))))

(defun ht047-simple-below-p
    (domain-carrier simple function scalar-less)
  (ht047-universal-p
   (ht047-simple-below-function
    domain-carrier simple function scalar-less)
   '(x)))

(defun ht047-lintegral-upper-bound-function
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (list
   'lambda '(simple values)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-simple-function-p
            (ht047-quoted domain-carrier)
            (ht047-quoted measurable)
            (ht047-quoted ennreal-carrier)
            (ht047-quoted ennreal-less)
            'simple 'values)
      (list 'ht047-simple-below-p
            (ht047-quoted domain-carrier)
            'simple
            (ht047-quoted function)
            (ht047-quoted scalar-less))))
    (list 'ht047-ennreal-less-equal-p
          (list 'ht047-finite-simple-integral
                (ht047-quoted domain-carrier)
                (ht047-quoted measure)
                'simple 'values
                (ht047-quoted scalar-zero)
                (ht047-quoted scalar-add)
                (ht047-quoted scalar-multiply))
          (ht047-quoted bound)
          (ht047-quoted scalar-less)))))

(defun ht047-lintegral-upper-bound-p
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (ht047-universal-p
   (ht047-lintegral-upper-bound-function
    domain-carrier measurable measure ennreal-carrier ennreal-less
    function bound scalar-zero scalar-add scalar-multiply scalar-less)
   '(simple values)))

(defun ht047-lintegral-least-upper-bound-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     function value)
  (list
   'lambda '(bound)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-ennreal-p
            'bound
            (ht047-quoted scalar-carrier)
            (ht047-quoted scalar-zero)
            (ht047-quoted scalar-less))
      (list 'ht047-lintegral-upper-bound-p
            (ht047-quoted domain-carrier)
            (ht047-quoted measurable)
            (ht047-quoted measure)
            (ht047-quoted ennreal-carrier)
            (ht047-quoted ennreal-less)
            (ht047-quoted function)
            'bound
            (ht047-quoted scalar-zero)
            (ht047-quoted scalar-add)
            (ht047-quoted scalar-multiply)
            (ht047-quoted scalar-less))))
    (list 'ht047-ennreal-less-equal-p
          (ht047-quoted value)
          'bound
          (ht047-quoted scalar-less)))))

(defun ht047-lintegral-value-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function value)
  (let ((ennreal-carrier
         (ht047-ennreal-carrier
          scalar-carrier scalar-zero scalar-less))
        (ennreal-less
         (ht047-ennreal-less-function scalar-less)))
    (and
     (ht047-function-p
      domain-carrier ennreal-carrier function)
     (ht047-member-p ennreal-carrier value)
     (ht047-lintegral-upper-bound-p
      domain-carrier measurable measure ennreal-carrier ennreal-less
      function value scalar-zero scalar-add scalar-multiply scalar-less)
     (ht047-universal-p
      (ht047-lintegral-least-upper-bound-function
       scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
       domain-carrier measurable measure ennreal-carrier ennreal-less
       function value)
      '(bound)))))

(defun ht047-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (let ((ennreal-carrier
         (ht047-ennreal-carrier
          scalar-carrier scalar-zero scalar-less)))
    (list
     'lambda '(function)
     (ht047-implies-term
      (list 'ht047-function-p
            (ht047-quoted domain-carrier)
            (ht047-quoted ennreal-carrier)
            'function)
      (list 'ht047-lintegral-value-p
            (ht047-quoted scalar-carrier)
            (ht047-quoted scalar-zero)
            (ht047-quoted scalar-add)
            (ht047-quoted scalar-multiply)
            (ht047-quoted scalar-less)
            (ht047-quoted domain-carrier)
            (ht047-quoted measurable)
            (ht047-quoted measure)
            'function
            (ht047-static-apply-term
             lintegral
             (list
              (ht047-quoted domain-carrier)
              (ht047-quoted measurable)
              (ht047-quoted measure)
              'function)))))))

(defun ht047-lintegral-operation-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (and
   (tamep-functionp lintegral)
   (ht047-universal-p
    (ht047-lintegral-values-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    '(function))))

;; For real functions, AE strong measurability is the preceding AE
;; measurability because the real line is separable. Integrability and the
;; Bochner integral are then defined from the exact lower integral.

(defun ht047-real-enorm-function
    (real-zero real-negate real-less function)
  (list
   'lambda '(x)
   (list 'ht047-ennreal-finite
         (list 'ht047-scalar-absolute-value
               (ht047-quoted real-less)
               (ht047-quoted real-zero)
               (ht047-quoted real-negate)
               (ht047-static-apply-term function '(x))))))

(defun ht047-real-positive-part-function
    (real-zero real-less function)
  (list
   'lambda '(x)
   (list 'ht047-ennreal-finite
         (list 'if
               (ht047-static-apply-term
                real-less
                (list
                 (ht047-static-apply-term function '(x))
                 (ht047-quoted real-zero)))
               (ht047-quoted real-zero)
               (ht047-static-apply-term function '(x))))))

(defun ht047-real-negative-part-function
    (real-zero real-negate real-less function)
  (let ((negative-value
         (ht047-static-apply-term
          real-negate
          (list (ht047-static-apply-term function '(x))))))
    (list
     'lambda '(x)
     (list 'ht047-ennreal-finite
           (list 'if
                 (ht047-static-apply-term
                  real-less
                  (list negative-value
                        (ht047-quoted real-zero)))
                 (ht047-quoted real-zero)
                 negative-value)))))

(defun ht047-ennreal-to-real (value real-zero)
  (if (equal value :ht047-top)
      real-zero
    (if (and (consp value)
             (equal (car value) :ht047-finite))
        (cdr value)
      real-zero)))

(defun ht047-integrable-p
    (real-zero real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (and
   (ht047-ae-measurable-p
    real-zero domain-carrier measurable measure
    real-carrier real-less function)
   (ht047-ennreal-less-p
    (apply$
     lintegral
     (list
      domain-carrier measurable measure
      (ht047-real-enorm-function
       real-zero real-negate real-less function)))
    :ht047-top
    real-less)))

(defun ht047-real-integral-value
    (real-zero real-add real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (if
      (ht047-integrable-p
       real-zero real-negate real-less
       domain-carrier measurable measure real-carrier function lintegral)
      (ht047-binary-value
       real-add
       (ht047-ennreal-to-real
        (apply$
         lintegral
         (list
          domain-carrier measurable measure
          (ht047-real-positive-part-function
           real-zero real-less function)))
        real-zero)
       (ht047-unary-value
        real-negate
        (ht047-ennreal-to-real
         (apply$
          lintegral
          (list
           domain-carrier measurable measure
           (ht047-real-negative-part-function
            real-zero real-negate real-less function)))
         real-zero)))
    real-zero))

;; General topologies and continuous maps.

(defun ht047-union-member-function (family x)
  (list
   'lambda '(set)
   (ht047-and-terms
    (list
     (ht047-static-apply-term family '(set))
     (ht047-apply-term 'set (list (ht047-quoted x)))))))

(defun ht047-union-member-p (family x)
  (ht047-exists-p
   (ht047-union-member-function family x)
   '(set)))

(defun ht047-union-set (carrier family)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term carrier '(x))
     (list 'ht047-union-member-p
           (ht047-quoted family) 'x)))))

(defun ht047-family-members-open-function (topology family)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term family '(set))
    (ht047-static-apply-term topology '(set)))))

(defun ht047-family-members-open-p (topology family)
  (and
   (tamep-functionp family)
   (ht047-universal-p
    (ht047-family-members-open-function topology family)
    '(set))))

(defun ht047-topology-intersection-function
    (carrier topology)
  (list
   'lambda '(left right)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term topology '(left))
      (ht047-static-apply-term topology '(right))))
    (ht047-static-apply-term
     topology
     (list
      (list 'lambda '(x)
            (ht047-and-terms
             (list
              (ht047-static-apply-term
               (ht047-quoted carrier) '(x))
              (ht047-apply-term 'left '(x))
              (ht047-apply-term 'right '(x))))))))))

(defun ht047-topology-union-function
    (carrier topology)
  (list
   'lambda '(family)
   (ht047-implies-term
    (list 'ht047-family-members-open-p
          (ht047-quoted topology) 'family)
    (ht047-static-apply-term
     topology
     (list
      (list 'ht047-union-set
            (ht047-quoted carrier) 'family))))))

(defun ht047-topological-space-p (carrier topology)
  (and
   (ht047-family-of-sets-p carrier topology)
   (ht047-member-p topology (ht047-empty-set))
   (ht047-member-p topology (ht047-full-set carrier))
   (ht047-universal-p
    (ht047-topology-intersection-function carrier topology)
    '(left right))
   (ht047-universal-p
    (ht047-topology-union-function carrier topology)
    '(family))))

(defun ht047-preimage-set
    (domain-carrier function target-set)
  (list
   'lambda '(x)
   (ht047-and-terms
    (list
     (ht047-static-apply-term domain-carrier '(x))
     (ht047-static-apply-term
      target-set
      (list (ht047-static-apply-term function '(x))))))))

(defun ht047-continuity-function
    (domain-carrier domain-topology target-topology function)
  (list
   'lambda '(open-set)
   (ht047-implies-term
    (ht047-static-apply-term target-topology '(open-set))
    (ht047-static-apply-term
     domain-topology
     (list
      (list 'ht047-preimage-set
            (ht047-quoted domain-carrier)
            (ht047-quoted function)
            'open-set))))))

(defun ht047-continuous-p
    (domain-carrier domain-topology
     target-carrier target-topology function)
  (and
   (ht047-function-p domain-carrier target-carrier function)
   (ht047-universal-p
    (ht047-continuity-function
     domain-carrier domain-topology target-topology function)
    '(open-set))))

(defun ht047-opens-measurable-function
    (topology measurable)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term topology '(set))
    (ht047-static-apply-term measurable '(set)))))

(defun ht047-opens-measurable-space-p
    (topology measurable)
  (ht047-universal-p
   (ht047-opens-measurable-function topology measurable)
   '(set)))

(defun ht047-topology-subset-sigma-function
    (topology sigma)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term topology '(set))
    (ht047-static-apply-term sigma '(set)))))

(defun ht047-topology-subset-sigma-p (topology sigma)
  (ht047-universal-p
   (ht047-topology-subset-sigma-function topology sigma)
   '(set)))

(defun ht047-borel-member-function
    (carrier topology set)
  (list
   'lambda '(sigma)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'ht047-sigma-algebra-p
            (ht047-quoted carrier) 'sigma)
      (list 'ht047-topology-subset-sigma-p
            (ht047-quoted topology) 'sigma)))
    (ht047-apply-term
     'sigma (list (ht047-quoted set))))))

(defun ht047-borel-member-p (carrier topology set)
  (and
   (ht047-valid-set-p carrier set)
   (ht047-universal-p
    (ht047-borel-member-function carrier topology set)
    '(sigma))))

(defun ht047-borel-space-function
    (carrier topology measurable)
  (list
   'lambda '(set)
   (ht047-implies-term
    (list 'ht047-valid-set-p
          (ht047-quoted carrier) 'set)
    (ht047-iff-term
     (ht047-static-apply-term measurable '(set))
     (list 'ht047-borel-member-p
           (ht047-quoted carrier)
           (ht047-quoted topology)
           'set)))))

(defun ht047-borel-space-p
    (carrier topology measurable)
  (and
   (ht047-sigma-algebra-p carrier measurable)
   (ht047-universal-p
    (ht047-borel-space-function
     carrier topology measurable)
    '(set))))

;; The exact order topology on the represented real field.

(defun ht047-open-interval-subset-function
    (real-carrier real-less lower upper set)
  (list
   'lambda '(y)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term real-carrier '(y))
      (ht047-static-apply-term
       real-less (list (ht047-quoted lower) 'y))
      (ht047-static-apply-term
       real-less (list 'y (ht047-quoted upper)))))
    (ht047-static-apply-term set '(y)))))

(defun ht047-open-interval-subset-p
    (real-carrier real-less lower upper set)
  (ht047-universal-p
   (ht047-open-interval-subset-function
    real-carrier real-less lower upper set)
   '(y)))

(defun ht047-order-neighborhood-witness-function
    (real-carrier real-less set x)
  (list
   'lambda '(bounds)
   (ht047-and-terms
    (list
     (list 'true-listp 'bounds)
     (list 'equal (list 'len 'bounds) '2)
     (ht047-static-apply-term
      real-carrier (list (list 'car 'bounds)))
     (ht047-static-apply-term
      real-carrier (list (list 'cadr 'bounds)))
     (ht047-static-apply-term
      real-less
      (list (list 'car 'bounds) (ht047-quoted x)))
     (ht047-static-apply-term
      real-less
      (list (ht047-quoted x) (list 'cadr 'bounds)))
     (list 'ht047-open-interval-subset-p
           (ht047-quoted real-carrier)
           (ht047-quoted real-less)
           (list 'car 'bounds)
           (list 'cadr 'bounds)
           (ht047-quoted set))))))

(defun ht047-order-neighborhood-p
    (real-carrier real-less set x)
  (ht047-exists-p
   (ht047-order-neighborhood-witness-function
    real-carrier real-less set x)
   '(bounds)))

(defun ht047-order-open-points-function
    (real-carrier real-less set)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term real-carrier '(x))
      (ht047-static-apply-term set '(x))))
    (list 'ht047-order-neighborhood-p
          (ht047-quoted real-carrier)
          (ht047-quoted real-less)
          (ht047-quoted set)
          'x))))

(defun ht047-order-open-p
    (real-carrier real-less set)
  (and
   (ht047-valid-set-p real-carrier set)
   (ht047-universal-p
    (ht047-order-open-points-function
     real-carrier real-less set)
    '(x))))

(defun ht047-order-topology-function
    (real-carrier real-less topology)
  (list
   'lambda '(set)
   (ht047-implies-term
    (list 'ht047-valid-set-p
          (ht047-quoted real-carrier) 'set)
    (ht047-iff-term
     (ht047-static-apply-term topology '(set))
     (list 'ht047-order-open-p
           (ht047-quoted real-carrier)
           (ht047-quoted real-less)
           'set)))))

(defun ht047-order-topology-p
    (real-carrier real-less topology)
  (and
   (ht047-topological-space-p real-carrier topology)
   (ht047-universal-p
    (ht047-order-topology-function
     real-carrier real-less topology)
    '(set))))

;; Arbitrary filters and scalar convergence along them.

(defun ht047-filter-upward-function
    (carrier filter)
  (list
   'lambda '(left right)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term filter '(left))
      (list 'ht047-valid-set-p
            (ht047-quoted carrier) 'right)
      (list 'ht047-set-subset-p
            (ht047-quoted carrier) 'left 'right)))
    (ht047-static-apply-term filter '(right)))))

(defun ht047-filter-intersection-function
    (carrier filter)
  (list
   'lambda '(left right)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term filter '(left))
      (ht047-static-apply-term filter '(right))))
    (ht047-static-apply-term
     filter
     (list
      (list 'lambda '(x)
            (ht047-and-terms
             (list
              (ht047-static-apply-term
               (ht047-quoted carrier) '(x))
              (ht047-apply-term 'left '(x))
              (ht047-apply-term 'right '(x))))))))))

(defun ht047-filter-p (carrier filter)
  (and
   (ht047-family-of-sets-p carrier filter)
   (ht047-member-p filter (ht047-full-set carrier))
   (ht047-universal-p
    (ht047-filter-upward-function carrier filter)
    '(left right))
   (ht047-universal-p
    (ht047-filter-intersection-function carrier filter)
    '(left right))))

(defun ht047-real-ball-event-set
    (index-carrier real-zero real-add real-negate real-less
     values limit epsilon)
  (list
   'lambda '(i)
   (ht047-and-terms
    (list
     (ht047-static-apply-term index-carrier '(i))
     (ht047-static-apply-term
      real-less
      (list
       (list 'ht047-scalar-absolute-value
             (ht047-quoted real-less)
             (ht047-quoted real-zero)
             (ht047-quoted real-negate)
             (ht047-static-apply-term
              real-add
              (list
               (ht047-static-apply-term values '(i))
               (ht047-static-apply-term
                real-negate
                (list (ht047-quoted limit))))))
       (ht047-quoted epsilon)))))))

(defun ht047-real-tendsto-filter-function
    (index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
  (list
   'lambda '(epsilon)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (ht047-static-apply-term real-carrier '(epsilon))
      (ht047-static-apply-term
       real-less
       (list (ht047-quoted real-zero) 'epsilon))))
    (ht047-static-apply-term
     filter
     (list
      (list 'ht047-real-ball-event-set
            (ht047-quoted index-carrier)
            (ht047-quoted real-zero)
            (ht047-quoted real-add)
            (ht047-quoted real-negate)
            (ht047-quoted real-less)
            (ht047-quoted values)
            (ht047-quoted limit)
            'epsilon))))))

(defun ht047-real-tendsto-filter-p
    (index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
  (and
   (ht047-function-p index-carrier real-carrier values)
   (ht047-member-p real-carrier limit)
   (ht047-universal-p
    (ht047-real-tendsto-filter-function
     index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
    '(epsilon))))

;; Generic measurability and almost-everywhere measurability.

(defun ht047-generic-measurability-function
    (domain-carrier domain-measurable
     target-measurable function)
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term target-measurable '(set))
    (ht047-static-apply-term
     domain-measurable
     (list
      (list 'ht047-preimage-set
            (ht047-quoted domain-carrier)
            (ht047-quoted function)
            'set))))))

(defun ht047-generic-measurable-function-p
    (domain-carrier domain-measurable
     target-carrier target-measurable function)
  (and
   (ht047-function-p domain-carrier target-carrier function)
   (ht047-universal-p
    (ht047-generic-measurability-function
     domain-carrier domain-measurable target-measurable function)
    '(set))))

(defun ht047-generic-ae-measurable-witness-function
    (real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
  (list
   'lambda '(representative)
   (ht047-and-terms
    (list
     (list 'ht047-generic-measurable-function-p
           (ht047-quoted domain-carrier)
           (ht047-quoted domain-measurable)
           (ht047-quoted target-carrier)
           (ht047-quoted target-measurable)
           'representative)
     (list 'ht047-ae-equal-p
           (ht047-quoted real-zero)
           (ht047-quoted domain-carrier)
           (ht047-quoted measure)
           (ht047-quoted target-carrier)
           (ht047-quoted function)
           'representative)))))

(defun ht047-generic-ae-measurable-p
    (real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
  (and
   (ht047-function-p domain-carrier target-carrier function)
   (ht047-exists-p
    (ht047-generic-ae-measurable-witness-function
     real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
    '(representative))))

;; Dependent source spaces and probability measures.

(defun ht047-fiber-carrier (omega-carrier i)
  (list
   'lambda '(x)
   (ht047-static-apply-term
    omega-carrier
    (list (ht047-quoted i) 'x))))

(defun ht047-fiber-measurable (omega-measurable i)
  (list
   'lambda '(set)
   (ht047-static-apply-term
    omega-measurable
    (list (ht047-quoted i) 'set))))

(defun ht047-fiber-measure (mu i)
  (list
   'lambda '(set)
   (ht047-static-apply-term
    mu
    (list (ht047-quoted i) 'set))))

(defun ht047-fiber-random-variable (x-family i)
  (list
   'lambda '(x)
   (ht047-static-apply-term
    x-family
    (list (ht047-quoted i) 'x))))

(defun ht047-probability-measure-p
    (real-carrier real-zero real-one real-add real-less
     carrier measurable measure)
  (and
   (ht047-measure-space-p
    real-carrier real-zero real-add real-less
    carrier measurable measure)
   (equal
    (ht047-unary-value
     measure (ht047-full-set carrier))
    (ht047-ennreal-finite real-one))))

(defun ht047-source-measure-family-function
    (real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
  (list
   'lambda '(i)
   (ht047-implies-term
    (ht047-static-apply-term index-carrier '(i))
    (ht047-and-terms
     (list
      (list 'ht047-probability-measure-p
            (ht047-quoted real-carrier)
            (ht047-quoted real-zero)
            (ht047-quoted real-one)
            (ht047-quoted real-add)
            (ht047-quoted real-less)
            (list 'ht047-fiber-carrier
                  (ht047-quoted omega-carrier) 'i)
            (list 'ht047-fiber-measurable
                  (ht047-quoted omega-measurable) 'i)
            (list 'ht047-fiber-measure
                  (ht047-quoted mu) 'i))
      (list 'ht047-lintegral-operation-p
            (ht047-quoted real-carrier)
            (ht047-quoted real-zero)
            (ht047-quoted real-add)
            (ht047-quoted real-multiply)
            (ht047-quoted real-less)
            (list 'ht047-fiber-carrier
                  (ht047-quoted omega-carrier) 'i)
            (list 'ht047-fiber-measurable
                  (ht047-quoted omega-measurable) 'i)
            (list 'ht047-fiber-measure
                  (ht047-quoted mu) 'i)
            (ht047-quoted lintegral)))))))

(defun ht047-source-measure-family-p
    (real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
  (and
   (tamep-functionp omega-carrier)
   (tamep-functionp omega-measurable)
   (tamep-functionp mu)
   (tamep-functionp lintegral)
   (ht047-universal-p
    (ht047-source-measure-family-function
     real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
    '(i))))

(defun ht047-family-ae-measurable-function
    (real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
  (list
   'lambda '(i)
   (ht047-implies-term
    (ht047-static-apply-term index-carrier '(i))
    (list 'ht047-generic-ae-measurable-p
          (ht047-quoted real-zero)
          (list 'ht047-fiber-carrier
                (ht047-quoted omega-carrier) 'i)
          (list 'ht047-fiber-measurable
                (ht047-quoted omega-measurable) 'i)
          (list 'ht047-fiber-measure
                (ht047-quoted mu) 'i)
          (ht047-quoted target-carrier)
          (ht047-quoted target-measurable)
          (list 'ht047-fiber-random-variable
                (ht047-quoted x-family) 'i)))))

(defun ht047-family-ae-measurable-p
    (real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
  (and
   (tamep-functionp x-family)
   (ht047-universal-p
    (ht047-family-ae-measurable-function
     real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
    '(i))))

;; Bounded continuous test functions and their integrals.

(defun ht047-bound-function
    (domain-carrier real-zero real-negate real-less function bound)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term domain-carrier '(x))
    (ht047-not-term
     (ht047-static-apply-term
      real-less
      (list
       (ht047-quoted bound)
       (list 'ht047-scalar-absolute-value
             (ht047-quoted real-less)
             (ht047-quoted real-zero)
             (ht047-quoted real-negate)
             (ht047-static-apply-term function '(x)))))))))

(defun ht047-bound-witness-function
    (domain-carrier real-carrier real-zero real-negate real-less function)
  (list
   'lambda '(bound)
   (ht047-and-terms
    (list
     (ht047-static-apply-term real-carrier '(bound))
     (ht047-not-term
      (ht047-static-apply-term
       real-less
       (list 'bound (ht047-quoted real-zero))))
     (list 'ht047-universal-p
           (list 'ht047-bound-function
                 (ht047-quoted domain-carrier)
                 (ht047-quoted real-zero)
                 (ht047-quoted real-negate)
                 (ht047-quoted real-less)
                 (ht047-quoted function)
                 'bound)
           (ht047-quoted '(x)))))))

(defun ht047-bounded-continuous-p
    (domain-carrier domain-topology
     real-carrier real-topology real-zero real-negate real-less function)
  (and
   (ht047-continuous-p
    domain-carrier domain-topology
    real-carrier real-topology function)
   (ht047-exists-p
    (ht047-bound-witness-function
     domain-carrier real-carrier real-zero real-negate real-less function)
    '(bound))))

(defun ht047-compose (outer inner)
  (list
   'lambda '(x)
   (ht047-static-apply-term
    outer
    (list (ht047-static-apply-term inner '(x))))))

(defun ht047-compose-family (outer x-family)
  (list
   'lambda '(i x)
   (ht047-static-apply-term
    outer
    (list
     (ht047-static-apply-term x-family '(i x))))))

(defun ht047-test-integral-values
    (real-zero real-add real-negate real-less real-carrier
     omega-carrier omega-measurable mu lintegral x-family test)
  (list
   'lambda '(i)
   (list 'ht047-real-integral-value
         (ht047-quoted real-zero)
         (ht047-quoted real-add)
         (ht047-quoted real-negate)
         (ht047-quoted real-less)
         (list 'ht047-fiber-carrier
               (ht047-quoted omega-carrier) 'i)
         (list 'ht047-fiber-measurable
               (ht047-quoted omega-measurable) 'i)
         (list 'ht047-fiber-measure
               (ht047-quoted mu) 'i)
         (ht047-quoted real-carrier)
         (list 'ht047-compose
               (ht047-quoted test)
               (list 'ht047-fiber-random-variable
                     (ht047-quoted x-family) 'i))
         (ht047-quoted lintegral))))

(defun ht047-test-limit-integral
    (real-zero real-add real-negate real-less real-carrier
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function test)
  (ht047-real-integral-value
   real-zero real-add real-negate real-less
   limit-carrier limit-measurable limit-measure
   real-carrier
   (ht047-compose test limit-function)
   limit-lintegral))

(defun ht047-weak-convergence-test-function
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology)
  (list
   'lambda '(test)
   (ht047-implies-term
    (list 'ht047-bounded-continuous-p
          (ht047-quoted target-carrier)
          (ht047-quoted target-topology)
          (ht047-quoted real-carrier)
          (ht047-quoted real-topology)
          (ht047-quoted real-zero)
          (ht047-quoted real-negate)
          (ht047-quoted real-less)
          'test)
    (list 'ht047-real-tendsto-filter-p
          (ht047-quoted index-carrier)
          (ht047-quoted filter)
          (ht047-quoted real-carrier)
          (ht047-quoted real-zero)
          (ht047-quoted real-add)
          (ht047-quoted real-negate)
          (ht047-quoted real-less)
          (list 'ht047-test-integral-values
                (ht047-quoted real-zero)
                (ht047-quoted real-add)
                (ht047-quoted real-negate)
                (ht047-quoted real-less)
                (ht047-quoted real-carrier)
                (ht047-quoted omega-carrier)
                (ht047-quoted omega-measurable)
                (ht047-quoted mu)
                (ht047-quoted lintegral)
                (ht047-quoted x-family)
                'test)
          (list 'ht047-test-limit-integral
                (ht047-quoted real-zero)
                (ht047-quoted real-add)
                (ht047-quoted real-negate)
                (ht047-quoted real-less)
                (ht047-quoted real-carrier)
                (ht047-quoted limit-carrier)
                (ht047-quoted limit-measurable)
                (ht047-quoted limit-measure)
                (ht047-quoted limit-lintegral)
                (ht047-quoted limit-function)
                'test)))))

(defun ht047-weak-convergence-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology)
  (ht047-universal-p
   (ht047-weak-convergence-test-function
    real-carrier real-zero real-add real-negate real-less real-topology
    index-carrier filter
    omega-carrier omega-measurable mu lintegral x-family
    limit-carrier limit-measurable limit-measure
    limit-lintegral limit-function
    target-carrier target-topology)
   '(test)))

(defun ht047-tendsto-in-distribution-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology target-measurable)
  (and
   (ht047-family-ae-measurable-p
    real-zero index-carrier omega-carrier omega-measurable mu
    target-carrier target-measurable x-family)
   (ht047-generic-ae-measurable-p
    real-zero limit-carrier limit-measurable limit-measure
    target-carrier target-measurable limit-function)
   (ht047-weak-convergence-p
    real-carrier real-zero real-add real-negate real-less real-topology
    index-carrier filter
    omega-carrier omega-measurable mu lintegral x-family
    limit-carrier limit-measurable limit-measure
    limit-lintegral limit-function
    target-carrier target-topology)))

;; Natural indices and the sequential filter.

(defun ht047-natural-carrier ()
  (list 'lambda '(n) (list 'natp 'n)))

(defun ht047-eventually-from-function (set start)
  (list
   'lambda '(n)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'natp 'n)
      (list '<= (ht047-quoted start) 'n)))
    (ht047-static-apply-term set '(n)))))

(defun ht047-eventually-at-top-p (set)
  (and
   (tamep-functionp set)
   (ht047-exists-p
    (list
     'lambda '(start)
     (ht047-and-terms
      (list
       (list 'natp 'start)
       (list 'ht047-universal-p
             (list 'ht047-eventually-from-function
                   (ht047-quoted set) 'start)
             (ht047-quoted '(n))))))
    '(start))))

(defun ht047-sequential-filter ()
  (list
   'lambda '(set)
   (list 'ht047-eventually-at-top-p 'set)))

;; Exact real powers, factorials, and Taylor partial sums.

(defun ht047-real-nat-value (n real-zero real-one real-add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (ht047-binary-value
     real-add
     (ht047-real-nat-value
      (- n 1) real-zero real-one real-add)
     real-one)))

(defun ht047-real-power
    (value exponent real-one real-multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      real-one
    (ht047-binary-value
     real-multiply
     value
     (ht047-real-power
      value (- exponent 1) real-one real-multiply))))

(defun ht047-real-factorial
    (n real-zero real-one real-add real-multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-one
    (ht047-binary-value
     real-multiply
     (ht047-real-nat-value n real-zero real-one real-add)
     (ht047-real-factorial
      (- n 1)
      real-zero real-one real-add real-multiply))))

(defun ht047-real-divide
    (numerator denominator real-multiply real-inverse)
  (ht047-binary-value
   real-multiply
   numerator
   (ht047-unary-value real-inverse denominator)))

(defun ht047-alternating-value (k value real-negate)
  (if (equal (mod (nfix k) 2) 0)
      value
    (ht047-unary-value real-negate value)))

(defun ht047-exp-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (term
            (ht047-real-divide
             (ht047-real-power x k real-one real-multiply)
             (ht047-real-factorial
              k real-zero real-one real-add real-multiply)
             real-multiply real-inverse)))
      (ht047-binary-value
       real-add
       (ht047-exp-partial-sum
        k x
        real-zero real-one real-add real-multiply real-inverse)
       term))))

(defun ht047-cos-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-negate real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (exponent (* 2 k))
           (unsigned
            (ht047-real-divide
             (ht047-real-power
              x exponent real-one real-multiply)
             (ht047-real-factorial
              exponent real-zero real-one real-add real-multiply)
             real-multiply real-inverse))
           (term
            (ht047-alternating-value k unsigned real-negate)))
      (ht047-binary-value
       real-add
       (ht047-cos-partial-sum
        k x
        real-zero real-one real-add real-multiply
        real-negate real-inverse)
       term))))

(defun ht047-sin-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-negate real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (exponent (+ 1 (* 2 k)))
           (unsigned
            (ht047-real-divide
             (ht047-real-power
              x exponent real-one real-multiply)
             (ht047-real-factorial
              exponent real-zero real-one real-add real-multiply)
             real-multiply real-inverse))
           (term
            (ht047-alternating-value k unsigned real-negate)))
      (ht047-binary-value
       real-add
       (ht047-sin-partial-sum
        k x
        real-zero real-one real-add real-multiply
        real-negate real-inverse)
       term))))

(defun ht047-exp-partial-sum-sequence
    (x real-zero real-one real-add real-multiply real-inverse)
  (list
   'lambda '(n)
   (list
    'ht047-exp-partial-sum
    'n
    (ht047-quoted x)
    (ht047-quoted real-zero)
    (ht047-quoted real-one)
    (ht047-quoted real-add)
    (ht047-quoted real-multiply)
    (ht047-quoted real-inverse))))

(defun ht047-cos-partial-sum-sequence
    (x real-zero real-one real-add real-multiply
       real-negate real-inverse)
  (list
   'lambda '(n)
   (list
    'ht047-cos-partial-sum
    'n
    (ht047-quoted x)
    (ht047-quoted real-zero)
    (ht047-quoted real-one)
    (ht047-quoted real-add)
    (ht047-quoted real-multiply)
    (ht047-quoted real-negate)
    (ht047-quoted real-inverse))))

(defun ht047-sin-partial-sum-sequence
    (x real-zero real-one real-add real-multiply
       real-negate real-inverse)
  (list
   'lambda '(n)
   (list
    'ht047-sin-partial-sum
    'n
    (ht047-quoted x)
    (ht047-quoted real-zero)
    (ht047-quoted real-one)
    (ht047-quoted real-add)
    (ht047-quoted real-multiply)
    (ht047-quoted real-negate)
    (ht047-quoted real-inverse))))

(defun ht047-exp-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term real-carrier '(x))
    (list
     'ht047-real-tendsto-filter-p
     (list 'ht047-natural-carrier)
     (list 'ht047-sequential-filter)
     (ht047-quoted real-carrier)
     (ht047-quoted real-zero)
     (ht047-quoted real-add)
     (ht047-quoted real-negate)
     (ht047-quoted real-less)
     (list
      'ht047-exp-partial-sum-sequence
      'x
      (ht047-quoted real-zero)
      (ht047-quoted real-one)
      (ht047-quoted real-add)
      (ht047-quoted real-multiply)
      (ht047-quoted real-inverse))
     (ht047-static-apply-term exp '(x))))))

(defun ht047-cos-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term real-carrier '(x))
    (list
     'ht047-real-tendsto-filter-p
     (list 'ht047-natural-carrier)
     (list 'ht047-sequential-filter)
     (ht047-quoted real-carrier)
     (ht047-quoted real-zero)
     (ht047-quoted real-add)
     (ht047-quoted real-negate)
     (ht047-quoted real-less)
     (list
      'ht047-cos-partial-sum-sequence
      'x
      (ht047-quoted real-zero)
      (ht047-quoted real-one)
      (ht047-quoted real-add)
      (ht047-quoted real-multiply)
      (ht047-quoted real-negate)
      (ht047-quoted real-inverse))
     (ht047-static-apply-term cos '(x))))))

(defun ht047-sin-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term real-carrier '(x))
    (list
     'ht047-real-tendsto-filter-p
     (list 'ht047-natural-carrier)
     (list 'ht047-sequential-filter)
     (ht047-quoted real-carrier)
     (ht047-quoted real-zero)
     (ht047-quoted real-add)
     (ht047-quoted real-negate)
     (ht047-quoted real-less)
     (list
      'ht047-sin-partial-sum-sequence
      'x
      (ht047-quoted real-zero)
      (ht047-quoted real-one)
      (ht047-quoted real-add)
      (ht047-quoted real-multiply)
      (ht047-quoted real-negate)
      (ht047-quoted real-inverse))
     (ht047-static-apply-term sin '(x))))))

(defun ht047-analytic-functions-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp sin cos)
  (and
   (ht047-function-p real-carrier real-carrier exp)
   (ht047-function-p real-carrier real-carrier sin)
   (ht047-function-p real-carrier real-carrier cos)
   (ht047-universal-p
    (ht047-exp-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp)
    '(x))
   (ht047-universal-p
    (ht047-sin-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
    '(x))
   (ht047-universal-p
    (ht047-cos-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
    '(x))))

;; The total square-root operation agrees with the nonnegative root on
;; nonnegative inputs and is zero on negative inputs.

(defun ht047-square-root-laws-function
    (real-carrier real-zero real-multiply real-less square-root)
  (list
   'lambda '(x)
   (ht047-implies-term
    (ht047-static-apply-term real-carrier '(x))
    (let ((root (ht047-static-apply-term square-root '(x))))
      (ht047-and-terms
       (list
        (ht047-implies-term
         (ht047-static-apply-term
          real-less
          (list 'x (ht047-quoted real-zero)))
         (list 'equal root (ht047-quoted real-zero)))
        (ht047-implies-term
         (ht047-not-term
          (ht047-static-apply-term
           real-less
           (list 'x (ht047-quoted real-zero))))
         (ht047-and-terms
          (list
           (ht047-not-term
            (ht047-static-apply-term
             real-less
             (list root (ht047-quoted real-zero))))
           (list 'equal
                 (ht047-static-apply-term
                  real-multiply (list root root))
                 'x))))))))))

(defun ht047-square-root-operation-p
    (real-carrier real-zero real-multiply real-less square-root)
  (and
   (ht047-function-p real-carrier real-carrier square-root)
   (ht047-universal-p
    (ht047-square-root-laws-function
     real-carrier real-zero real-multiply real-less square-root)
    '(x))))

;; Real random-variable families and their laws.

(defun ht047-random-variable-family-function
    (sample-carrier sample-measurable
     real-carrier real-borel x-family)
  (list
   'lambda '(n)
   (ht047-implies-term
    (list 'natp 'n)
    (list
     'ht047-generic-measurable-function-p
     (ht047-quoted sample-carrier)
     (ht047-quoted sample-measurable)
     (ht047-quoted real-carrier)
     (ht047-quoted real-borel)
     (list
      'ht047-fiber-random-variable
      (ht047-quoted x-family)
      'n)))))

(defun ht047-random-variable-family-p
    (sample-carrier sample-measurable
     real-carrier real-borel x-family)
  (and
   (tamep-functionp x-family)
   (ht047-universal-p
    (ht047-random-variable-family-function
     sample-carrier sample-measurable
     real-carrier real-borel x-family)
    '(n))))

(defun ht047-distribution-equality-function
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure random-variable)
  (declare (ignore sample-measurable real-carrier))
  (list
   'lambda '(set)
   (ht047-implies-term
    (ht047-static-apply-term real-borel '(set))
    (list
     'equal
     (ht047-static-apply-term
      sample-measure
      (list
       (list
        'ht047-preimage-set
        (ht047-quoted sample-carrier)
        (ht047-quoted random-variable)
        'set)))
     (ht047-static-apply-term target-measure '(set))))))

(defun ht047-distribution-equal-p
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure random-variable)
  (and
   (ht047-generic-measurable-function-p
    sample-carrier sample-measurable
    real-carrier real-borel random-variable)
   (ht047-universal-p
    (ht047-distribution-equality-function
     sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure random-variable)
    '(set))))

(defun ht047-common-distribution-family-function
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure x-family)
  (list
   'lambda '(n)
   (ht047-implies-term
    (list 'natp 'n)
    (list
     'ht047-distribution-equal-p
     (ht047-quoted sample-carrier)
     (ht047-quoted sample-measurable)
     (ht047-quoted sample-measure)
     (ht047-quoted real-carrier)
     (ht047-quoted real-borel)
     (ht047-quoted target-measure)
     (list
      'ht047-fiber-random-variable
      (ht047-quoted x-family)
      'n)))))

(defun ht047-common-distribution-family-p
    (sample-carrier sample-measurable sample-measure
     real-carrier real-borel target-measure x-family)
  (ht047-universal-p
   (ht047-common-distribution-family-function
    sample-carrier sample-measurable sample-measure
    real-carrier real-borel target-measure x-family)
   '(n)))

(defun ht047-natural-list-p (indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (ht047-natural-list-p (cdr indices)))
    (equal indices nil)))

(defun ht047-measurable-set-list-p (sets real-borel)
  (if (consp sets)
      (and
       (tamep-functionp (car sets))
       (ht047-member-p real-borel (car sets))
       (ht047-measurable-set-list-p (cdr sets) real-borel))
    (equal sets nil)))

(defun ht047-joint-event-set
    (sample-carrier x-family indices sets)
  (if (and (consp indices) (consp sets))
      (let ((tail
             (ht047-joint-event-set
              sample-carrier x-family
              (cdr indices) (cdr sets))))
        (list
         'lambda '(x)
         (ht047-and-terms
          (list
           (ht047-static-apply-term sample-carrier '(x))
           (ht047-static-apply-term
            (car sets)
            (list
             (ht047-static-apply-term
              x-family
              (list
               (ht047-quoted (car indices))
               'x))))
           (ht047-static-apply-term tail '(x))))))
    (ht047-full-set sample-carrier)))

(defun ht047-marginal-event-set
    (sample-carrier x-family index set)
  (ht047-preimage-set
   sample-carrier
   (ht047-fiber-random-variable x-family index)
   set))

(defun ht047-marginal-product
    (sample-carrier sample-measure x-family indices sets
     real-zero real-one real-multiply)
  (if (and (consp indices) (consp sets))
      (ht047-ennreal-multiply
       (ht047-unary-value
        sample-measure
        (ht047-marginal-event-set
         sample-carrier x-family
         (car indices) (car sets)))
       (ht047-marginal-product
        sample-carrier sample-measure x-family
        (cdr indices) (cdr sets)
        real-zero real-one real-multiply)
       real-zero real-multiply)
    (ht047-ennreal-finite real-one)))

(defun ht047-finite-independence-p
    (sample-carrier sample-measure x-family indices sets
     real-zero real-one real-multiply)
  (equal
   (ht047-unary-value
    sample-measure
    (ht047-joint-event-set
     sample-carrier x-family indices sets))
   (ht047-marginal-product
    sample-carrier sample-measure x-family indices sets
    real-zero real-one real-multiply)))

(defun ht047-independence-function
    (sample-carrier sample-measure real-borel x-family
     real-zero real-one real-multiply)
  (list
   'lambda '(indices sets)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'true-listp 'indices)
      (list 'no-duplicatesp-equal 'indices)
      (list 'ht047-natural-list-p 'indices)
      (list 'true-listp 'sets)
      (list 'equal (list 'len 'indices) (list 'len 'sets))
      (list
       'ht047-measurable-set-list-p
       'sets
       (ht047-quoted real-borel))))
    (list
     'ht047-finite-independence-p
     (ht047-quoted sample-carrier)
     (ht047-quoted sample-measure)
     (ht047-quoted x-family)
     'indices
     'sets
     (ht047-quoted real-zero)
     (ht047-quoted real-one)
     (ht047-quoted real-multiply)))))

(defun ht047-independent-random-variables-p
    (sample-carrier sample-measure real-borel x-family
     real-zero real-one real-multiply)
  (ht047-universal-p
   (ht047-independence-function
    sample-carrier sample-measure real-borel x-family
    real-zero real-one real-multiply)
   '(indices sets)))

;; Expectations, square integrability, and variance.

(defun ht047-square-function (function real-multiply)
  (list
   'lambda '(x)
   (ht047-static-apply-term
    real-multiply
    (list
     (ht047-static-apply-term function '(x))
     (ht047-static-apply-term function '(x))))))

(defun ht047-centered-square-function
    (function mean real-add real-multiply real-negate)
  (let ((centered
         (ht047-static-apply-term
          real-add
          (list
           (ht047-static-apply-term function '(x))
           (ht047-static-apply-term
            real-negate
            (list (ht047-quoted mean)))))))
    (list
     'lambda '(x)
     (ht047-static-apply-term
      real-multiply
      (list centered centered)))))

(defun ht047-expectation-value
    (real-zero real-add real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier function lintegral)
  (ht047-real-integral-value
   real-zero real-add real-negate real-less
   sample-carrier sample-measurable sample-measure
   real-carrier function lintegral))

(defun ht047-variance-value
    (real-zero real-add real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier function lintegral)
  (let ((mean
         (ht047-expectation-value
          real-zero real-add real-negate real-less
          sample-carrier sample-measurable sample-measure
          real-carrier function lintegral)))
    (ht047-real-integral-value
     real-zero real-add real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier
     (ht047-centered-square-function
      function mean real-add real-multiply real-negate)
     lintegral)))

(defun ht047-moment-laws-function
    (real-zero real-add real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier x-family lintegral mean sigma)
  (list
   'lambda '(n)
   (ht047-implies-term
    (list 'natp 'n)
    (let ((xn
           (list
            'ht047-fiber-random-variable
            (ht047-quoted x-family)
            'n)))
      (ht047-and-terms
       (list
        (list
         'equal
         (list
          'ht047-expectation-value
          (ht047-quoted real-zero)
          (ht047-quoted real-add)
          (ht047-quoted real-negate)
          (ht047-quoted real-less)
          (ht047-quoted sample-carrier)
          (ht047-quoted sample-measurable)
          (ht047-quoted sample-measure)
          (ht047-quoted real-carrier)
          xn
          (ht047-quoted lintegral))
         (ht047-quoted mean))
        (list
         'ht047-integrable-p
         (ht047-quoted real-zero)
         (ht047-quoted real-negate)
         (ht047-quoted real-less)
         (ht047-quoted sample-carrier)
         (ht047-quoted sample-measurable)
         (ht047-quoted sample-measure)
         (ht047-quoted real-carrier)
         (list
          'ht047-square-function
          xn
          (ht047-quoted real-multiply))
         (ht047-quoted lintegral))
        (list
         'equal
         (list
          'ht047-variance-value
          (ht047-quoted real-zero)
          (ht047-quoted real-add)
          (ht047-quoted real-multiply)
          (ht047-quoted real-negate)
          (ht047-quoted real-less)
          (ht047-quoted sample-carrier)
          (ht047-quoted sample-measurable)
          (ht047-quoted sample-measure)
          (ht047-quoted real-carrier)
          xn
          (ht047-quoted lintegral))
         (ht047-static-apply-term
          real-multiply
          (list
           (ht047-quoted sigma)
           (ht047-quoted sigma))))))))))

(defun ht047-moment-laws-p
    (real-zero real-add real-multiply real-negate real-less
     sample-carrier sample-measurable sample-measure
     real-carrier x-family lintegral mean sigma)
  (ht047-universal-p
   (ht047-moment-laws-function
    real-zero real-add real-multiply real-negate real-less
    sample-carrier sample-measurable sample-measure
    real-carrier x-family lintegral mean sigma)
   '(n)))

;; Partial sums, centering, and normalization.

(defun ht047-partial-sum-value
    (x-family n x real-zero real-add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (ht047-binary-value
     real-add
     (ht047-partial-sum-value
      x-family (- n 1) x real-zero real-add)
     (ht047-binary-value
      x-family (- n 1) x))))

(defun ht047-centered-partial-sum-value
    (x-family n x mean real-zero real-add real-negate)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (ht047-binary-value
     real-add
     (ht047-centered-partial-sum-value
      x-family (- n 1) x mean
      real-zero real-add real-negate)
     (ht047-binary-value
      real-add
      (ht047-binary-value x-family (- n 1) x)
      (ht047-unary-value real-negate mean)))))

(defun ht047-partial-sum-family
    (x-family real-zero real-add)
  (list
   'lambda '(n x)
   (list
    'ht047-partial-sum-value
    (ht047-quoted x-family)
    'n 'x
    (ht047-quoted real-zero)
    (ht047-quoted real-add))))

(defun ht047-partial-sum-family-equality-function
    (sample-carrier x-family s-family real-zero real-add)
  (list
   'lambda '(n x)
   (ht047-implies-term
    (ht047-and-terms
     (list
      (list 'natp 'n)
      (ht047-static-apply-term sample-carrier '(x))))
    (list
     'equal
     (ht047-static-apply-term s-family '(n x))
     (list
      'ht047-partial-sum-value
      (ht047-quoted x-family)
      'n 'x
      (ht047-quoted real-zero)
      (ht047-quoted real-add))))))

(defun ht047-partial-sum-family-p
    (sample-carrier x-family s-family real-zero real-add)
  (and
   (tamep-functionp s-family)
   (ht047-universal-p
    (ht047-partial-sum-family-equality-function
     sample-carrier x-family s-family real-zero real-add)
    '(n x))))

(defun ht047-normalized-value
    (sum-value n sigma
     real-zero real-one real-add real-multiply real-inverse square-root)
  (let* ((n-real
          (ht047-real-nat-value
           n real-zero real-one real-add))
         (sigma-square
          (ht047-binary-value real-multiply sigma sigma))
         (scale-square
          (ht047-binary-value real-multiply n-real sigma-square))
         (scale
          (ht047-unary-value square-root scale-square)))
    (ht047-binary-value
     real-multiply
     sum-value
     (ht047-unary-value real-inverse scale))))

(defun ht047-normalized-s-family
    (s-family sigma
     real-zero real-one real-add real-multiply real-inverse square-root)
  (list
   'lambda '(n x)
   (list
    'ht047-normalized-value
    (ht047-static-apply-term s-family '(n x))
    'n
    (ht047-quoted sigma)
    (ht047-quoted real-zero)
    (ht047-quoted real-one)
    (ht047-quoted real-add)
    (ht047-quoted real-multiply)
    (ht047-quoted real-inverse)
    (ht047-quoted square-root))))

(defun ht047-centered-normalized-x-family
    (x-family mean sigma
     real-zero real-one real-add real-multiply
     real-negate real-inverse square-root)
  (list
   'lambda '(n x)
   (list
    'ht047-normalized-value
    (list
     'ht047-centered-partial-sum-value
     (ht047-quoted x-family)
     'n 'x
     (ht047-quoted mean)
     (ht047-quoted real-zero)
     (ht047-quoted real-add)
     (ht047-quoted real-negate))
    'n
    (ht047-quoted sigma)
    (ht047-quoted real-zero)
    (ht047-quoted real-one)
    (ht047-quoted real-add)
    (ht047-quoted real-multiply)
    (ht047-quoted real-inverse)
    (ht047-quoted square-root))))

;; The standard normal law is characterized exactly by its characteristic
;; function: cosine integral exp(-t^2/2) and sine integral zero.

(defun ht047-characteristic-cos-function
    (t-value real-multiply cos)
  (list
   'lambda '(x)
   (ht047-static-apply-term
    cos
    (list
     (ht047-static-apply-term
      real-multiply
      (list (ht047-quoted t-value) 'x))))))

(defun ht047-characteristic-sin-function
    (t-value real-multiply sin)
  (list
   'lambda '(x)
   (ht047-static-apply-term
    sin
    (list
     (ht047-static-apply-term
      real-multiply
      (list (ht047-quoted t-value) 'x))))))

(defun ht047-standard-normal-characteristic-function
    (real-zero real-one real-add real-multiply real-negate
     real-inverse real-less real-carrier real-borel
     standard-normal-measure lintegral exp sin cos)
  (list
   'lambda '(t-value)
   (ht047-implies-term
    (ht047-static-apply-term real-carrier '(t-value))
    (let* ((two
            (ht047-real-nat-value
             2 real-zero real-one real-add))
           (t-square
            (ht047-static-apply-term
             real-multiply '(t-value t-value)))
           (minus-half-square
            (ht047-static-apply-term
             real-negate
             (list
              (ht047-static-apply-term
               real-multiply
               (list
                t-square
                (ht047-static-apply-term
                 real-inverse
                 (list (ht047-quoted two)))))))))
      (ht047-and-terms
       (list
        (list
         'equal
         (list
          'ht047-real-integral-value
          (ht047-quoted real-zero)
          (ht047-quoted real-add)
          (ht047-quoted real-negate)
          (ht047-quoted real-less)
          (ht047-quoted real-carrier)
          (ht047-quoted real-borel)
          (ht047-quoted standard-normal-measure)
          (ht047-quoted real-carrier)
          (list
           'ht047-characteristic-cos-function
           't-value
           (ht047-quoted real-multiply)
           (ht047-quoted cos))
          (ht047-quoted lintegral))
         (ht047-static-apply-term exp (list minus-half-square)))
        (list
         'equal
         (list
          'ht047-real-integral-value
          (ht047-quoted real-zero)
          (ht047-quoted real-add)
          (ht047-quoted real-negate)
          (ht047-quoted real-less)
          (ht047-quoted real-carrier)
          (ht047-quoted real-borel)
          (ht047-quoted standard-normal-measure)
          (ht047-quoted real-carrier)
          (list
           'ht047-characteristic-sin-function
           't-value
           (ht047-quoted real-multiply)
           (ht047-quoted sin))
          (ht047-quoted lintegral))
         (ht047-quoted real-zero))))))))

(defun ht047-standard-normal-distribution-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-borel
     standard-normal-measure lintegral exp sin cos)
  (and
   (ht047-probability-measure-p
    real-carrier real-zero real-one real-add real-less
    real-carrier real-borel standard-normal-measure)
   (ht047-lintegral-operation-p
    real-carrier real-zero real-add real-multiply real-less
    real-carrier real-borel standard-normal-measure lintegral)
   (ht047-universal-p
    (ht047-standard-normal-characteristic-function
     real-zero real-one real-add real-multiply real-negate
     real-inverse real-less real-carrier real-borel
     standard-normal-measure lintegral exp sin cos)
    '(t-value))))

;; Constant source-space families let the general weak-convergence definition
;; express weak convergence of the laws of random variables on one space.

(defun ht047-constant-source-carrier-family (sample-carrier)
  (list
   'lambda '(n x)
   (ht047-static-apply-term sample-carrier '(x))))

(defun ht047-constant-source-measurable-family (sample-measurable)
  (list
   'lambda '(n set)
   (ht047-static-apply-term sample-measurable '(set))))

(defun ht047-constant-source-measure-family (sample-measure)
  (list
   'lambda '(n set)
   (ht047-static-apply-term sample-measure '(set))))

(defun ht047-real-identity-function ()
  (list 'lambda '(x) 'x))

(defun ht047-weak-convergence-to-standard-normal-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     sample-carrier sample-measurable sample-measure lintegral
     normalized-family real-borel standard-normal-measure)
  (ht047-weak-convergence-p
   real-carrier real-zero real-add real-negate real-less real-topology
   (ht047-natural-carrier)
   (ht047-sequential-filter)
   (ht047-constant-source-carrier-family sample-carrier)
   (ht047-constant-source-measurable-family sample-measurable)
   (ht047-constant-source-measure-family sample-measure)
   lintegral
   normalized-family
   real-carrier
   real-borel
   standard-normal-measure
   lintegral
   (ht047-real-identity-function)
   real-carrier
   real-topology))

;; Shared structural and probabilistic hypotheses of the two source theorems.

(defun ht047-central-limit-context-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology real-borel exp sin cos square-root
     sample-carrier sample-measurable sample-measure
     common-measure standard-normal-measure lintegral
     x-family mean sigma)
  (and
   (ht047-real-field-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less real-supremum)
   (ht047-order-topology-p
    real-carrier real-less real-topology)
   (ht047-borel-space-p
    real-carrier real-topology real-borel)
   (ht047-filter-p
    (ht047-natural-carrier)
    (ht047-sequential-filter))
   (ht047-analytic-functions-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less exp sin cos)
   (ht047-square-root-operation-p
    real-carrier real-zero real-multiply real-less square-root)
   (ht047-probability-measure-p
    real-carrier real-zero real-one real-add real-less
    sample-carrier sample-measurable sample-measure)
   (ht047-lintegral-operation-p
    real-carrier real-zero real-add real-multiply real-less
    sample-carrier sample-measurable sample-measure lintegral)
   (ht047-measure-space-p
    real-carrier real-zero real-add real-less
    real-carrier real-borel common-measure)
   (ht047-standard-normal-distribution-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less real-borel
    standard-normal-measure lintegral exp sin cos)
   (ht047-random-variable-family-p
    sample-carrier sample-measurable
    real-carrier real-borel x-family)
   (ht047-independent-random-variables-p
    sample-carrier sample-measure real-borel x-family
    real-zero real-one real-multiply)
   (ht047-common-distribution-family-p
    sample-carrier sample-measurable sample-measure
    real-carrier real-borel common-measure x-family)
   (ht047-member-p real-carrier mean)
   (ht047-member-p real-carrier sigma)
   (ht047-binary-value real-less real-zero sigma)
   (ht047-moment-laws-p
    real-zero real-add real-multiply real-negate real-less
    sample-carrier sample-measurable sample-measure
    real-carrier x-family lintegral mean sigma)))

(defun hundred-theorems-047-central-limit-theorem-zero-mean-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology real-borel exp sin cos square-root
     sample-carrier sample-measurable sample-measure
     common-measure standard-normal-measure lintegral
     x-family sigma s-family)
  (implies
   (and
    (ht047-central-limit-context-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology real-borel exp sin cos square-root
     sample-carrier sample-measurable sample-measure
     common-measure standard-normal-measure lintegral
     x-family real-zero sigma)
    (ht047-partial-sum-family-p
     sample-carrier x-family s-family real-zero real-add))
   (ht047-weak-convergence-to-standard-normal-p
    real-carrier real-zero real-add real-negate real-less real-topology
    sample-carrier sample-measurable sample-measure lintegral
    (ht047-normalized-s-family
     s-family sigma
     real-zero real-one real-add real-multiply
     real-inverse square-root)
    real-borel standard-normal-measure)))

(defun hundred-theorems-047-central-limit-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology real-borel exp sin cos square-root
     sample-carrier sample-measurable sample-measure
     common-measure standard-normal-measure lintegral
     x-family mean sigma)
  (implies
   (ht047-central-limit-context-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less real-supremum
    real-topology real-borel exp sin cos square-root
    sample-carrier sample-measurable sample-measure
    common-measure standard-normal-measure lintegral
    x-family mean sigma)
   (ht047-weak-convergence-to-standard-normal-p
    real-carrier real-zero real-add real-negate real-less real-topology
    sample-carrier sample-measurable sample-measure lintegral
    (ht047-centered-normalized-x-family
     x-family mean sigma
     real-zero real-one real-add real-multiply
     real-negate real-inverse square-root)
    real-borel standard-normal-measure)))

(value-triple :itpeval-statement-checked)
:q
