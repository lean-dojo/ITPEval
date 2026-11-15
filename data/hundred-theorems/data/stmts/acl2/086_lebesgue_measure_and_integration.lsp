;; Statement-only formalization of Hundred Theorems artifact 086,
;; "Lebesgue Measure and Integration": on every arbitrary measure space, the
;; lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple minorants and satisfies existence and uniqueness,
;; indicator normalization, monotonicity, measurable additivity,
;; almost-everywhere congruence, monotone convergence, and measurable-set
;; restriction. This file contains no proof.
;; Manual semantic audit (2026-09-06): retained as a historical candidate,
;; but not counted as a faithful standard-ACL2 translation. See
;; corpus-extension/semantic_canonical_resolutions.json for the blocker.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, functions, sigma algebras, and operations are tame APPLY$
;; function objects. FN-EQUAL supplies unbounded universal quantification, and
;; inequality with a constant-false function supplies internal existential
;; witnesses. The scalar structure is a Dedekind-complete ordered field, hence
;; a presentation of the real field. The measure on an arbitrary subset is
;; characterized as the infimum of the measures of its measurable supersets.
;; Measurability is defined through upper-ray preimages, and lintegral is the
;; supremum of integrals of measurable finite-range simple functions below
;; the integrand. Liminf is characterized order-theoretically as the supremum
;; of all eventual lower bounds, which is the atTop filter liminf.

(defun ht086-quoted (object)
  (list 'quote object))

(defun ht086-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (ht086-term-list (cdr terms)))
    (ht086-quoted nil)))

(defun ht086-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (ht086-term-list arguments)))

(defun ht086-static-apply-term (function arguments)
  (ht086-apply-term
   (ht086-quoted function)
   arguments))

(defun ht086-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht086-and-terms (cdr terms))
            (ht086-quoted nil))
    (ht086-quoted t)))

(defun ht086-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht086-quoted t)
            (ht086-or-terms (cdr terms)))
    (ht086-quoted nil)))

(defun ht086-not-term (term)
  (list 'if term
        (ht086-quoted nil)
        (ht086-quoted t)))

(defun ht086-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        (list 'if
              conclusion
              (ht086-quoted t)
              (ht086-quoted nil))
        (ht086-quoted t)))

(defun ht086-iff-term (left right)
  (list 'if left
        (list 'if right
              (ht086-quoted t)
              (ht086-quoted nil))
        (list 'if right
              (ht086-quoted nil)
              (ht086-quoted t))))

(defun ht086-true-function (formals)
  (list 'lambda formals (ht086-quoted t)))

(defun ht086-false-function (formals)
  (list 'lambda formals (ht086-quoted nil)))

(defun ht086-universal-p (function formals)
  (let ((always-true (ht086-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun ht086-exists-p (function formals)
  (let ((always-false (ht086-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun ht086-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht086-unary-value (function object)
  (apply$ function (list object)))

(defun ht086-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun ht086-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (ht086-static-apply-term carrier '(x))
      (ht086-static-apply-term left '(x))))
    (ht086-static-apply-term right '(x)))))

(defun ht086-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (ht086-universal-p
    (ht086-set-subset-function carrier left right)
    '(x))))

(defun ht086-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (ht086-set-subset-p carrier set carrier)))

(defun ht086-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term carrier '(x))
    (ht086-iff-term
     (ht086-static-apply-term left '(x))
     (ht086-static-apply-term right '(x))))))

(defun ht086-set-equiv-p (carrier left right)
  (and
   (ht086-valid-set-p carrier left)
   (ht086-valid-set-p carrier right)
   (ht086-universal-p
    (ht086-set-equiv-function carrier left right)
    '(x))))

(defun ht086-empty-set ()
  (list 'lambda '(x) (ht086-quoted nil)))

(defun ht086-full-set (carrier)
  (list 'lambda '(x)
        (ht086-static-apply-term carrier '(x))))

(defun ht086-complement-set (carrier set)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term carrier '(x))
     (ht086-not-term
      (ht086-static-apply-term set '(x)))))))

(defun ht086-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term domain-carrier '(x))
    (ht086-static-apply-term
     codomain-carrier
     (list (ht086-static-apply-term function '(x)))))))

(defun ht086-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (ht086-universal-p
    (ht086-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun ht086-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (ht086-static-apply-term add '(x y)))
         (yz-add (ht086-static-apply-term add '(y z)))
         (xy-mul (ht086-static-apply-term multiply '(x y)))
         (yz-mul (ht086-static-apply-term multiply '(y z)))
         (neg-x (ht086-static-apply-term negate '(x)))
         (inv-x (ht086-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (ht086-implies-term
      (ht086-and-terms
       (list
        (ht086-static-apply-term carrier '(x))
        (ht086-static-apply-term carrier '(y))
        (ht086-static-apply-term carrier '(z))))
      (ht086-and-terms
       (list
        (ht086-static-apply-term carrier (list xy-add))
        (ht086-static-apply-term carrier (list xy-mul))
        (ht086-static-apply-term carrier (list neg-x))
        (ht086-static-apply-term carrier (list inv-x))
        (list 'equal
              (ht086-static-apply-term add (list xy-add 'z))
              (ht086-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (ht086-static-apply-term add '(y x)))
        (list 'equal
              (ht086-static-apply-term
               add (list 'x (ht086-quoted zero)))
              'x)
        (list 'equal
              (ht086-static-apply-term add (list 'x neg-x))
              (ht086-quoted zero))
        (list 'equal
              (ht086-static-apply-term multiply (list xy-mul 'z))
              (ht086-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (ht086-static-apply-term multiply '(y x)))
        (list 'equal
              (ht086-static-apply-term
               multiply (list 'x (ht086-quoted one)))
              'x)
        (ht086-implies-term
         (list 'equal 'x (ht086-quoted zero))
         (list 'equal inv-x (ht086-quoted zero)))
        (ht086-implies-term
         (ht086-not-term
          (list 'equal 'x (ht086-quoted zero)))
         (list 'equal
               (ht086-static-apply-term
                multiply (list 'x inv-x))
               (ht086-quoted one)))
        (list 'equal
              (ht086-static-apply-term multiply (list 'x yz-add))
              (ht086-static-apply-term
               add
               (list
                (ht086-static-apply-term multiply '(x y))
                (ht086-static-apply-term multiply '(x z)))))))))))

(defun ht086-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (ht086-static-apply-term less '(x y)))
        (yx (ht086-static-apply-term less '(y x)))
        (yz (ht086-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (ht086-implies-term
      (ht086-and-terms
       (list
        (ht086-static-apply-term carrier '(x))
        (ht086-static-apply-term carrier '(y))
        (ht086-static-apply-term carrier '(z))))
      (ht086-and-terms
       (list
        (ht086-not-term
         (ht086-static-apply-term less '(x x)))
        (ht086-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (ht086-implies-term
         (ht086-and-terms (list xy yz))
         (ht086-static-apply-term less '(x z)))
        (ht086-implies-term
         xy
         (ht086-static-apply-term
          less
          (list
           (ht086-static-apply-term add '(x z))
           (ht086-static-apply-term add '(y z)))))
        (ht086-implies-term
         (ht086-and-terms
          (list
           (ht086-static-apply-term
            less (list (ht086-quoted zero) 'x))
           (ht086-static-apply-term
            less (list (ht086-quoted zero) 'y))))
         (ht086-static-apply-term
          less
          (list
           (ht086-quoted zero)
           (ht086-static-apply-term multiply '(x y)))))))))))

(defun ht086-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (ht086-static-apply-term carrier '(x))
      (ht086-static-apply-term set '(x))))
    (ht086-not-term
     (ht086-static-apply-term
      less (list (ht086-quoted upper) 'x))))))

(defun ht086-upper-bound-p
    (carrier less set upper)
  (and
   (ht086-member-p carrier upper)
   (ht086-valid-set-p carrier set)
   (ht086-universal-p
    (ht086-upper-bound-function carrier less set upper)
    '(x))))

(defun ht086-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term carrier '(x))
     (ht086-static-apply-term set '(x))))))

(defun ht086-set-nonempty-p (carrier set)
  (and
   (ht086-valid-set-p carrier set)
   (ht086-exists-p
    (ht086-set-nonempty-function carrier set)
    '(x))))

(defun ht086-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'ht086-upper-bound-p
         (ht086-quoted carrier)
         (ht086-quoted less)
         (ht086-quoted set)
         'upper)))

(defun ht086-bounded-above-p (carrier less set)
  (ht086-exists-p
   (ht086-bounded-above-function carrier less set)
   '(upper)))

(defun ht086-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (ht086-implies-term
    (list 'ht086-upper-bound-p
          (ht086-quoted carrier)
          (ht086-quoted less)
          (ht086-quoted set)
          'upper)
    (ht086-not-term
     (ht086-static-apply-term
      less (list 'upper (ht086-quoted supremum)))))))

(defun ht086-least-upper-bound-p
    (carrier less set supremum)
  (and
   (ht086-upper-bound-p carrier less set supremum)
   (ht086-universal-p
    (ht086-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun ht086-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-valid-set-p
            (ht086-quoted carrier) 'set)
      (list 'ht086-set-nonempty-p
            (ht086-quoted carrier) 'set)
      (list 'ht086-bounded-above-p
            (ht086-quoted carrier)
            (ht086-quoted less)
            'set)))
    (list 'ht086-least-upper-bound-p
          (ht086-quoted carrier)
          (ht086-quoted less)
          'set
          (ht086-static-apply-term
           supremum-operation '(set))))))

(defun ht086-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (ht086-member-p carrier zero)
   (ht086-member-p carrier one)
   (not (equal zero one))
   (ht086-universal-p
    (ht086-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (ht086-universal-p
    (ht086-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (ht086-universal-p
    (ht086-completeness-function
     carrier less supremum)
    '(set))
   (ht086-binary-value less zero one)))

(defun ht086-scalar-absolute-value
    (less zero negate value)
  (if (ht086-binary-value less value zero)
      (ht086-unary-value negate value)
    value))
;; Sigma algebras.

(defun ht086-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (ht086-implies-term
    (list 'ht086-set-equiv-p
          (ht086-quoted carrier)
          'left 'right)
    (ht086-iff-term
     (ht086-static-apply-term family '(left))
     (ht086-static-apply-term family '(right))))))

(defun ht086-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (ht086-implies-term
    (ht086-static-apply-term family '(set))
    (list 'ht086-valid-set-p
          (ht086-quoted carrier)
          'set))))

(defun ht086-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (ht086-universal-p
    (ht086-family-extensional-function carrier family)
    '(left right))
   (ht086-universal-p
    (ht086-family-members-valid-function carrier family)
    '(set))))

(defun ht086-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (ht086-and-terms
    (list
     (list 'natp 'n)
     (ht086-apply-term
      (ht086-static-apply-term sequence '(n))
      (list (ht086-quoted x)))))))

(defun ht086-sequence-union-member-p (sequence x)
  (ht086-exists-p
   (ht086-sequence-union-member-function sequence x)
   '(n)))

(defun ht086-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term carrier '(x))
     (list 'ht086-sequence-union-member-p
           (ht086-quoted sequence)
           'x)))))

(defun ht086-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (ht086-implies-term
    (list 'natp 'n)
    (list 'ht086-valid-set-p
          (ht086-quoted carrier)
          (ht086-static-apply-term sequence '(n))))))

(defun ht086-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (ht086-universal-p
    (ht086-sequence-of-sets-function carrier sequence)
    '(n))))

(defun ht086-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (ht086-implies-term
    (list 'natp 'n)
    (ht086-static-apply-term
     family
     (list (ht086-static-apply-term sequence '(n)))))))

(defun ht086-sequence-members-family-p
    (carrier family sequence)
  (and
   (ht086-sequence-of-sets-p carrier sequence)
   (ht086-universal-p
    (ht086-sequence-members-family-function family sequence)
    '(n))))

(defun ht086-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (ht086-implies-term
    (ht086-static-apply-term family '(set))
    (ht086-static-apply-term
     family
     (list
      (list 'ht086-complement-set
            (ht086-quoted carrier)
            'set))))))

(defun ht086-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (ht086-implies-term
    (list 'ht086-sequence-members-family-p
          (ht086-quoted carrier)
          (ht086-quoted family)
          'sequence)
    (ht086-static-apply-term
     family
     (list
      (list 'ht086-sequence-union-set
            (ht086-quoted carrier)
            'sequence))))))

(defun ht086-sigma-algebra-p (carrier family)
  (and
   (ht086-family-of-sets-p carrier family)
   (ht086-member-p family (ht086-empty-set))
   (ht086-universal-p
    (ht086-sigma-complement-function carrier family)
    '(set))
   (ht086-universal-p
    (ht086-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun ht086-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :ht086-top)
   (and
    (consp value)
    (equal (car value) :ht086-finite)
    (ht086-member-p scalar-carrier (cdr value))
    (not
     (ht086-binary-value scalar-less (cdr value) scalar-zero)))))

(defun ht086-ennreal-finite (value)
  (cons :ht086-finite value))

(defun ht086-ennreal-zero (scalar-zero)
  (ht086-ennreal-finite scalar-zero))

(defun ht086-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :ht086-top) nil)
   ((equal right :ht086-top) t)
   (t
    (ht086-binary-value scalar-less (cdr left) (cdr right)))))

(defun ht086-ennreal-less-equal-p (left right scalar-less)
  (not (ht086-ennreal-less-p right left scalar-less)))

(defun ht086-ennreal-add (left right scalar-add)
  (if (or (equal left :ht086-top)
          (equal right :ht086-top))
      :ht086-top
    (ht086-ennreal-finite
     (ht086-binary-value scalar-add (cdr left) (cdr right)))))

(defun ht086-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (ht086-ennreal-zero scalar-zero))
        (equal right (ht086-ennreal-zero scalar-zero)))
    (ht086-ennreal-zero scalar-zero))
   ((or (equal left :ht086-top)
        (equal right :ht086-top))
    :ht086-top)
   (t
    (ht086-ennreal-finite
     (ht086-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun ht086-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht086-ennreal-zero scalar-zero)
    (ht086-ennreal-add
     (ht086-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (ht086-unary-value sequence (- count 1))
     scalar-add)))

(defun ht086-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (ht086-implies-term
    (list 'natp 'count)
    (list 'ht086-ennreal-less-equal-p
          (list 'ht086-finite-ennreal-sum
                (ht086-quoted sequence)
                'count
                (ht086-quoted scalar-zero)
                (ht086-quoted scalar-add))
          (ht086-quoted total)
          (ht086-quoted scalar-less)))))

(defun ht086-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (ht086-universal-p
   (ht086-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun ht086-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-ennreal-p
            'bound
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-less))
      (list 'ht086-sum-upper-bound-p
            (ht086-quoted sequence)
            'bound
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-less))))
    (list 'ht086-ennreal-less-equal-p
          (ht086-quoted total)
          'bound
          (ht086-quoted scalar-less)))))

(defun ht086-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (ht086-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (ht086-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (ht086-universal-p
    (ht086-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun ht086-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (ht086-implies-term
    (list 'ht086-set-equiv-p
          (ht086-quoted carrier)
          'left 'right)
    (list 'equal
          (ht086-static-apply-term measure '(left))
          (ht086-static-apply-term measure '(right))))))

(defun ht086-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (ht086-implies-term
    (list 'ht086-valid-set-p
          (ht086-quoted carrier)
          'set)
    (list 'ht086-ennreal-p
          (ht086-static-apply-term measure '(set))
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-less)))))

(defun ht086-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (ht086-static-apply-term
    measure
    (list (ht086-static-apply-term sequence '(n))))))

(defun ht086-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term carrier '(x))
    (ht086-not-term
     (ht086-and-terms
      (list
       (ht086-static-apply-term left '(x))
       (ht086-static-apply-term right '(x))))))))

(defun ht086-disjoint-sets-p (carrier left right)
  (ht086-universal-p
   (ht086-disjoint-sets-function carrier left right)
   '(x)))

(defun ht086-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (ht086-not-term (list 'equal 'm 'n))))
    (list 'ht086-disjoint-sets-p
          (ht086-quoted carrier)
          (ht086-static-apply-term sequence '(m))
          (ht086-static-apply-term sequence '(n))))))

(defun ht086-pairwise-disjoint-p (carrier sequence)
  (ht086-universal-p
   (ht086-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun ht086-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-sequence-members-family-p
            (ht086-quoted carrier)
            (ht086-quoted measurable)
            'sequence)
      (list 'ht086-pairwise-disjoint-p
            (ht086-quoted carrier)
            'sequence)))
    (list 'ht086-countable-sum-p
          (list 'ht086-measure-sequence-values
                (ht086-quoted measure)
                'sequence)
          (ht086-static-apply-term
           measure
           (list
            (list 'ht086-sequence-union-set
                  (ht086-quoted carrier)
                  'sequence)))
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-less)))))

(defun ht086-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (ht086-static-apply-term measurable '(superset))
      (list 'ht086-set-subset-p
            (ht086-quoted carrier)
            (ht086-quoted set)
            'superset)))
    (list 'ht086-ennreal-less-equal-p
          (ht086-quoted lower)
          (ht086-static-apply-term measure '(superset))
          (ht086-quoted scalar-less)))))

(defun ht086-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (ht086-universal-p
   (ht086-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun ht086-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-ennreal-p
            'lower
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-less))
      (list 'ht086-measurable-superset-lower-bound-p
            (ht086-quoted carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            (ht086-quoted set)
            'lower
            (ht086-quoted scalar-less))))
    (list 'ht086-ennreal-less-equal-p
          'lower
          (ht086-static-apply-term
           measure (list (ht086-quoted set)))
          (ht086-quoted scalar-less)))))

(defun ht086-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (ht086-valid-set-p carrier set)
   (ht086-measurable-superset-lower-bound-p
    carrier measurable measure set
    (ht086-unary-value measure set)
    scalar-less)
   (ht086-universal-p
    (ht086-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun ht086-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (ht086-implies-term
    (list 'ht086-valid-set-p
          (ht086-quoted carrier)
          'set)
    (list 'ht086-outer-value-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-less)
          (ht086-quoted carrier)
          (ht086-quoted measurable)
          (ht086-quoted measure)
          'set))))

(defun ht086-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (ht086-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (ht086-universal-p
    (ht086-measure-extensional-function carrier measure)
    '(left right))
   (ht086-universal-p
    (ht086-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (equal
    (ht086-unary-value measure (ht086-empty-set))
    (ht086-ennreal-zero scalar-zero))
   (ht086-universal-p
    (ht086-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (ht086-universal-p
    (ht086-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; Function sequences and order-topological convergence.

(defun ht086-ennreal-carrier
    (scalar-carrier scalar-zero scalar-less)
  (list
   'lambda '(value)
   (list 'ht086-ennreal-p
         'value
         (ht086-quoted scalar-carrier)
         (ht086-quoted scalar-zero)
         (ht086-quoted scalar-less))))

(defun ht086-ennreal-less-function (scalar-less)
  (list
   'lambda '(left right)
   (list 'ht086-ennreal-less-p
         'left 'right
         (ht086-quoted scalar-less))))

(defun ht086-less-equal-term (less left right)
  (ht086-not-term
   (ht086-static-apply-term less (list right left))))

(defun ht086-sequence-term-function (sequence n)
  (list
   'lambda '(x)
   (ht086-apply-term
    (ht086-static-apply-term
     sequence (list (ht086-quoted n)))
    '(x))))

(defun ht086-function-sequence-values-function
    (domain-carrier codomain-carrier sequence)
  (list
   'lambda '(n)
   (ht086-implies-term
    (list 'natp 'n)
    (list 'ht086-function-p
          (ht086-quoted domain-carrier)
          (ht086-quoted codomain-carrier)
          (ht086-static-apply-term sequence '(n))))))

(defun ht086-function-sequence-p
    (domain-carrier codomain-carrier sequence)
  (and
   (tamep-functionp sequence)
   (ht086-universal-p
    (ht086-function-sequence-values-function
     domain-carrier codomain-carrier sequence)
    '(n))))

(defun ht086-natural-values-function
    (carrier values)
  (list
   'lambda '(n)
   (ht086-implies-term
    (list 'natp 'n)
    (ht086-static-apply-term
     carrier
     (list (ht086-static-apply-term values '(n)))))))

(defun ht086-natural-values-p (carrier values)
  (and
   (tamep-functionp values)
   (ht086-universal-p
    (ht086-natural-values-function carrier values)
    '(n))))

(defun ht086-eventual-lower-function
    (values less lower start)
  (list
   'lambda '(n)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'natp 'n)
      (list '<= (ht086-quoted start) 'n)))
    (ht086-static-apply-term
     less
     (list
      (ht086-quoted lower)
      (ht086-static-apply-term values '(n)))))))

(defun ht086-eventual-lower-p
    (values less lower start)
  (and
   (natp start)
   (ht086-universal-p
    (ht086-eventual-lower-function
     values less lower start)
    '(n))))

(defun ht086-lower-start-function
    (values less lower)
  (list
   'lambda '(start)
   (list 'ht086-eventual-lower-p
         (ht086-quoted values)
         (ht086-quoted less)
         (ht086-quoted lower)
         'start)))

(defun ht086-eventually-above-p
    (values less lower)
  (ht086-exists-p
   (ht086-lower-start-function values less lower)
   '(start)))

(defun ht086-eventual-upper-function
    (values less upper start)
  (list
   'lambda '(n)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'natp 'n)
      (list '<= (ht086-quoted start) 'n)))
    (ht086-static-apply-term
     less
     (list
      (ht086-static-apply-term values '(n))
      (ht086-quoted upper))))))

(defun ht086-eventual-upper-p
    (values less upper start)
  (and
   (natp start)
   (ht086-universal-p
    (ht086-eventual-upper-function
     values less upper start)
    '(n))))

(defun ht086-upper-start-function
    (values less upper)
  (list
   'lambda '(start)
   (list 'ht086-eventual-upper-p
         (ht086-quoted values)
         (ht086-quoted less)
         (ht086-quoted upper)
         'start)))

(defun ht086-eventually-below-p
    (values less upper)
  (ht086-exists-p
   (ht086-upper-start-function values less upper)
   '(start)))

(defun ht086-order-convergence-bound-function
    (carrier less values limit)
  (list
   'lambda '(bound)
   (ht086-implies-term
    (ht086-static-apply-term carrier '(bound))
    (ht086-and-terms
     (list
      (ht086-implies-term
       (ht086-static-apply-term
        less (list 'bound (ht086-quoted limit)))
       (list 'ht086-eventually-above-p
             (ht086-quoted values)
             (ht086-quoted less)
             'bound))
      (ht086-implies-term
       (ht086-static-apply-term
        less (list (ht086-quoted limit) 'bound))
       (list 'ht086-eventually-below-p
             (ht086-quoted values)
             (ht086-quoted less)
             'bound)))))))

(defun ht086-tendsto-order-p
    (carrier less values limit)
  (and
   (tamep-functionp carrier)
   (tamep-functionp less)
   (ht086-natural-values-p carrier values)
   (ht086-member-p carrier limit)
   (ht086-universal-p
    (ht086-order-convergence-bound-function
     carrier less values limit)
    '(bound))))

;; Pointwise monotonicity and almost-everywhere order convergence.

(defun ht086-pointwise-values-function (sequence x)
  (list
   'lambda '(n)
   (ht086-apply-term
    (ht086-static-apply-term sequence '(n))
    (list (ht086-quoted x)))))

(defun ht086-pointwise-monotone-index-function
    (sequence less x)
  (let ((left
         (ht086-apply-term
          (ht086-static-apply-term sequence '(n))
          (list (ht086-quoted x))))
        (right
         (ht086-apply-term
          (ht086-static-apply-term sequence '(m))
          (list (ht086-quoted x)))))
    (list
     'lambda '(n m)
     (ht086-implies-term
      (ht086-and-terms
       (list
        (list 'natp 'n)
        (list 'natp 'm)
        (list '<= 'n 'm)))
      (ht086-less-equal-term less left right)))))

(defun ht086-pointwise-monotone-p
    (sequence less x)
  (ht086-universal-p
   (ht086-pointwise-monotone-index-function
    sequence less x)
   '(n m)))

(defun ht086-pointwise-antitone-index-function
    (sequence less x)
  (let ((left
         (ht086-apply-term
          (ht086-static-apply-term sequence '(m))
          (list (ht086-quoted x))))
        (right
         (ht086-apply-term
          (ht086-static-apply-term sequence '(n))
          (list (ht086-quoted x)))))
    (list
     'lambda '(n m)
     (ht086-implies-term
      (ht086-and-terms
       (list
        (list 'natp 'n)
        (list 'natp 'm)
        (list '<= 'n 'm)))
      (ht086-less-equal-term less left right)))))

(defun ht086-pointwise-antitone-p
    (sequence less x)
  (ht086-universal-p
   (ht086-pointwise-antitone-index-function
    sequence less x)
   '(n m)))

(defun ht086-monotone-failure-set
    (domain-carrier sequence less)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (ht086-not-term
      (list 'ht086-pointwise-monotone-p
            (ht086-quoted sequence)
            (ht086-quoted less)
            'x))))))

(defun ht086-antitone-failure-set
    (domain-carrier sequence less)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (ht086-not-term
      (list 'ht086-pointwise-antitone-p
            (ht086-quoted sequence)
            (ht086-quoted less)
            'x))))))

(defun ht086-null-set-p
    (scalar-zero domain-carrier measure set)
  (and
   (ht086-valid-set-p domain-carrier set)
   (equal
    (ht086-unary-value measure set)
    (ht086-ennreal-zero scalar-zero))))

(defun ht086-ae-monotone-p
    (scalar-zero domain-carrier measure sequence less)
  (ht086-null-set-p
   scalar-zero domain-carrier measure
   (ht086-monotone-failure-set
    domain-carrier sequence less)))

(defun ht086-ae-antitone-p
    (scalar-zero domain-carrier measure sequence less)
  (ht086-null-set-p
   scalar-zero domain-carrier measure
   (ht086-antitone-failure-set
    domain-carrier sequence less)))

(defun ht086-pointwise-tendsto-p
    (carrier less sequence limit x)
  (ht086-tendsto-order-p
   carrier less
   (ht086-pointwise-values-function sequence x)
   (ht086-unary-value limit x)))

(defun ht086-tendsto-failure-set
    (domain-carrier codomain-carrier less sequence limit)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (ht086-not-term
      (list 'ht086-pointwise-tendsto-p
            (ht086-quoted codomain-carrier)
            (ht086-quoted less)
            (ht086-quoted sequence)
            (ht086-quoted limit)
            'x))))))

(defun ht086-ae-pointwise-tendsto-p
    (scalar-zero domain-carrier measure
     codomain-carrier less sequence limit)
  (and
   (ht086-function-sequence-p
    domain-carrier codomain-carrier sequence)
   (ht086-function-p
    domain-carrier codomain-carrier limit)
   (ht086-null-set-p
    scalar-zero domain-carrier measure
    (ht086-tendsto-failure-set
     domain-carrier codomain-carrier less sequence limit))))

;; Equality almost everywhere.

(defun ht086-disagreement-set
    (domain-carrier left right)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (ht086-not-term
      (list 'equal
            (ht086-static-apply-term left '(x))
            (ht086-static-apply-term right '(x))))))))

(defun ht086-ae-equal-p
    (scalar-zero domain-carrier measure codomain-carrier left right)
  (and
   (ht086-function-p domain-carrier codomain-carrier left)
   (ht086-function-p domain-carrier codomain-carrier right)
   (ht086-null-set-p
    scalar-zero domain-carrier measure
    (ht086-disagreement-set domain-carrier left right))))

;; Standard measurability is characterized by measurable upper-ray preimages.

(defun ht086-upper-ray-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (ht086-static-apply-term
      less
      (list (ht086-quoted threshold)
            (ht086-static-apply-term function '(x))))))))

(defun ht086-measurable-upper-rays-function
    (domain-carrier measurable codomain-carrier less function)
  (list
   'lambda '(threshold)
   (ht086-implies-term
    (ht086-static-apply-term codomain-carrier '(threshold))
    (ht086-static-apply-term
     measurable
     (list
      (list 'ht086-upper-ray-preimage-set
            (ht086-quoted domain-carrier)
            (ht086-quoted function)
            (ht086-quoted less)
            'threshold))))))

(defun ht086-measurable-function-p
    (domain-carrier measurable codomain-carrier less function)
  (and
   (ht086-function-p domain-carrier codomain-carrier function)
   (ht086-universal-p
    (ht086-measurable-upper-rays-function
     domain-carrier measurable codomain-carrier less function)
    '(threshold))))

(defun ht086-ae-measurable-witness-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (list
   'lambda '(representative)
   (ht086-and-terms
    (list
     (list 'ht086-measurable-function-p
           (ht086-quoted domain-carrier)
           (ht086-quoted measurable)
           (ht086-quoted codomain-carrier)
           (ht086-quoted less)
           'representative)
     (list 'ht086-ae-equal-p
           (ht086-quoted scalar-zero)
           (ht086-quoted domain-carrier)
           (ht086-quoted measure)
           (ht086-quoted codomain-carrier)
           (ht086-quoted function)
           'representative)))))

(defun ht086-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (and
   (ht086-function-p domain-carrier codomain-carrier function)
   (ht086-exists-p
    (ht086-ae-measurable-witness-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
    '(representative))))

;; The lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple functions below the integrand.

(defun ht086-fiber-set (domain-carrier function value)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (list 'equal
           (ht086-static-apply-term function '(x))
           (ht086-quoted value))))))

(defun ht086-values-in-carrier-p (carrier values)
  (if (consp values)
      (and
       (ht086-member-p carrier (car values))
       (ht086-values-in-carrier-p carrier (cdr values)))
    (equal values nil)))

(defun ht086-value-attained-function
    (domain-carrier function value)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (list 'equal
           (ht086-static-apply-term function '(x))
           (ht086-quoted value))))))

(defun ht086-value-attained-p
    (domain-carrier function value)
  (ht086-exists-p
   (ht086-value-attained-function
    domain-carrier function value)
   '(x)))

(defun ht086-values-attained-p
    (domain-carrier function values)
  (if (consp values)
      (and
       (ht086-value-attained-p
        domain-carrier function (car values))
       (ht086-values-attained-p
        domain-carrier function (cdr values)))
    (equal values nil)))

(defun ht086-range-in-values-function
    (domain-carrier function values)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term domain-carrier '(x))
    (list 'member-equal
          (ht086-static-apply-term function '(x))
          (ht086-quoted values)))))

(defun ht086-simple-function-p
    (domain-carrier measurable codomain-carrier less function values)
  (and
   (ht086-measurable-function-p
    domain-carrier measurable codomain-carrier less function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (ht086-values-in-carrier-p codomain-carrier values)
   (ht086-values-attained-p domain-carrier function values)
   (ht086-universal-p
    (ht086-range-in-values-function
     domain-carrier function values)
    '(x))))

(defun ht086-finite-simple-integral
    (domain-carrier measure function values
     scalar-zero scalar-add scalar-multiply)
  (if (consp values)
      (ht086-ennreal-add
       (ht086-ennreal-multiply
        (car values)
        (ht086-unary-value
         measure
         (ht086-fiber-set
          domain-carrier function (car values)))
        scalar-zero scalar-multiply)
       (ht086-finite-simple-integral
        domain-carrier measure function (cdr values)
        scalar-zero scalar-add scalar-multiply)
       scalar-add)
    (ht086-ennreal-zero scalar-zero)))

(defun ht086-simple-below-function
    (domain-carrier simple function scalar-less)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term domain-carrier '(x))
    (list 'ht086-ennreal-less-equal-p
          (ht086-static-apply-term simple '(x))
          (ht086-static-apply-term function '(x))
          (ht086-quoted scalar-less)))))

(defun ht086-simple-below-p
    (domain-carrier simple function scalar-less)
  (ht086-universal-p
   (ht086-simple-below-function
    domain-carrier simple function scalar-less)
   '(x)))

(defun ht086-lintegral-upper-bound-function
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (list
   'lambda '(simple values)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-simple-function-p
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted ennreal-carrier)
            (ht086-quoted ennreal-less)
            'simple 'values)
      (list 'ht086-simple-below-p
            (ht086-quoted domain-carrier)
            'simple
            (ht086-quoted function)
            (ht086-quoted scalar-less))))
    (list 'ht086-ennreal-less-equal-p
          (list 'ht086-finite-simple-integral
                (ht086-quoted domain-carrier)
                (ht086-quoted measure)
                'simple 'values
                (ht086-quoted scalar-zero)
                (ht086-quoted scalar-add)
                (ht086-quoted scalar-multiply))
          (ht086-quoted bound)
          (ht086-quoted scalar-less)))))

(defun ht086-lintegral-upper-bound-p
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (ht086-universal-p
   (ht086-lintegral-upper-bound-function
    domain-carrier measurable measure ennreal-carrier ennreal-less
    function bound scalar-zero scalar-add scalar-multiply scalar-less)
   '(simple values)))

(defun ht086-lintegral-least-upper-bound-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     function value)
  (list
   'lambda '(bound)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-ennreal-p
            'bound
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-less))
      (list 'ht086-lintegral-upper-bound-p
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            (ht086-quoted ennreal-carrier)
            (ht086-quoted ennreal-less)
            (ht086-quoted function)
            'bound
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less))))
    (list 'ht086-ennreal-less-equal-p
          (ht086-quoted value)
          'bound
          (ht086-quoted scalar-less)))))

(defun ht086-lintegral-value-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function value)
  (let ((ennreal-carrier
         (ht086-ennreal-carrier
          scalar-carrier scalar-zero scalar-less))
        (ennreal-less
         (ht086-ennreal-less-function scalar-less)))
    (and
     (ht086-function-p
      domain-carrier ennreal-carrier function)
     (ht086-member-p ennreal-carrier value)
     (ht086-lintegral-upper-bound-p
      domain-carrier measurable measure ennreal-carrier ennreal-less
      function value scalar-zero scalar-add scalar-multiply scalar-less)
     (ht086-universal-p
      (ht086-lintegral-least-upper-bound-function
       scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
       domain-carrier measurable measure ennreal-carrier ennreal-less
       function value)
      '(bound)))))

(defun ht086-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (let ((ennreal-carrier
         (ht086-ennreal-carrier
          scalar-carrier scalar-zero scalar-less)))
    (list
     'lambda '(function)
     (ht086-implies-term
      (list 'ht086-function-p
            (ht086-quoted domain-carrier)
            (ht086-quoted ennreal-carrier)
            'function)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'function
            (ht086-static-apply-term
             lintegral
             (list
              (ht086-quoted domain-carrier)
              (ht086-quoted measurable)
              (ht086-quoted measure)
              'function)))))))

(defun ht086-lintegral-operation-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (and
   (tamep-functionp lintegral)
   (ht086-universal-p
    (ht086-lintegral-values-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    '(function))))

;; Measurable sequences indexed by all natural numbers.

(defun ht086-sequence-measurable-function
    (domain-carrier measurable codomain-carrier less sequence)
  (list
   'lambda '(n)
   (ht086-implies-term
    (list 'natp 'n)
    (list 'ht086-measurable-function-p
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (ht086-quoted codomain-carrier)
          (ht086-quoted less)
          (ht086-static-apply-term sequence '(n))))))

(defun ht086-sequence-measurable-p
    (domain-carrier measurable codomain-carrier less sequence)
  (and
   (ht086-function-sequence-p
    domain-carrier codomain-carrier sequence)
   (ht086-universal-p
    (ht086-sequence-measurable-function
     domain-carrier measurable codomain-carrier less sequence)
    '(n))))

;; Fundamental laws for the lower integral relation.

(defun ht086-pointwise-less-equal-function
    (domain-carrier left right scalar-less)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term domain-carrier '(x))
    (list 'ht086-ennreal-less-equal-p
          (ht086-static-apply-term left '(x))
          (ht086-static-apply-term right '(x))
          (ht086-quoted scalar-less)))))

(defun ht086-pointwise-less-equal-p
    (domain-carrier left right scalar-less)
  (ht086-universal-p
   (ht086-pointwise-less-equal-function
    domain-carrier left right scalar-less)
   '(x)))

(defun ht086-indicator-one-function
    (domain-carrier set scalar-zero scalar-one)
  (list
   'lambda '(x)
   (list 'if
         (ht086-and-terms
          (list
           (ht086-static-apply-term domain-carrier '(x))
           (ht086-static-apply-term set '(x))))
         (list 'ht086-ennreal-finite
               (ht086-quoted scalar-one))
         (list 'ht086-ennreal-zero
               (ht086-quoted scalar-zero)))))

(defun ht086-indicator-function
    (domain-carrier set function scalar-zero)
  (list
   'lambda '(x)
   (list 'if
         (ht086-and-terms
          (list
           (ht086-static-apply-term domain-carrier '(x))
           (ht086-static-apply-term set '(x))))
         (ht086-static-apply-term function '(x))
         (list 'ht086-ennreal-zero
               (ht086-quoted scalar-zero)))))

(defun ht086-pointwise-add-function
    (left right scalar-add)
  (list
   'lambda '(x)
   (list 'ht086-ennreal-add
         (ht086-static-apply-term left '(x))
         (ht086-static-apply-term right '(x))
         (ht086-quoted scalar-add))))

(defun ht086-set-intersection
    (domain-carrier left right)
  (list
   'lambda '(x)
   (ht086-and-terms
    (list
     (ht086-static-apply-term domain-carrier '(x))
     (ht086-static-apply-term left '(x))
     (ht086-static-apply-term right '(x))))))

(defun ht086-restricted-measure
    (domain-carrier measure restricted-set)
  (list
   'lambda '(set)
   (ht086-static-apply-term
    measure
    (list
     (list 'ht086-set-intersection
           (ht086-quoted domain-carrier)
           'set
           (ht086-quoted restricted-set))))))

(defun ht086-lintegral-witness-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function)
  (list
   'lambda '(value)
   (list 'ht086-lintegral-value-p
         (ht086-quoted scalar-carrier)
         (ht086-quoted scalar-zero)
         (ht086-quoted scalar-add)
         (ht086-quoted scalar-multiply)
         (ht086-quoted scalar-less)
         (ht086-quoted domain-carrier)
         (ht086-quoted measurable)
         (ht086-quoted measure)
         (ht086-quoted function)
         'value)))

(defun ht086-lintegral-exists-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function)
  (ht086-exists-p
   (ht086-lintegral-witness-function
    scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
    domain-carrier measurable measure function)
   '(value)))

(defun ht086-lintegral-uniqueness-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function)
  (list
   'lambda '(left-value right-value)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            (ht086-quoted function)
            'left-value)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            (ht086-quoted function)
            'right-value)))
    (list 'equal 'left-value 'right-value))))

(defun ht086-lintegral-unique-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function)
  (ht086-universal-p
   (ht086-lintegral-uniqueness-function
    scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
    domain-carrier measurable measure function)
   '(left-value right-value)))

(defun ht086-existence-uniqueness-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier)
  (list
   'lambda '(function)
   (ht086-implies-term
    (list 'ht086-function-p
          (ht086-quoted domain-carrier)
          (ht086-quoted ennreal-carrier)
          'function)
    (ht086-and-terms
     (list
      (list 'ht086-lintegral-exists-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'function)
      (list 'ht086-lintegral-unique-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'function))))))

(defun ht086-indicator-normalization-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-less domain-carrier measurable measure)
  (list
   'lambda '(set)
   (ht086-implies-term
    (ht086-static-apply-term measurable '(set))
    (list 'ht086-lintegral-value-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-multiply)
          (ht086-quoted scalar-less)
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (ht086-quoted measure)
          (list 'ht086-indicator-one-function
                (ht086-quoted domain-carrier)
                'set
                (ht086-quoted scalar-zero)
                (ht086-quoted scalar-one))
          (ht086-static-apply-term measure '(set))))))

(defun ht086-monotonicity-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure)
  (list
   'lambda '(left right left-value right-value)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-pointwise-less-equal-p
            (ht086-quoted domain-carrier)
            'left 'right
            (ht086-quoted scalar-less))
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'left 'left-value)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'right 'right-value)))
    (list 'ht086-ennreal-less-equal-p
          'left-value 'right-value
          (ht086-quoted scalar-less)))))

(defun ht086-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less)
  (list
   'lambda '(left right left-value right-value)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-measurable-function-p
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted ennreal-carrier)
            (ht086-quoted ennreal-less)
            'left)
      (list 'ht086-measurable-function-p
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted ennreal-carrier)
            (ht086-quoted ennreal-less)
            'right)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'left 'left-value)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'right 'right-value)))
    (list 'ht086-lintegral-value-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-multiply)
          (ht086-quoted scalar-less)
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (ht086-quoted measure)
          (list 'ht086-pointwise-add-function
                'left 'right
                (ht086-quoted scalar-add))
          (list 'ht086-ennreal-add
                'left-value 'right-value
                (ht086-quoted scalar-add))))))

(defun ht086-ae-congruence-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier)
  (list
   'lambda '(left right left-value right-value)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-ae-equal-p
            (ht086-quoted scalar-zero)
            (ht086-quoted domain-carrier)
            (ht086-quoted measure)
            (ht086-quoted ennreal-carrier)
            'left 'right)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'left 'left-value)
      (list 'ht086-lintegral-value-p
            (ht086-quoted scalar-carrier)
            (ht086-quoted scalar-zero)
            (ht086-quoted scalar-add)
            (ht086-quoted scalar-multiply)
            (ht086-quoted scalar-less)
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted measure)
            'right 'right-value)))
    (list 'equal 'left-value 'right-value))))

(defun ht086-natural-range-member-function
    (sequence value)
  (list
   'lambda '(n)
   (ht086-and-terms
    (list
     (list 'natp 'n)
     (list 'equal
           (ht086-static-apply-term sequence '(n))
           (ht086-quoted value))))))

(defun ht086-natural-range-member-p
    (sequence value)
  (ht086-exists-p
   (ht086-natural-range-member-function sequence value)
   '(n)))

(defun ht086-natural-range-set
    (sequence)
  (list
   'lambda '(value)
   (list 'ht086-natural-range-member-p
         (ht086-quoted sequence)
         'value)))

(defun ht086-pointwise-supremum-at-p
    (ennreal-carrier ennreal-less sequence limit x)
  (ht086-least-upper-bound-p
   ennreal-carrier ennreal-less
   (ht086-natural-range-set
    (ht086-pointwise-values-function sequence x))
   (ht086-unary-value limit x)))

(defun ht086-pointwise-supremum-function
    (domain-carrier ennreal-carrier ennreal-less sequence limit)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term domain-carrier '(x))
    (list 'ht086-pointwise-supremum-at-p
          (ht086-quoted ennreal-carrier)
          (ht086-quoted ennreal-less)
          (ht086-quoted sequence)
          (ht086-quoted limit)
          'x))))

(defun ht086-pointwise-supremum-p
    (domain-carrier ennreal-carrier ennreal-less sequence limit)
  (and
   (ht086-function-sequence-p
    domain-carrier ennreal-carrier sequence)
   (ht086-function-p
    domain-carrier ennreal-carrier limit)
   (ht086-universal-p
    (ht086-pointwise-supremum-function
     domain-carrier ennreal-carrier ennreal-less sequence limit)
    '(x))))

(defun ht086-everywhere-monotone-function
    (domain-carrier sequence ennreal-less)
  (list
   'lambda '(x)
   (ht086-implies-term
    (ht086-static-apply-term domain-carrier '(x))
    (list 'ht086-pointwise-monotone-p
          (ht086-quoted sequence)
          (ht086-quoted ennreal-less)
          'x))))

(defun ht086-everywhere-monotone-p
    (domain-carrier sequence ennreal-less)
  (ht086-universal-p
   (ht086-everywhere-monotone-function
    domain-carrier sequence ennreal-less)
   '(x)))

(defun ht086-sequence-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure sequence integral-values)
  (list
   'lambda '(n)
   (ht086-implies-term
    (list 'natp 'n)
    (list 'ht086-lintegral-value-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-multiply)
          (ht086-quoted scalar-less)
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (ht086-quoted measure)
          (ht086-static-apply-term sequence '(n))
          (ht086-static-apply-term integral-values '(n))))))

(defun ht086-sequence-lintegral-values-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure sequence integral-values)
  (ht086-universal-p
   (ht086-sequence-lintegral-values-function
    scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
    domain-carrier measurable measure sequence integral-values)
   '(n)))

(defun ht086-monotone-convergence-witness-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     sequence limit)
  (list
   'lambda '(integral-values limit-value)
   (ht086-and-terms
    (list
     (list 'ht086-natural-values-p
           (ht086-quoted ennreal-carrier)
           'integral-values)
     (list 'ht086-sequence-lintegral-values-p
           (ht086-quoted scalar-carrier)
           (ht086-quoted scalar-zero)
           (ht086-quoted scalar-add)
           (ht086-quoted scalar-multiply)
           (ht086-quoted scalar-less)
           (ht086-quoted domain-carrier)
           (ht086-quoted measurable)
           (ht086-quoted measure)
           (ht086-quoted sequence)
           'integral-values)
     (list 'ht086-lintegral-value-p
           (ht086-quoted scalar-carrier)
           (ht086-quoted scalar-zero)
           (ht086-quoted scalar-add)
           (ht086-quoted scalar-multiply)
           (ht086-quoted scalar-less)
           (ht086-quoted domain-carrier)
           (ht086-quoted measurable)
           (ht086-quoted measure)
           (ht086-quoted limit)
           'limit-value)
     (list 'ht086-least-upper-bound-p
           (ht086-quoted ennreal-carrier)
           (ht086-quoted ennreal-less)
           (list 'ht086-natural-range-set
                 'integral-values)
           'limit-value)))))

(defun ht086-monotone-convergence-witness-exists-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     sequence limit)
  (ht086-exists-p
   (ht086-monotone-convergence-witness-function
    scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
    domain-carrier measurable measure ennreal-carrier ennreal-less
    sequence limit)
   '(integral-values limit-value)))

(defun ht086-monotone-convergence-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less)
  (list
   'lambda '(sequence limit)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (list 'ht086-sequence-measurable-p
            (ht086-quoted domain-carrier)
            (ht086-quoted measurable)
            (ht086-quoted ennreal-carrier)
            (ht086-quoted ennreal-less)
            'sequence)
      (list 'ht086-everywhere-monotone-p
            (ht086-quoted domain-carrier)
            'sequence
            (ht086-quoted ennreal-less))
      (list 'ht086-pointwise-supremum-p
            (ht086-quoted domain-carrier)
            (ht086-quoted ennreal-carrier)
            (ht086-quoted ennreal-less)
            'sequence 'limit)))
    (list 'ht086-monotone-convergence-witness-exists-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-multiply)
          (ht086-quoted scalar-less)
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (ht086-quoted measure)
          (ht086-quoted ennreal-carrier)
          (ht086-quoted ennreal-less)
          'sequence 'limit))))

(defun ht086-restricted-measure-law-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     domain-carrier measurable measure)
  (list
   'lambda '(set)
   (ht086-implies-term
    (ht086-static-apply-term measurable '(set))
    (list 'ht086-measure-space-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-less)
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (list 'ht086-restricted-measure
                (ht086-quoted domain-carrier)
                (ht086-quoted measure)
                'set)))))

(defun ht086-restriction-identity-witness-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure set function)
  (list
   'lambda '(indicator-value restricted-value)
   (ht086-and-terms
    (list
     (list 'ht086-lintegral-value-p
           (ht086-quoted scalar-carrier)
           (ht086-quoted scalar-zero)
           (ht086-quoted scalar-add)
           (ht086-quoted scalar-multiply)
           (ht086-quoted scalar-less)
           (ht086-quoted domain-carrier)
           (ht086-quoted measurable)
           (ht086-quoted measure)
           (list 'ht086-indicator-function
                 (ht086-quoted domain-carrier)
                 (ht086-quoted set)
                 (ht086-quoted function)
                 (ht086-quoted scalar-zero))
           'indicator-value)
     (list 'ht086-lintegral-value-p
           (ht086-quoted scalar-carrier)
           (ht086-quoted scalar-zero)
           (ht086-quoted scalar-add)
           (ht086-quoted scalar-multiply)
           (ht086-quoted scalar-less)
           (ht086-quoted domain-carrier)
           (ht086-quoted measurable)
           (list 'ht086-restricted-measure
                 (ht086-quoted domain-carrier)
                 (ht086-quoted measure)
                 (ht086-quoted set))
           (ht086-quoted function)
           'restricted-value)
     (list 'equal 'indicator-value 'restricted-value)))))

(defun ht086-restriction-identity-witness-exists-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure set function)
  (ht086-exists-p
   (ht086-restriction-identity-witness-function
    scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
    domain-carrier measurable measure set function)
   '(indicator-value restricted-value)))

(defun ht086-restriction-identity-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier)
  (list
   'lambda '(set function)
   (ht086-implies-term
    (ht086-and-terms
     (list
      (ht086-static-apply-term measurable '(set))
      (list 'ht086-function-p
            (ht086-quoted domain-carrier)
            (ht086-quoted ennreal-carrier)
            'function)))
    (list 'ht086-restriction-identity-witness-exists-p
          (ht086-quoted scalar-carrier)
          (ht086-quoted scalar-zero)
          (ht086-quoted scalar-add)
          (ht086-quoted scalar-multiply)
          (ht086-quoted scalar-less)
          (ht086-quoted domain-carrier)
          (ht086-quoted measurable)
          (ht086-quoted measure)
          'set 'function))))

(defun hundred-theorems-086-lebesgue-measure-and-integration-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     domain-carrier measurable measure)
  (let ((ennreal-carrier
         (ht086-ennreal-carrier
          real-carrier real-zero real-less))
        (ennreal-less
         (ht086-ennreal-less-function real-less)))
    (implies
     (and
      (ht086-real-field-p
       real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less real-supremum)
      (ht086-measure-space-p
       real-carrier real-zero real-add real-less
       domain-carrier measurable measure))
     (and
      (ht086-universal-p
       (ht086-existence-uniqueness-function
        real-carrier real-zero real-add real-multiply real-less
        domain-carrier measurable measure ennreal-carrier)
       '(function))
      (ht086-universal-p
       (ht086-indicator-normalization-function
        real-carrier real-zero real-one real-add real-multiply
        real-less domain-carrier measurable measure)
       '(set))
      (ht086-universal-p
       (ht086-monotonicity-function
        real-carrier real-zero real-add real-multiply real-less
        domain-carrier measurable measure)
       '(left right left-value right-value))
      (ht086-universal-p
       (ht086-additivity-function
        real-carrier real-zero real-add real-multiply real-less
        domain-carrier measurable measure ennreal-carrier ennreal-less)
       '(left right left-value right-value))
      (ht086-universal-p
       (ht086-ae-congruence-function
        real-carrier real-zero real-add real-multiply real-less
        domain-carrier measurable measure ennreal-carrier)
       '(left right left-value right-value))
      (ht086-universal-p
       (ht086-monotone-convergence-function
        real-carrier real-zero real-add real-multiply real-less
        domain-carrier measurable measure ennreal-carrier ennreal-less)
       '(sequence limit))
      (ht086-universal-p
       (ht086-restricted-measure-law-function
        real-carrier real-zero real-add real-less
        domain-carrier measurable measure)
       '(set))
      (ht086-universal-p
       (ht086-restriction-identity-function
        real-carrier real-zero real-add real-multiply real-less
        domain-carrier measurable measure ennreal-carrier)
       '(set function))))))

(value-triple :itpeval-statement-checked)
:q
