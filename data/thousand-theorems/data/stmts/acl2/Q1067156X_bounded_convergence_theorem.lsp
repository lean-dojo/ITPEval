;; Statement-only formalization of thousand-theorems corpus artifact Q1067156X,
;; "Bounded convergence theorem": a uniformly eventually almost-everywhere
;; bounded family of bounded continuous nonnegative-real functions, converging
;; almost everywhere along a countably generated filter on a finite measure
;; space, has lower integrals converging to the lower integral of its limit;
;; the natural-number, everywhere-bounded specialization is included as well.
;; This file contains no proof.

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
;; target functions take finite nonnegative values. Topologies and filters are
;; represented extensionally as families of sets. Tendsto is encoded by
;; eventual membership in every strict lower and upper order neighborhood.

(defun q1067156x-quoted (object)
  (list 'quote object))

(defun q1067156x-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q1067156x-term-list (cdr terms)))
    (q1067156x-quoted nil)))

(defun q1067156x-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (q1067156x-term-list arguments)))

(defun q1067156x-static-apply-term (function arguments)
  (q1067156x-apply-term
   (q1067156x-quoted function)
   arguments))

(defun q1067156x-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q1067156x-and-terms (cdr terms))
            (q1067156x-quoted nil))
    (q1067156x-quoted t)))

(defun q1067156x-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q1067156x-quoted t)
            (q1067156x-or-terms (cdr terms)))
    (q1067156x-quoted nil)))

(defun q1067156x-not-term (term)
  (list 'if term
        (q1067156x-quoted nil)
        (q1067156x-quoted t)))

(defun q1067156x-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q1067156x-quoted t)))

(defun q1067156x-iff-term (left right)
  (list 'if left
        (list 'if right
              (q1067156x-quoted t)
              (q1067156x-quoted nil))
        (list 'if right
              (q1067156x-quoted nil)
              (q1067156x-quoted t))))

(defun q1067156x-true-function (formals)
  (list 'lambda formals (q1067156x-quoted t)))

(defun q1067156x-false-function (formals)
  (list 'lambda formals (q1067156x-quoted nil)))

(defun q1067156x-universal-p (function formals)
  (let ((always-true (q1067156x-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun q1067156x-exists-p (function formals)
  (let ((always-false (q1067156x-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun q1067156x-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q1067156x-unary-value (function object)
  (apply$ function (list object)))

(defun q1067156x-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun q1067156x-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term carrier '(x))
      (q1067156x-static-apply-term left '(x))))
    (q1067156x-static-apply-term right '(x)))))

(defun q1067156x-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q1067156x-universal-p
    (q1067156x-set-subset-function carrier left right)
    '(x))))

(defun q1067156x-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q1067156x-set-subset-p carrier set carrier)))

(defun q1067156x-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-static-apply-term carrier '(x))
    (q1067156x-iff-term
     (q1067156x-static-apply-term left '(x))
     (q1067156x-static-apply-term right '(x))))))

(defun q1067156x-set-equiv-p (carrier left right)
  (and
   (q1067156x-valid-set-p carrier left)
   (q1067156x-valid-set-p carrier right)
   (q1067156x-universal-p
    (q1067156x-set-equiv-function carrier left right)
    '(x))))

(defun q1067156x-empty-set ()
  (list 'lambda '(x) (q1067156x-quoted nil)))

(defun q1067156x-full-set (carrier)
  (list 'lambda '(x)
        (q1067156x-static-apply-term carrier '(x))))

(defun q1067156x-complement-set (carrier set)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term carrier '(x))
     (q1067156x-not-term
      (q1067156x-static-apply-term set '(x)))))))

(defun q1067156x-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-static-apply-term domain-carrier '(x))
    (q1067156x-static-apply-term
     codomain-carrier
     (list (q1067156x-static-apply-term function '(x)))))))

(defun q1067156x-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (q1067156x-universal-p
    (q1067156x-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q1067156x-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (q1067156x-static-apply-term add '(x y)))
         (yz-add (q1067156x-static-apply-term add '(y z)))
         (xy-mul (q1067156x-static-apply-term multiply '(x y)))
         (yz-mul (q1067156x-static-apply-term multiply '(y z)))
         (neg-x (q1067156x-static-apply-term negate '(x)))
         (inv-x (q1067156x-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (q1067156x-implies-term
      (q1067156x-and-terms
       (list
        (q1067156x-static-apply-term carrier '(x))
        (q1067156x-static-apply-term carrier '(y))
        (q1067156x-static-apply-term carrier '(z))))
      (q1067156x-and-terms
       (list
        (q1067156x-static-apply-term carrier (list xy-add))
        (q1067156x-static-apply-term carrier (list xy-mul))
        (q1067156x-static-apply-term carrier (list neg-x))
        (q1067156x-static-apply-term carrier (list inv-x))
        (list 'equal
              (q1067156x-static-apply-term add (list xy-add 'z))
              (q1067156x-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (q1067156x-static-apply-term add '(y x)))
        (list 'equal
              (q1067156x-static-apply-term
               add (list 'x (q1067156x-quoted zero)))
              'x)
        (list 'equal
              (q1067156x-static-apply-term add (list 'x neg-x))
              (q1067156x-quoted zero))
        (list 'equal
              (q1067156x-static-apply-term multiply (list xy-mul 'z))
              (q1067156x-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (q1067156x-static-apply-term multiply '(y x)))
        (list 'equal
              (q1067156x-static-apply-term
               multiply (list 'x (q1067156x-quoted one)))
              'x)
        (q1067156x-implies-term
         (list 'equal 'x (q1067156x-quoted zero))
         (list 'equal inv-x (q1067156x-quoted zero)))
        (q1067156x-implies-term
         (q1067156x-not-term
          (list 'equal 'x (q1067156x-quoted zero)))
         (list 'equal
               (q1067156x-static-apply-term
                multiply (list 'x inv-x))
               (q1067156x-quoted one)))
        (list 'equal
              (q1067156x-static-apply-term multiply (list 'x yz-add))
              (q1067156x-static-apply-term
               add
               (list
                (q1067156x-static-apply-term multiply '(x y))
                (q1067156x-static-apply-term multiply '(x z)))))))))))

(defun q1067156x-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (q1067156x-static-apply-term less '(x y)))
        (yx (q1067156x-static-apply-term less '(y x)))
        (yz (q1067156x-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (q1067156x-implies-term
      (q1067156x-and-terms
       (list
        (q1067156x-static-apply-term carrier '(x))
        (q1067156x-static-apply-term carrier '(y))
        (q1067156x-static-apply-term carrier '(z))))
      (q1067156x-and-terms
       (list
        (q1067156x-not-term
         (q1067156x-static-apply-term less '(x x)))
        (q1067156x-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q1067156x-implies-term
         (q1067156x-and-terms (list xy yz))
         (q1067156x-static-apply-term less '(x z)))
        (q1067156x-implies-term
         xy
         (q1067156x-static-apply-term
          less
          (list
           (q1067156x-static-apply-term add '(x z))
           (q1067156x-static-apply-term add '(y z)))))
        (q1067156x-implies-term
         (q1067156x-and-terms
          (list
           (q1067156x-static-apply-term
            less (list (q1067156x-quoted zero) 'x))
           (q1067156x-static-apply-term
            less (list (q1067156x-quoted zero) 'y))))
         (q1067156x-static-apply-term
          less
          (list
           (q1067156x-quoted zero)
           (q1067156x-static-apply-term multiply '(x y)))))))))))

(defun q1067156x-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term carrier '(x))
      (q1067156x-static-apply-term set '(x))))
    (q1067156x-not-term
     (q1067156x-static-apply-term
      less (list (q1067156x-quoted upper) 'x))))))

(defun q1067156x-upper-bound-p
    (carrier less set upper)
  (and
   (q1067156x-member-p carrier upper)
   (q1067156x-valid-set-p carrier set)
   (q1067156x-universal-p
    (q1067156x-upper-bound-function carrier less set upper)
    '(x))))

(defun q1067156x-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term carrier '(x))
     (q1067156x-static-apply-term set '(x))))))

(defun q1067156x-set-nonempty-p (carrier set)
  (and
   (q1067156x-valid-set-p carrier set)
   (q1067156x-exists-p
    (q1067156x-set-nonempty-function carrier set)
    '(x))))

(defun q1067156x-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'q1067156x-upper-bound-p
         (q1067156x-quoted carrier)
         (q1067156x-quoted less)
         (q1067156x-quoted set)
         'upper)))

(defun q1067156x-bounded-above-p (carrier less set)
  (q1067156x-exists-p
   (q1067156x-bounded-above-function carrier less set)
   '(upper)))

(defun q1067156x-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (q1067156x-implies-term
    (list 'q1067156x-upper-bound-p
          (q1067156x-quoted carrier)
          (q1067156x-quoted less)
          (q1067156x-quoted set)
          'upper)
    (q1067156x-not-term
     (q1067156x-static-apply-term
      less (list 'upper (q1067156x-quoted supremum)))))))

(defun q1067156x-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q1067156x-upper-bound-p carrier less set supremum)
   (q1067156x-universal-p
    (q1067156x-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q1067156x-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-valid-set-p
            (q1067156x-quoted carrier) 'set)
      (list 'q1067156x-set-nonempty-p
            (q1067156x-quoted carrier) 'set)
      (list 'q1067156x-bounded-above-p
            (q1067156x-quoted carrier)
            (q1067156x-quoted less)
            'set)))
    (list 'q1067156x-least-upper-bound-p
          (q1067156x-quoted carrier)
          (q1067156x-quoted less)
          'set
          (q1067156x-static-apply-term
           supremum-operation '(set))))))

(defun q1067156x-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q1067156x-member-p carrier zero)
   (q1067156x-member-p carrier one)
   (not (equal zero one))
   (q1067156x-universal-p
    (q1067156x-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q1067156x-universal-p
    (q1067156x-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q1067156x-universal-p
    (q1067156x-completeness-function
     carrier less supremum)
    '(set))
   (q1067156x-binary-value less zero one)))

(defun q1067156x-scalar-absolute-value
    (less zero negate value)
  (if (q1067156x-binary-value less value zero)
      (q1067156x-unary-value negate value)
    value))
;; Sigma algebras.

(defun q1067156x-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (q1067156x-implies-term
    (list 'q1067156x-set-equiv-p
          (q1067156x-quoted carrier)
          'left 'right)
    (q1067156x-iff-term
     (q1067156x-static-apply-term family '(left))
     (q1067156x-static-apply-term family '(right))))))

(defun q1067156x-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (q1067156x-static-apply-term family '(set))
    (list 'q1067156x-valid-set-p
          (q1067156x-quoted carrier)
          'set))))

(defun q1067156x-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q1067156x-universal-p
    (q1067156x-family-extensional-function carrier family)
    '(left right))
   (q1067156x-universal-p
    (q1067156x-family-members-valid-function carrier family)
    '(set))))

(defun q1067156x-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (q1067156x-and-terms
    (list
     (list 'natp 'n)
     (q1067156x-apply-term
      (q1067156x-static-apply-term sequence '(n))
      (list (q1067156x-quoted x)))))))

(defun q1067156x-sequence-union-member-p (sequence x)
  (q1067156x-exists-p
   (q1067156x-sequence-union-member-function sequence x)
   '(n)))

(defun q1067156x-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term carrier '(x))
     (list 'q1067156x-sequence-union-member-p
           (q1067156x-quoted sequence)
           'x)))))

(defun q1067156x-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (list 'q1067156x-valid-set-p
          (q1067156x-quoted carrier)
          (q1067156x-static-apply-term sequence '(n))))))

(defun q1067156x-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (q1067156x-universal-p
    (q1067156x-sequence-of-sets-function carrier sequence)
    '(n))))

(defun q1067156x-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (q1067156x-static-apply-term
     family
     (list (q1067156x-static-apply-term sequence '(n)))))))

(defun q1067156x-sequence-members-family-p
    (carrier family sequence)
  (and
   (q1067156x-sequence-of-sets-p carrier sequence)
   (q1067156x-universal-p
    (q1067156x-sequence-members-family-function family sequence)
    '(n))))

(defun q1067156x-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (q1067156x-static-apply-term family '(set))
    (q1067156x-static-apply-term
     family
     (list
      (list 'q1067156x-complement-set
            (q1067156x-quoted carrier)
            'set))))))

(defun q1067156x-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (q1067156x-implies-term
    (list 'q1067156x-sequence-members-family-p
          (q1067156x-quoted carrier)
          (q1067156x-quoted family)
          'sequence)
    (q1067156x-static-apply-term
     family
     (list
      (list 'q1067156x-sequence-union-set
            (q1067156x-quoted carrier)
            'sequence))))))

(defun q1067156x-sigma-algebra-p (carrier family)
  (and
   (q1067156x-family-of-sets-p carrier family)
   (q1067156x-member-p family (q1067156x-empty-set))
   (q1067156x-universal-p
    (q1067156x-sigma-complement-function carrier family)
    '(set))
   (q1067156x-universal-p
    (q1067156x-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun q1067156x-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :q1067156x-top)
   (and
    (consp value)
    (equal (car value) :q1067156x-finite)
    (q1067156x-member-p scalar-carrier (cdr value))
    (not
     (q1067156x-binary-value scalar-less (cdr value) scalar-zero)))))

(defun q1067156x-ennreal-finite (value)
  (cons :q1067156x-finite value))

(defun q1067156x-ennreal-zero (scalar-zero)
  (q1067156x-ennreal-finite scalar-zero))

(defun q1067156x-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :q1067156x-top) nil)
   ((equal right :q1067156x-top) t)
   (t
    (q1067156x-binary-value scalar-less (cdr left) (cdr right)))))

(defun q1067156x-ennreal-less-equal-p (left right scalar-less)
  (not (q1067156x-ennreal-less-p right left scalar-less)))

(defun q1067156x-ennreal-add (left right scalar-add)
  (if (or (equal left :q1067156x-top)
          (equal right :q1067156x-top))
      :q1067156x-top
    (q1067156x-ennreal-finite
     (q1067156x-binary-value scalar-add (cdr left) (cdr right)))))

(defun q1067156x-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (q1067156x-ennreal-zero scalar-zero))
        (equal right (q1067156x-ennreal-zero scalar-zero)))
    (q1067156x-ennreal-zero scalar-zero))
   ((or (equal left :q1067156x-top)
        (equal right :q1067156x-top))
    :q1067156x-top)
   (t
    (q1067156x-ennreal-finite
     (q1067156x-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun q1067156x-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1067156x-ennreal-zero scalar-zero)
    (q1067156x-ennreal-add
     (q1067156x-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (q1067156x-unary-value sequence (- count 1))
     scalar-add)))

(defun q1067156x-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (q1067156x-implies-term
    (list 'natp 'count)
    (list 'q1067156x-ennreal-less-equal-p
          (list 'q1067156x-finite-ennreal-sum
                (q1067156x-quoted sequence)
                'count
                (q1067156x-quoted scalar-zero)
                (q1067156x-quoted scalar-add))
          (q1067156x-quoted total)
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (q1067156x-universal-p
   (q1067156x-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun q1067156x-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-ennreal-p
            'bound
            (q1067156x-quoted scalar-carrier)
            (q1067156x-quoted scalar-zero)
            (q1067156x-quoted scalar-less))
      (list 'q1067156x-sum-upper-bound-p
            (q1067156x-quoted sequence)
            'bound
            (q1067156x-quoted scalar-zero)
            (q1067156x-quoted scalar-add)
            (q1067156x-quoted scalar-less))))
    (list 'q1067156x-ennreal-less-equal-p
          (q1067156x-quoted total)
          'bound
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (q1067156x-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (q1067156x-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (q1067156x-universal-p
    (q1067156x-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun q1067156x-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (q1067156x-implies-term
    (list 'q1067156x-set-equiv-p
          (q1067156x-quoted carrier)
          'left 'right)
    (list 'equal
          (q1067156x-static-apply-term measure '(left))
          (q1067156x-static-apply-term measure '(right))))))

(defun q1067156x-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (list 'q1067156x-valid-set-p
          (q1067156x-quoted carrier)
          'set)
    (list 'q1067156x-ennreal-p
          (q1067156x-static-apply-term measure '(set))
          (q1067156x-quoted scalar-carrier)
          (q1067156x-quoted scalar-zero)
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (q1067156x-static-apply-term
    measure
    (list (q1067156x-static-apply-term sequence '(n))))))

(defun q1067156x-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-static-apply-term carrier '(x))
    (q1067156x-not-term
     (q1067156x-and-terms
      (list
       (q1067156x-static-apply-term left '(x))
       (q1067156x-static-apply-term right '(x))))))))

(defun q1067156x-disjoint-sets-p (carrier left right)
  (q1067156x-universal-p
   (q1067156x-disjoint-sets-function carrier left right)
   '(x)))

(defun q1067156x-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (q1067156x-not-term (list 'equal 'm 'n))))
    (list 'q1067156x-disjoint-sets-p
          (q1067156x-quoted carrier)
          (q1067156x-static-apply-term sequence '(m))
          (q1067156x-static-apply-term sequence '(n))))))

(defun q1067156x-pairwise-disjoint-p (carrier sequence)
  (q1067156x-universal-p
   (q1067156x-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun q1067156x-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-sequence-members-family-p
            (q1067156x-quoted carrier)
            (q1067156x-quoted measurable)
            'sequence)
      (list 'q1067156x-pairwise-disjoint-p
            (q1067156x-quoted carrier)
            'sequence)))
    (list 'q1067156x-countable-sum-p
          (list 'q1067156x-measure-sequence-values
                (q1067156x-quoted measure)
                'sequence)
          (q1067156x-static-apply-term
           measure
           (list
            (list 'q1067156x-sequence-union-set
                  (q1067156x-quoted carrier)
                  'sequence)))
          (q1067156x-quoted scalar-carrier)
          (q1067156x-quoted scalar-zero)
          (q1067156x-quoted scalar-add)
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term measurable '(superset))
      (list 'q1067156x-set-subset-p
            (q1067156x-quoted carrier)
            (q1067156x-quoted set)
            'superset)))
    (list 'q1067156x-ennreal-less-equal-p
          (q1067156x-quoted lower)
          (q1067156x-static-apply-term measure '(superset))
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (q1067156x-universal-p
   (q1067156x-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun q1067156x-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-ennreal-p
            'lower
            (q1067156x-quoted scalar-carrier)
            (q1067156x-quoted scalar-zero)
            (q1067156x-quoted scalar-less))
      (list 'q1067156x-measurable-superset-lower-bound-p
            (q1067156x-quoted carrier)
            (q1067156x-quoted measurable)
            (q1067156x-quoted measure)
            (q1067156x-quoted set)
            'lower
            (q1067156x-quoted scalar-less))))
    (list 'q1067156x-ennreal-less-equal-p
          'lower
          (q1067156x-static-apply-term
           measure (list (q1067156x-quoted set)))
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (q1067156x-valid-set-p carrier set)
   (q1067156x-measurable-superset-lower-bound-p
    carrier measurable measure set
    (q1067156x-unary-value measure set)
    scalar-less)
   (q1067156x-universal-p
    (q1067156x-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun q1067156x-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (list 'q1067156x-valid-set-p
          (q1067156x-quoted carrier)
          'set)
    (list 'q1067156x-outer-value-p
          (q1067156x-quoted scalar-carrier)
          (q1067156x-quoted scalar-zero)
          (q1067156x-quoted scalar-less)
          (q1067156x-quoted carrier)
          (q1067156x-quoted measurable)
          (q1067156x-quoted measure)
          'set))))

(defun q1067156x-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (q1067156x-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (q1067156x-universal-p
    (q1067156x-measure-extensional-function carrier measure)
    '(left right))
   (q1067156x-universal-p
    (q1067156x-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (equal
    (q1067156x-unary-value measure (q1067156x-empty-set))
    (q1067156x-ennreal-zero scalar-zero))
   (q1067156x-universal-p
    (q1067156x-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (q1067156x-universal-p
    (q1067156x-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; Function sequences and order-topological convergence.

(defun q1067156x-ennreal-carrier
    (scalar-carrier scalar-zero scalar-less)
  (list
   'lambda '(value)
   (list 'q1067156x-ennreal-p
         'value
         (q1067156x-quoted scalar-carrier)
         (q1067156x-quoted scalar-zero)
         (q1067156x-quoted scalar-less))))

(defun q1067156x-ennreal-less-function (scalar-less)
  (list
   'lambda '(left right)
   (list 'q1067156x-ennreal-less-p
         'left 'right
         (q1067156x-quoted scalar-less))))

(defun q1067156x-less-equal-term (less left right)
  (q1067156x-not-term
   (q1067156x-static-apply-term less (list right left))))

(defun q1067156x-sequence-term-function (sequence n)
  (list
   'lambda '(x)
   (q1067156x-apply-term
    (q1067156x-static-apply-term
     sequence (list (q1067156x-quoted n)))
    '(x))))

(defun q1067156x-function-sequence-values-function
    (domain-carrier codomain-carrier sequence)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (list 'q1067156x-function-p
          (q1067156x-quoted domain-carrier)
          (q1067156x-quoted codomain-carrier)
          (q1067156x-static-apply-term sequence '(n))))))

(defun q1067156x-function-sequence-p
    (domain-carrier codomain-carrier sequence)
  (and
   (tamep-functionp sequence)
   (q1067156x-universal-p
    (q1067156x-function-sequence-values-function
     domain-carrier codomain-carrier sequence)
    '(n))))

(defun q1067156x-natural-values-function
    (carrier values)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (q1067156x-static-apply-term
     carrier
     (list (q1067156x-static-apply-term values '(n)))))))

(defun q1067156x-natural-values-p (carrier values)
  (and
   (tamep-functionp values)
   (q1067156x-universal-p
    (q1067156x-natural-values-function carrier values)
    '(n))))

(defun q1067156x-eventual-lower-function
    (values less lower start)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q1067156x-quoted start) 'n)))
    (q1067156x-static-apply-term
     less
     (list
      (q1067156x-quoted lower)
      (q1067156x-static-apply-term values '(n)))))))

(defun q1067156x-eventual-lower-p
    (values less lower start)
  (and
   (natp start)
   (q1067156x-universal-p
    (q1067156x-eventual-lower-function
     values less lower start)
    '(n))))

(defun q1067156x-lower-start-function
    (values less lower)
  (list
   'lambda '(start)
   (list 'q1067156x-eventual-lower-p
         (q1067156x-quoted values)
         (q1067156x-quoted less)
         (q1067156x-quoted lower)
         'start)))

(defun q1067156x-eventually-above-p
    (values less lower)
  (q1067156x-exists-p
   (q1067156x-lower-start-function values less lower)
   '(start)))

(defun q1067156x-eventual-upper-function
    (values less upper start)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q1067156x-quoted start) 'n)))
    (q1067156x-static-apply-term
     less
     (list
      (q1067156x-static-apply-term values '(n))
      (q1067156x-quoted upper))))))

(defun q1067156x-eventual-upper-p
    (values less upper start)
  (and
   (natp start)
   (q1067156x-universal-p
    (q1067156x-eventual-upper-function
     values less upper start)
    '(n))))

(defun q1067156x-upper-start-function
    (values less upper)
  (list
   'lambda '(start)
   (list 'q1067156x-eventual-upper-p
         (q1067156x-quoted values)
         (q1067156x-quoted less)
         (q1067156x-quoted upper)
         'start)))

(defun q1067156x-eventually-below-p
    (values less upper)
  (q1067156x-exists-p
   (q1067156x-upper-start-function values less upper)
   '(start)))

(defun q1067156x-order-convergence-bound-function
    (carrier less values limit)
  (list
   'lambda '(bound)
   (q1067156x-implies-term
    (q1067156x-static-apply-term carrier '(bound))
    (q1067156x-and-terms
     (list
      (q1067156x-implies-term
       (q1067156x-static-apply-term
        less (list 'bound (q1067156x-quoted limit)))
       (list 'q1067156x-eventually-above-p
             (q1067156x-quoted values)
             (q1067156x-quoted less)
             'bound))
      (q1067156x-implies-term
       (q1067156x-static-apply-term
        less (list (q1067156x-quoted limit) 'bound))
       (list 'q1067156x-eventually-below-p
             (q1067156x-quoted values)
             (q1067156x-quoted less)
             'bound)))))))

(defun q1067156x-tendsto-order-p
    (carrier less values limit)
  (and
   (tamep-functionp carrier)
   (tamep-functionp less)
   (q1067156x-natural-values-p carrier values)
   (q1067156x-member-p carrier limit)
   (q1067156x-universal-p
    (q1067156x-order-convergence-bound-function
     carrier less values limit)
    '(bound))))

;; Pointwise monotonicity and almost-everywhere order convergence.

(defun q1067156x-pointwise-values-function (sequence x)
  (list
   'lambda '(n)
   (q1067156x-apply-term
    (q1067156x-static-apply-term sequence '(n))
    (list (q1067156x-quoted x)))))

(defun q1067156x-pointwise-monotone-index-function
    (sequence less x)
  (let ((left
         (q1067156x-apply-term
          (q1067156x-static-apply-term sequence '(n))
          (list (q1067156x-quoted x))))
        (right
         (q1067156x-apply-term
          (q1067156x-static-apply-term sequence '(m))
          (list (q1067156x-quoted x)))))
    (list
     'lambda '(n m)
     (q1067156x-implies-term
      (q1067156x-and-terms
       (list
        (list 'natp 'n)
        (list 'natp 'm)
        (list '<= 'n 'm)))
      (q1067156x-less-equal-term less left right)))))

(defun q1067156x-pointwise-monotone-p
    (sequence less x)
  (q1067156x-universal-p
   (q1067156x-pointwise-monotone-index-function
    sequence less x)
   '(n m)))

(defun q1067156x-pointwise-antitone-index-function
    (sequence less x)
  (let ((left
         (q1067156x-apply-term
          (q1067156x-static-apply-term sequence '(m))
          (list (q1067156x-quoted x))))
        (right
         (q1067156x-apply-term
          (q1067156x-static-apply-term sequence '(n))
          (list (q1067156x-quoted x)))))
    (list
     'lambda '(n m)
     (q1067156x-implies-term
      (q1067156x-and-terms
       (list
        (list 'natp 'n)
        (list 'natp 'm)
        (list '<= 'n 'm)))
      (q1067156x-less-equal-term less left right)))))

(defun q1067156x-pointwise-antitone-p
    (sequence less x)
  (q1067156x-universal-p
   (q1067156x-pointwise-antitone-index-function
    sequence less x)
   '(n m)))

(defun q1067156x-monotone-failure-set
    (domain-carrier sequence less)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-not-term
      (list 'q1067156x-pointwise-monotone-p
            (q1067156x-quoted sequence)
            (q1067156x-quoted less)
            'x))))))

(defun q1067156x-antitone-failure-set
    (domain-carrier sequence less)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-not-term
      (list 'q1067156x-pointwise-antitone-p
            (q1067156x-quoted sequence)
            (q1067156x-quoted less)
            'x))))))

(defun q1067156x-null-set-p
    (scalar-zero domain-carrier measure set)
  (and
   (q1067156x-valid-set-p domain-carrier set)
   (equal
    (q1067156x-unary-value measure set)
    (q1067156x-ennreal-zero scalar-zero))))

(defun q1067156x-ae-monotone-p
    (scalar-zero domain-carrier measure sequence less)
  (q1067156x-null-set-p
   scalar-zero domain-carrier measure
   (q1067156x-monotone-failure-set
    domain-carrier sequence less)))

(defun q1067156x-ae-antitone-p
    (scalar-zero domain-carrier measure sequence less)
  (q1067156x-null-set-p
   scalar-zero domain-carrier measure
   (q1067156x-antitone-failure-set
    domain-carrier sequence less)))

(defun q1067156x-pointwise-tendsto-p
    (carrier less sequence limit x)
  (q1067156x-tendsto-order-p
   carrier less
   (q1067156x-pointwise-values-function sequence x)
   (q1067156x-unary-value limit x)))

(defun q1067156x-tendsto-failure-set
    (domain-carrier codomain-carrier less sequence limit)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-not-term
      (list 'q1067156x-pointwise-tendsto-p
            (q1067156x-quoted codomain-carrier)
            (q1067156x-quoted less)
            (q1067156x-quoted sequence)
            (q1067156x-quoted limit)
            'x))))))

(defun q1067156x-ae-pointwise-tendsto-p
    (scalar-zero domain-carrier measure
     codomain-carrier less sequence limit)
  (and
   (q1067156x-function-sequence-p
    domain-carrier codomain-carrier sequence)
   (q1067156x-function-p
    domain-carrier codomain-carrier limit)
   (q1067156x-null-set-p
    scalar-zero domain-carrier measure
    (q1067156x-tendsto-failure-set
     domain-carrier codomain-carrier less sequence limit))))

;; Equality almost everywhere.

(defun q1067156x-disagreement-set
    (domain-carrier left right)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-not-term
      (list 'equal
            (q1067156x-static-apply-term left '(x))
            (q1067156x-static-apply-term right '(x))))))))

(defun q1067156x-ae-equal-p
    (scalar-zero domain-carrier measure codomain-carrier left right)
  (and
   (q1067156x-function-p domain-carrier codomain-carrier left)
   (q1067156x-function-p domain-carrier codomain-carrier right)
   (q1067156x-null-set-p
    scalar-zero domain-carrier measure
    (q1067156x-disagreement-set domain-carrier left right))))

;; Standard measurability is characterized by measurable upper-ray preimages.

(defun q1067156x-upper-ray-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-static-apply-term
      less
      (list (q1067156x-quoted threshold)
            (q1067156x-static-apply-term function '(x))))))))

(defun q1067156x-measurable-upper-rays-function
    (domain-carrier measurable codomain-carrier less function)
  (list
   'lambda '(threshold)
   (q1067156x-implies-term
    (q1067156x-static-apply-term codomain-carrier '(threshold))
    (q1067156x-static-apply-term
     measurable
     (list
      (list 'q1067156x-upper-ray-preimage-set
            (q1067156x-quoted domain-carrier)
            (q1067156x-quoted function)
            (q1067156x-quoted less)
            'threshold))))))

(defun q1067156x-measurable-function-p
    (domain-carrier measurable codomain-carrier less function)
  (and
   (q1067156x-function-p domain-carrier codomain-carrier function)
   (q1067156x-universal-p
    (q1067156x-measurable-upper-rays-function
     domain-carrier measurable codomain-carrier less function)
    '(threshold))))

(defun q1067156x-ae-measurable-witness-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (list
   'lambda '(representative)
   (q1067156x-and-terms
    (list
     (list 'q1067156x-measurable-function-p
           (q1067156x-quoted domain-carrier)
           (q1067156x-quoted measurable)
           (q1067156x-quoted codomain-carrier)
           (q1067156x-quoted less)
           'representative)
     (list 'q1067156x-ae-equal-p
           (q1067156x-quoted scalar-zero)
           (q1067156x-quoted domain-carrier)
           (q1067156x-quoted measure)
           (q1067156x-quoted codomain-carrier)
           (q1067156x-quoted function)
           'representative)))))

(defun q1067156x-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (and
   (q1067156x-function-p domain-carrier codomain-carrier function)
   (q1067156x-exists-p
    (q1067156x-ae-measurable-witness-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
    '(representative))))

;; The lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple functions below the integrand.

(defun q1067156x-fiber-set (domain-carrier function value)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (list 'equal
           (q1067156x-static-apply-term function '(x))
           (q1067156x-quoted value))))))

(defun q1067156x-values-in-carrier-p (carrier values)
  (if (consp values)
      (and
       (q1067156x-member-p carrier (car values))
       (q1067156x-values-in-carrier-p carrier (cdr values)))
    (equal values nil)))

(defun q1067156x-value-attained-function
    (domain-carrier function value)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (list 'equal
           (q1067156x-static-apply-term function '(x))
           (q1067156x-quoted value))))))

(defun q1067156x-value-attained-p
    (domain-carrier function value)
  (q1067156x-exists-p
   (q1067156x-value-attained-function
    domain-carrier function value)
   '(x)))

(defun q1067156x-values-attained-p
    (domain-carrier function values)
  (if (consp values)
      (and
       (q1067156x-value-attained-p
        domain-carrier function (car values))
       (q1067156x-values-attained-p
        domain-carrier function (cdr values)))
    (equal values nil)))

(defun q1067156x-range-in-values-function
    (domain-carrier function values)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-static-apply-term domain-carrier '(x))
    (list 'member-equal
          (q1067156x-static-apply-term function '(x))
          (q1067156x-quoted values)))))

(defun q1067156x-simple-function-p
    (domain-carrier measurable codomain-carrier less function values)
  (and
   (q1067156x-measurable-function-p
    domain-carrier measurable codomain-carrier less function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (q1067156x-values-in-carrier-p codomain-carrier values)
   (q1067156x-values-attained-p domain-carrier function values)
   (q1067156x-universal-p
    (q1067156x-range-in-values-function
     domain-carrier function values)
    '(x))))

(defun q1067156x-finite-simple-integral
    (domain-carrier measure function values
     scalar-zero scalar-add scalar-multiply)
  (if (consp values)
      (q1067156x-ennreal-add
       (q1067156x-ennreal-multiply
        (car values)
        (q1067156x-unary-value
         measure
         (q1067156x-fiber-set
          domain-carrier function (car values)))
        scalar-zero scalar-multiply)
       (q1067156x-finite-simple-integral
        domain-carrier measure function (cdr values)
        scalar-zero scalar-add scalar-multiply)
       scalar-add)
    (q1067156x-ennreal-zero scalar-zero)))

(defun q1067156x-simple-below-function
    (domain-carrier simple function scalar-less)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-static-apply-term domain-carrier '(x))
    (list 'q1067156x-ennreal-less-equal-p
          (q1067156x-static-apply-term simple '(x))
          (q1067156x-static-apply-term function '(x))
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-simple-below-p
    (domain-carrier simple function scalar-less)
  (q1067156x-universal-p
   (q1067156x-simple-below-function
    domain-carrier simple function scalar-less)
   '(x)))

(defun q1067156x-lintegral-upper-bound-function
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (list
   'lambda '(simple values)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-simple-function-p
            (q1067156x-quoted domain-carrier)
            (q1067156x-quoted measurable)
            (q1067156x-quoted ennreal-carrier)
            (q1067156x-quoted ennreal-less)
            'simple 'values)
      (list 'q1067156x-simple-below-p
            (q1067156x-quoted domain-carrier)
            'simple
            (q1067156x-quoted function)
            (q1067156x-quoted scalar-less))))
    (list 'q1067156x-ennreal-less-equal-p
          (list 'q1067156x-finite-simple-integral
                (q1067156x-quoted domain-carrier)
                (q1067156x-quoted measure)
                'simple 'values
                (q1067156x-quoted scalar-zero)
                (q1067156x-quoted scalar-add)
                (q1067156x-quoted scalar-multiply))
          (q1067156x-quoted bound)
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-lintegral-upper-bound-p
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (q1067156x-universal-p
   (q1067156x-lintegral-upper-bound-function
    domain-carrier measurable measure ennreal-carrier ennreal-less
    function bound scalar-zero scalar-add scalar-multiply scalar-less)
   '(simple values)))

(defun q1067156x-lintegral-least-upper-bound-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     function value)
  (list
   'lambda '(bound)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-ennreal-p
            'bound
            (q1067156x-quoted scalar-carrier)
            (q1067156x-quoted scalar-zero)
            (q1067156x-quoted scalar-less))
      (list 'q1067156x-lintegral-upper-bound-p
            (q1067156x-quoted domain-carrier)
            (q1067156x-quoted measurable)
            (q1067156x-quoted measure)
            (q1067156x-quoted ennreal-carrier)
            (q1067156x-quoted ennreal-less)
            (q1067156x-quoted function)
            'bound
            (q1067156x-quoted scalar-zero)
            (q1067156x-quoted scalar-add)
            (q1067156x-quoted scalar-multiply)
            (q1067156x-quoted scalar-less))))
    (list 'q1067156x-ennreal-less-equal-p
          (q1067156x-quoted value)
          'bound
          (q1067156x-quoted scalar-less)))))

(defun q1067156x-lintegral-value-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function value)
  (let ((ennreal-carrier
         (q1067156x-ennreal-carrier
          scalar-carrier scalar-zero scalar-less))
        (ennreal-less
         (q1067156x-ennreal-less-function scalar-less)))
    (and
     (q1067156x-function-p
      domain-carrier ennreal-carrier function)
     (q1067156x-member-p ennreal-carrier value)
     (q1067156x-lintegral-upper-bound-p
      domain-carrier measurable measure ennreal-carrier ennreal-less
      function value scalar-zero scalar-add scalar-multiply scalar-less)
     (q1067156x-universal-p
      (q1067156x-lintegral-least-upper-bound-function
       scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
       domain-carrier measurable measure ennreal-carrier ennreal-less
       function value)
      '(bound)))))

(defun q1067156x-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (let ((ennreal-carrier
         (q1067156x-ennreal-carrier
          scalar-carrier scalar-zero scalar-less)))
    (list
     'lambda '(function)
     (q1067156x-implies-term
      (list 'q1067156x-function-p
            (q1067156x-quoted domain-carrier)
            (q1067156x-quoted ennreal-carrier)
            'function)
      (list 'q1067156x-lintegral-value-p
            (q1067156x-quoted scalar-carrier)
            (q1067156x-quoted scalar-zero)
            (q1067156x-quoted scalar-add)
            (q1067156x-quoted scalar-multiply)
            (q1067156x-quoted scalar-less)
            (q1067156x-quoted domain-carrier)
            (q1067156x-quoted measurable)
            (q1067156x-quoted measure)
            'function
            (q1067156x-static-apply-term
             lintegral
             (list
              (q1067156x-quoted domain-carrier)
              (q1067156x-quoted measurable)
              (q1067156x-quoted measure)
              'function)))))))

(defun q1067156x-lintegral-operation-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (and
   (tamep-functionp lintegral)
   (q1067156x-universal-p
    (q1067156x-lintegral-values-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    '(function))))

(defun q1067156x-sequence-ae-measurable-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less sequence)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (list 'q1067156x-ae-measurable-p
          (q1067156x-quoted scalar-zero)
          (q1067156x-quoted domain-carrier)
          (q1067156x-quoted measurable)
          (q1067156x-quoted measure)
          (q1067156x-quoted codomain-carrier)
          (q1067156x-quoted less)
          (q1067156x-static-apply-term sequence '(n))))))

(defun q1067156x-sequence-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less sequence)
  (and
   (tamep-functionp sequence)
   (q1067156x-universal-p
    (q1067156x-sequence-ae-measurable-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less sequence)
    '(n))))

(defun q1067156x-lintegral-sequence-values
    (domain-carrier measurable measure sequence lintegral)
  (list
   'lambda '(n)
   (q1067156x-static-apply-term
    lintegral
    (list
     (q1067156x-quoted domain-carrier)
     (q1067156x-quoted measurable)
     (q1067156x-quoted measure)
     (q1067156x-static-apply-term sequence '(n))))))

;; For real functions, AE strong measurability is the preceding AE
;; measurability because the real line is separable. Integrability and the
;; Bochner integral are then defined from the exact lower integral.

(defun q1067156x-real-enorm-function
    (real-zero real-negate real-less function)
  (list
   'lambda '(x)
   (list 'q1067156x-ennreal-finite
         (list 'q1067156x-scalar-absolute-value
               (q1067156x-quoted real-less)
               (q1067156x-quoted real-zero)
               (q1067156x-quoted real-negate)
               (q1067156x-static-apply-term function '(x))))))

(defun q1067156x-real-positive-part-function
    (real-zero real-less function)
  (list
   'lambda '(x)
   (list 'q1067156x-ennreal-finite
         (list 'if
               (q1067156x-static-apply-term
                real-less
                (list
                 (q1067156x-static-apply-term function '(x))
                 (q1067156x-quoted real-zero)))
               (q1067156x-quoted real-zero)
               (q1067156x-static-apply-term function '(x))))))

(defun q1067156x-real-negative-part-function
    (real-zero real-negate real-less function)
  (let ((negative-value
         (q1067156x-static-apply-term
          real-negate
          (list (q1067156x-static-apply-term function '(x))))))
    (list
     'lambda '(x)
     (list 'q1067156x-ennreal-finite
           (list 'if
                 (q1067156x-static-apply-term
                  real-less
                  (list negative-value
                        (q1067156x-quoted real-zero)))
                 (q1067156x-quoted real-zero)
                 negative-value)))))

(defun q1067156x-ennreal-to-real (value real-zero)
  (if (equal value :q1067156x-top)
      real-zero
    (if (and (consp value)
             (equal (car value) :q1067156x-finite))
        (cdr value)
      real-zero)))

(defun q1067156x-integrable-p
    (real-zero real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (and
   (q1067156x-ae-measurable-p
    real-zero domain-carrier measurable measure
    real-carrier real-less function)
   (q1067156x-ennreal-less-p
    (apply$
     lintegral
     (list
      domain-carrier measurable measure
      (q1067156x-real-enorm-function
       real-zero real-negate real-less function)))
    :q1067156x-top
    real-less)))

(defun q1067156x-real-integral-value
    (real-zero real-add real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (if
      (q1067156x-integrable-p
       real-zero real-negate real-less
       domain-carrier measurable measure real-carrier function lintegral)
      (q1067156x-binary-value
       real-add
       (q1067156x-ennreal-to-real
        (apply$
         lintegral
         (list
          domain-carrier measurable measure
          (q1067156x-real-positive-part-function
           real-zero real-less function)))
        real-zero)
       (q1067156x-unary-value
        real-negate
        (q1067156x-ennreal-to-real
         (apply$
          lintegral
          (list
           domain-carrier measurable measure
           (q1067156x-real-negative-part-function
            real-zero real-negate real-less function)))
         real-zero)))
    real-zero))

(defun q1067156x-sequence-integrable-function
    (real-zero real-negate real-less
     domain-carrier measurable measure real-carrier sequence lintegral)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (list 'q1067156x-integrable-p
          (q1067156x-quoted real-zero)
          (q1067156x-quoted real-negate)
          (q1067156x-quoted real-less)
          (q1067156x-quoted domain-carrier)
          (q1067156x-quoted measurable)
          (q1067156x-quoted measure)
          (q1067156x-quoted real-carrier)
          (q1067156x-static-apply-term sequence '(n))
          (q1067156x-quoted lintegral)))))

(defun q1067156x-sequence-integrable-p
    (real-zero real-negate real-less
     domain-carrier measurable measure real-carrier sequence lintegral)
  (and
   (tamep-functionp sequence)
   (q1067156x-universal-p
    (q1067156x-sequence-integrable-function
     real-zero real-negate real-less
     domain-carrier measurable measure real-carrier sequence lintegral)
    '(n))))

(defun q1067156x-real-integral-sequence-values
    (real-zero real-add real-negate real-less
     domain-carrier measurable measure real-carrier sequence lintegral)
  (list
   'lambda '(n)
   (list 'q1067156x-real-integral-value
         (q1067156x-quoted real-zero)
         (q1067156x-quoted real-add)
         (q1067156x-quoted real-negate)
         (q1067156x-quoted real-less)
         (q1067156x-quoted domain-carrier)
         (q1067156x-quoted measurable)
         (q1067156x-quoted measure)
         (q1067156x-quoted real-carrier)
         (q1067156x-static-apply-term sequence '(n))
         (q1067156x-quoted lintegral))))

;; Arbitrary topologies on the source and the standard order topology on NNReal.

(defun q1067156x-intersection-set (left right)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term left '(x))
     (q1067156x-static-apply-term right '(x))))))

(defun q1067156x-family-union-witness-function
    (carrier family x)
  (list
   'lambda '(set)
   (q1067156x-and-terms
    (list
     (list 'q1067156x-valid-set-p
           (q1067156x-quoted carrier)
           'set)
     (q1067156x-static-apply-term family '(set))
     (q1067156x-apply-term
      'set
      (list (q1067156x-quoted x)))))))

(defun q1067156x-family-union-member-p
    (carrier family x)
  (q1067156x-exists-p
   (q1067156x-family-union-witness-function
    carrier family x)
   '(set)))

(defun q1067156x-family-union-set (carrier family)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term carrier '(x))
     (list 'q1067156x-family-union-member-p
           (q1067156x-quoted carrier)
           (q1067156x-quoted family)
           'x)))))

(defun q1067156x-family-members-open-function
    (topology family)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (q1067156x-static-apply-term family '(set))
    (q1067156x-static-apply-term topology '(set)))))

(defun q1067156x-topology-intersection-function
    (topology)
  (list
   'lambda '(left right)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term topology '(left))
      (q1067156x-static-apply-term topology '(right))))
    (q1067156x-static-apply-term
     topology
     (list (list 'q1067156x-intersection-set
                 'left 'right))))))

(defun q1067156x-topology-union-function
    (carrier topology)
  (list
   'lambda '(family)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'q1067156x-family-of-sets-p
            (q1067156x-quoted carrier)
            'family)
      (list 'q1067156x-universal-p
            (list 'q1067156x-family-members-open-function
                  (q1067156x-quoted topology)
                  'family)
            (q1067156x-quoted '(set)))))
    (q1067156x-static-apply-term
     topology
     (list
      (list 'q1067156x-family-union-set
            (q1067156x-quoted carrier)
            'family))))))

(defun q1067156x-topological-space-p
    (carrier topology)
  (and
   (q1067156x-family-of-sets-p carrier topology)
   (q1067156x-member-p topology (q1067156x-empty-set))
   (q1067156x-member-p topology (q1067156x-full-set carrier))
   (q1067156x-universal-p
    (q1067156x-topology-intersection-function topology)
    '(left right))
   (q1067156x-universal-p
    (q1067156x-topology-union-function carrier topology)
    '(family))))

(defun q1067156x-open-sets-measurable-function
    (topology measurable)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (q1067156x-static-apply-term topology '(set))
    (q1067156x-static-apply-term measurable '(set)))))

(defun q1067156x-opens-measurable-space-p
    (topology measurable)
  (q1067156x-universal-p
   (q1067156x-open-sets-measurable-function
    topology measurable)
   '(set)))

(defun q1067156x-nnreal-carrier
    (real-carrier real-zero real-less)
  (let ((ennreal-carrier
         (q1067156x-ennreal-carrier
          real-carrier real-zero real-less)))
    (list
     'lambda '(value)
     (q1067156x-and-terms
      (list
       (q1067156x-static-apply-term
        ennreal-carrier '(value))
       (q1067156x-not-term
        (list 'equal 'value
              (q1067156x-quoted :q1067156x-top))))))))

(defun q1067156x-upper-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-static-apply-term
      less
      (list
       (q1067156x-quoted threshold)
       (q1067156x-static-apply-term function '(x))))))))

(defun q1067156x-lower-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-static-apply-term
      less
      (list
       (q1067156x-static-apply-term function '(x))
       (q1067156x-quoted threshold)))))))

(defun q1067156x-continuity-rays-function
    (domain-carrier topology codomain-carrier less function)
  (list
   'lambda '(threshold)
   (q1067156x-implies-term
    (q1067156x-static-apply-term codomain-carrier '(threshold))
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term
       topology
       (list
        (list 'q1067156x-upper-preimage-set
              (q1067156x-quoted domain-carrier)
              (q1067156x-quoted function)
              (q1067156x-quoted less)
              'threshold)))
      (q1067156x-static-apply-term
       topology
       (list
        (list 'q1067156x-lower-preimage-set
              (q1067156x-quoted domain-carrier)
              (q1067156x-quoted function)
              (q1067156x-quoted less)
              'threshold))))))))

(defun q1067156x-continuous-nnreal-function-p
    (domain-carrier topology nnreal-carrier ennreal-less function)
  (and
   (q1067156x-function-p
    domain-carrier nnreal-carrier function)
   (q1067156x-universal-p
    (q1067156x-continuity-rays-function
     domain-carrier topology nnreal-carrier ennreal-less function)
    '(threshold))))

(defun q1067156x-function-bounded-by-p
    (domain-carrier less function bound)
  (q1067156x-universal-p
   (list
    'lambda '(x)
    (q1067156x-implies-term
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-less-equal-term
      less
      (q1067156x-static-apply-term function '(x))
      (q1067156x-quoted bound))))
   '(x)))

(defun q1067156x-bounded-witness-function
    (domain-carrier nnreal-carrier less function)
  (list
   'lambda '(bound)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term nnreal-carrier '(bound))
     (list 'q1067156x-function-bounded-by-p
           (q1067156x-quoted domain-carrier)
           (q1067156x-quoted less)
           (q1067156x-quoted function)
           'bound)))))

(defun q1067156x-bounded-continuous-function-p
    (domain-carrier topology nnreal-carrier less function)
  (and
   (q1067156x-continuous-nnreal-function-p
    domain-carrier topology nnreal-carrier less function)
   (q1067156x-exists-p
    (q1067156x-bounded-witness-function
     domain-carrier nnreal-carrier less function)
    '(bound))))

;; Arbitrary function families and their natural-number specialization.

(defun q1067156x-family-function-value
    (family index)
  (q1067156x-unary-value family index))

(defun q1067156x-function-family-values-function
    (index-carrier domain-carrier codomain-carrier family)
  (list
   'lambda '(i)
   (q1067156x-implies-term
    (q1067156x-static-apply-term index-carrier '(i))
    (list 'q1067156x-function-p
          (q1067156x-quoted domain-carrier)
          (q1067156x-quoted codomain-carrier)
          (q1067156x-static-apply-term family '(i))))))

(defun q1067156x-function-family-p
    (index-carrier domain-carrier codomain-carrier family)
  (and
   (tamep-functionp family)
   (q1067156x-universal-p
    (q1067156x-function-family-values-function
     index-carrier domain-carrier codomain-carrier family)
    '(i))))

(defun q1067156x-bounded-continuous-family-function
    (index-carrier domain-carrier topology
     nnreal-carrier less family)
  (list
   'lambda '(i)
   (q1067156x-implies-term
    (q1067156x-static-apply-term index-carrier '(i))
    (list 'q1067156x-bounded-continuous-function-p
          (q1067156x-quoted domain-carrier)
          (q1067156x-quoted topology)
          (q1067156x-quoted nnreal-carrier)
          (q1067156x-quoted less)
          (q1067156x-static-apply-term family '(i))))))

(defun q1067156x-bounded-continuous-family-p
    (index-carrier domain-carrier topology
     nnreal-carrier less family)
  (and
   (tamep-functionp family)
   (q1067156x-universal-p
    (q1067156x-bounded-continuous-family-function
     index-carrier domain-carrier topology
     nnreal-carrier less family)
    '(i))))

(defun q1067156x-bounded-continuous-sequence-function
    (domain-carrier topology nnreal-carrier less sequence)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (list 'q1067156x-bounded-continuous-function-p
          (q1067156x-quoted domain-carrier)
          (q1067156x-quoted topology)
          (q1067156x-quoted nnreal-carrier)
          (q1067156x-quoted less)
          (q1067156x-static-apply-term sequence '(n))))))

(defun q1067156x-bounded-continuous-sequence-p
    (domain-carrier topology nnreal-carrier less sequence)
  (and
   (tamep-functionp sequence)
   (q1067156x-universal-p
    (q1067156x-bounded-continuous-sequence-function
     domain-carrier topology nnreal-carrier less sequence)
    '(n))))

;; Filters and countable generation.

(defun q1067156x-filter-intersection-function (filter)
  (list
   'lambda '(left right)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term filter '(left))
      (q1067156x-static-apply-term filter '(right))))
    (q1067156x-static-apply-term
     filter
     (list (list 'q1067156x-intersection-set
                 'left 'right))))))

(defun q1067156x-filter-upward-function
    (carrier filter)
  (list
   'lambda '(left right)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (q1067156x-static-apply-term filter '(left))
      (list 'q1067156x-valid-set-p
            (q1067156x-quoted carrier)
            'right)
      (list 'q1067156x-set-subset-p
            (q1067156x-quoted carrier)
            'left 'right)))
    (q1067156x-static-apply-term filter '(right)))))

(defun q1067156x-filter-p (carrier filter)
  (and
   (q1067156x-family-of-sets-p carrier filter)
   (q1067156x-member-p filter (q1067156x-full-set carrier))
   (q1067156x-universal-p
    (q1067156x-filter-intersection-function filter)
    '(left right))
   (q1067156x-universal-p
    (q1067156x-filter-upward-function carrier filter)
    '(left right))))

(defun q1067156x-filter-basis-values-function
    (carrier filter basis)
  (list
   'lambda '(n)
   (q1067156x-implies-term
    (list 'natp 'n)
    (q1067156x-and-terms
     (list
      (list 'q1067156x-valid-set-p
            (q1067156x-quoted carrier)
            (q1067156x-static-apply-term basis '(n)))
      (q1067156x-static-apply-term
       filter
       (list (q1067156x-static-apply-term basis '(n)))))))))

(defun q1067156x-basis-below-function
    (carrier basis set)
  (list
   'lambda '(n)
   (q1067156x-and-terms
    (list
     (list 'natp 'n)
     (list 'q1067156x-set-subset-p
           (q1067156x-quoted carrier)
           (q1067156x-static-apply-term basis '(n))
           (q1067156x-quoted set))))))

(defun q1067156x-filter-basis-cofinal-function
    (carrier filter basis)
  (list
   'lambda '(set)
   (q1067156x-implies-term
    (q1067156x-static-apply-term filter '(set))
    (list 'q1067156x-exists-p
          (list 'q1067156x-basis-below-function
                (q1067156x-quoted carrier)
                (q1067156x-quoted basis)
                'set)
          (q1067156x-quoted '(n))))))

(defun q1067156x-filter-basis-p
    (carrier filter basis)
  (and
   (tamep-functionp basis)
   (q1067156x-universal-p
    (q1067156x-filter-basis-values-function
     carrier filter basis)
    '(n))
   (q1067156x-universal-p
    (q1067156x-filter-basis-cofinal-function
     carrier filter basis)
    '(set))))

(defun q1067156x-filter-basis-witness-function
    (carrier filter)
  (list
   'lambda '(basis)
   (list 'q1067156x-filter-basis-p
         (q1067156x-quoted carrier)
         (q1067156x-quoted filter)
         'basis)))

(defun q1067156x-countably-generated-filter-p
    (carrier filter)
  (and
   (q1067156x-filter-p carrier filter)
   (q1067156x-exists-p
    (q1067156x-filter-basis-witness-function
     carrier filter)
    '(basis))))

;; Order-topological convergence along an arbitrary filter.

(defun q1067156x-filter-lower-event
    (index-carrier less values lower)
  (list
   'lambda '(i)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term index-carrier '(i))
     (q1067156x-static-apply-term
      less
      (list
       (q1067156x-quoted lower)
       (q1067156x-static-apply-term values '(i))))))))

(defun q1067156x-filter-upper-event
    (index-carrier less values upper)
  (list
   'lambda '(i)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term index-carrier '(i))
     (q1067156x-static-apply-term
      less
      (list
       (q1067156x-static-apply-term values '(i))
       (q1067156x-quoted upper)))))))

(defun q1067156x-filter-convergence-bounds-function
    (index-carrier filter codomain-carrier less values limit)
  (list
   'lambda '(bound)
   (q1067156x-implies-term
    (q1067156x-static-apply-term codomain-carrier '(bound))
    (q1067156x-and-terms
     (list
      (q1067156x-implies-term
       (q1067156x-static-apply-term
        less
        (list 'bound (q1067156x-quoted limit)))
       (q1067156x-static-apply-term
        filter
        (list
         (list 'q1067156x-filter-lower-event
               (q1067156x-quoted index-carrier)
               (q1067156x-quoted less)
               (q1067156x-quoted values)
               'bound))))
      (q1067156x-implies-term
       (q1067156x-static-apply-term
        less
        (list (q1067156x-quoted limit) 'bound))
       (q1067156x-static-apply-term
        filter
        (list
         (list 'q1067156x-filter-upper-event
               (q1067156x-quoted index-carrier)
               (q1067156x-quoted less)
               (q1067156x-quoted values)
               'bound)))))))))

(defun q1067156x-tendsto-filter-order-p
    (index-carrier filter codomain-carrier less values limit)
  (and
   (q1067156x-filter-p index-carrier filter)
   (q1067156x-function-p
    index-carrier codomain-carrier values)
   (q1067156x-member-p codomain-carrier limit)
   (q1067156x-universal-p
    (q1067156x-filter-convergence-bounds-function
     index-carrier filter codomain-carrier less values limit)
    '(bound))))

(defun q1067156x-family-pointwise-values
    (family x)
  (list
   'lambda '(i)
   (q1067156x-apply-term
    (q1067156x-static-apply-term family '(i))
    (list (q1067156x-quoted x)))))

(defun q1067156x-filter-pointwise-tendsto-p
    (index-carrier filter codomain-carrier less
     family limit x)
  (q1067156x-tendsto-filter-order-p
   index-carrier filter codomain-carrier less
   (q1067156x-family-pointwise-values family x)
   (q1067156x-unary-value limit x)))

(defun q1067156x-filter-tendsto-failure-set
    (domain-carrier index-carrier filter
     codomain-carrier less family limit)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-not-term
      (list 'q1067156x-filter-pointwise-tendsto-p
            (q1067156x-quoted index-carrier)
            (q1067156x-quoted filter)
            (q1067156x-quoted codomain-carrier)
            (q1067156x-quoted less)
            (q1067156x-quoted family)
            (q1067156x-quoted limit)
            'x))))))

(defun q1067156x-ae-filter-pointwise-tendsto-p
    (real-zero domain-carrier measure
     index-carrier filter codomain-carrier less family limit)
  (and
   (q1067156x-function-family-p
    index-carrier domain-carrier codomain-carrier family)
   (q1067156x-function-p
    domain-carrier codomain-carrier limit)
   (q1067156x-null-set-p
    real-zero domain-carrier measure
    (q1067156x-filter-tendsto-failure-set
     domain-carrier index-carrier filter
     codomain-carrier less family limit))))

;; The eventual almost-everywhere uniform bound.

(defun q1067156x-bound-failure-set
    (domain-carrier less function bound)
  (list
   'lambda '(x)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term domain-carrier '(x))
     (q1067156x-static-apply-term
      less
      (list
       (q1067156x-quoted bound)
       (q1067156x-static-apply-term function '(x))))))))

(defun q1067156x-ae-bound-index-set
    (real-zero domain-carrier measure
     index-carrier less family bound)
  (list
   'lambda '(i)
   (q1067156x-and-terms
    (list
     (q1067156x-static-apply-term index-carrier '(i))
     (list 'q1067156x-null-set-p
           (q1067156x-quoted real-zero)
           (q1067156x-quoted domain-carrier)
           (q1067156x-quoted measure)
           (list 'q1067156x-bound-failure-set
                 (q1067156x-quoted domain-carrier)
                 (q1067156x-quoted less)
                 (q1067156x-static-apply-term family '(i))
                 (q1067156x-quoted bound)))))))

(defun q1067156x-eventually-ae-bounded-p
    (real-zero domain-carrier measure
     index-carrier filter less family bound)
  (q1067156x-member-p
   filter
   (q1067156x-ae-bound-index-set
    real-zero domain-carrier measure
    index-carrier less family bound)))

(defun q1067156x-everywhere-sequence-bound-function
    (domain-carrier less sequence bound)
  (list
   'lambda '(n x)
   (q1067156x-implies-term
    (q1067156x-and-terms
     (list
      (list 'natp 'n)
      (q1067156x-static-apply-term domain-carrier '(x))))
    (q1067156x-less-equal-term
     less
     (q1067156x-apply-term
      (q1067156x-static-apply-term sequence '(n))
      '(x))
     (q1067156x-quoted bound)))))

(defun q1067156x-everywhere-sequence-bounded-p
    (domain-carrier less sequence bound)
  (q1067156x-universal-p
   (q1067156x-everywhere-sequence-bound-function
    domain-carrier less sequence bound)
   '(n x)))

(defun q1067156x-everywhere-pointwise-limit-function
    (domain-carrier codomain-carrier less sequence limit)
  (list
   'lambda '(x)
   (q1067156x-implies-term
    (q1067156x-static-apply-term domain-carrier '(x))
    (list 'q1067156x-pointwise-tendsto-p
          (q1067156x-quoted codomain-carrier)
          (q1067156x-quoted less)
          (q1067156x-quoted sequence)
          (q1067156x-quoted limit)
          'x))))

(defun q1067156x-everywhere-pointwise-limit-p
    (domain-carrier codomain-carrier less sequence limit)
  (and
   (q1067156x-function-sequence-p
    domain-carrier codomain-carrier sequence)
   (q1067156x-function-p
    domain-carrier codomain-carrier limit)
   (q1067156x-universal-p
    (q1067156x-everywhere-pointwise-limit-function
     domain-carrier codomain-carrier less sequence limit)
    '(x))))

;; Finiteness of the measure and integral families.

(defun q1067156x-finite-measure-p
    (real-less domain-carrier measure)
  (q1067156x-ennreal-less-p
   (q1067156x-unary-value
    measure (q1067156x-full-set domain-carrier))
   :q1067156x-top
   real-less))

(defun q1067156x-lintegral-family-values
    (domain-carrier measurable measure family lintegral)
  (list
   'lambda '(i)
   (q1067156x-static-apply-term
    lintegral
    (list
     (q1067156x-quoted domain-carrier)
     (q1067156x-quoted measurable)
     (q1067156x-quoted measure)
     (q1067156x-static-apply-term family '(i))))))

;; The two indexed Lean declarations.

(defun q1067156x-filter-bounded-convergence-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     domain-carrier topology measurable measure lintegral
     index-carrier filter family bound limit)
  (let* ((ennreal-carrier
          (q1067156x-ennreal-carrier
           real-carrier real-zero real-less))
         (nnreal-carrier
          (q1067156x-nnreal-carrier
           real-carrier real-zero real-less))
         (ennreal-less
          (q1067156x-ennreal-less-function real-less))
         (integral-values
          (q1067156x-lintegral-family-values
           domain-carrier measurable measure family lintegral))
         (integral-limit
          (apply$ lintegral
                  (list domain-carrier measurable measure limit))))
    (implies
     (and
      (q1067156x-real-field-p
       real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less real-supremum)
      (q1067156x-topological-space-p
       domain-carrier topology)
      (q1067156x-measure-space-p
       real-carrier real-zero real-add real-less
       domain-carrier measurable measure)
      (q1067156x-opens-measurable-space-p
       topology measurable)
      (q1067156x-finite-measure-p
       real-less domain-carrier measure)
      (q1067156x-lintegral-operation-p
       real-carrier real-zero real-add real-multiply real-less
       domain-carrier measurable measure lintegral)
      (q1067156x-countably-generated-filter-p
       index-carrier filter)
      (q1067156x-bounded-continuous-family-p
       index-carrier domain-carrier topology
       nnreal-carrier ennreal-less family)
      (q1067156x-member-p nnreal-carrier bound)
      (q1067156x-function-p
       domain-carrier nnreal-carrier limit)
      (q1067156x-eventually-ae-bounded-p
       real-zero domain-carrier measure
       index-carrier filter ennreal-less family bound)
      (q1067156x-ae-filter-pointwise-tendsto-p
       real-zero domain-carrier measure
       index-carrier filter nnreal-carrier ennreal-less
       family limit))
     (q1067156x-tendsto-filter-order-p
      index-carrier filter ennreal-carrier ennreal-less
      integral-values integral-limit))))

(defun q1067156x-natural-bounded-convergence-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     domain-carrier topology measurable measure lintegral
     sequence bound limit)
  (let* ((ennreal-carrier
          (q1067156x-ennreal-carrier
           real-carrier real-zero real-less))
         (nnreal-carrier
          (q1067156x-nnreal-carrier
           real-carrier real-zero real-less))
         (ennreal-less
          (q1067156x-ennreal-less-function real-less))
         (integral-values
          (q1067156x-lintegral-sequence-values
           domain-carrier measurable measure sequence lintegral))
         (integral-limit
          (apply$ lintegral
                  (list domain-carrier measurable measure limit))))
    (implies
     (and
      (q1067156x-real-field-p
       real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less real-supremum)
      (q1067156x-topological-space-p
       domain-carrier topology)
      (q1067156x-measure-space-p
       real-carrier real-zero real-add real-less
       domain-carrier measurable measure)
      (q1067156x-opens-measurable-space-p
       topology measurable)
      (q1067156x-finite-measure-p
       real-less domain-carrier measure)
      (q1067156x-lintegral-operation-p
       real-carrier real-zero real-add real-multiply real-less
       domain-carrier measurable measure lintegral)
      (q1067156x-bounded-continuous-sequence-p
       domain-carrier topology nnreal-carrier ennreal-less sequence)
      (q1067156x-member-p nnreal-carrier bound)
      (q1067156x-function-p
       domain-carrier nnreal-carrier limit)
      (q1067156x-everywhere-sequence-bounded-p
       domain-carrier ennreal-less sequence bound)
      (q1067156x-everywhere-pointwise-limit-p
       domain-carrier nnreal-carrier ennreal-less sequence limit))
     (q1067156x-tendsto-order-p
      ennreal-carrier ennreal-less
      integral-values integral-limit))))

(defun thousand-theorems-q1067156x-bounded-convergence-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     domain-carrier topology measurable measure lintegral
     index-carrier filter family family-bound family-limit
     sequence sequence-bound sequence-limit)
  (and
   (q1067156x-filter-bounded-convergence-statement
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less real-supremum
    domain-carrier topology measurable measure lintegral
    index-carrier filter family family-bound family-limit)
   (q1067156x-natural-bounded-convergence-statement
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less real-supremum
    domain-carrier topology measurable measure lintegral
    sequence sequence-bound sequence-limit)))

(value-triple :itpeval-statement-checked)
:q
