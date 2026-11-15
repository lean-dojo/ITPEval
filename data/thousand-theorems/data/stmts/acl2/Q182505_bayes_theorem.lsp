;; Statement-only formalization of thousand-theorems corpus artifact Q182505,
;; "Bayes' theorem": for measurable events in an arbitrary finite measure
;; space, conditional probabilities satisfy Bayes' inverse-prior identity.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, measurable families, measures, and natural-indexed
;; sequences are tame APPLY$ function objects. FN-EQUAL supplies unbounded
;; universal quantification, so sigma closure and countable additivity range
;; over arbitrary represented measurable sequences rather than an
;; unconstrained accessor. The scalar structure is a Dedekind-complete ordered
;; field, hence a presentation of the standard real field rather than ACL2's
;; rational numbers; tagged finite nonnegative values plus top present ENNReal.

(defun q182505-quoted (object)
  (list 'quote object))

(defun q182505-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (q182505-term-list (cdr terms)))
    (q182505-quoted nil)))

(defun q182505-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (q182505-term-list arguments)))

(defun q182505-static-apply-term (function arguments)
  (q182505-apply-term
   (q182505-quoted function)
   arguments))

(defun q182505-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q182505-and-terms (cdr terms))
            (q182505-quoted nil))
    (q182505-quoted t)))

(defun q182505-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (q182505-quoted t)
            (q182505-or-terms (cdr terms)))
    (q182505-quoted nil)))

(defun q182505-not-term (term)
  (list 'if term
        (q182505-quoted nil)
        (q182505-quoted t)))

(defun q182505-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (q182505-quoted t)))

(defun q182505-iff-term (left right)
  (list 'if left
        (list 'if right
              (q182505-quoted t)
              (q182505-quoted nil))
        (list 'if right
              (q182505-quoted nil)
              (q182505-quoted t))))

(defun q182505-true-function (formals)
  (list 'lambda formals (q182505-quoted t)))

(defun q182505-false-function (formals)
  (list 'lambda formals (q182505-quoted nil)))

(defun q182505-universal-p (function formals)
  (let ((always-true (q182505-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun q182505-exists-p (function formals)
  (let ((always-false (q182505-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun q182505-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q182505-unary-value (function object)
  (apply$ function (list object)))

(defun q182505-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun q182505-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (q182505-static-apply-term carrier '(x))
      (q182505-static-apply-term left '(x))))
    (q182505-static-apply-term right '(x)))))

(defun q182505-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q182505-universal-p
    (q182505-set-subset-function carrier left right)
    '(x))))

(defun q182505-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (q182505-set-subset-p carrier set carrier)))

(defun q182505-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (q182505-implies-term
    (q182505-static-apply-term carrier '(x))
    (q182505-iff-term
     (q182505-static-apply-term left '(x))
     (q182505-static-apply-term right '(x))))))

(defun q182505-set-equiv-p (carrier left right)
  (and
   (q182505-valid-set-p carrier left)
   (q182505-valid-set-p carrier right)
   (q182505-universal-p
    (q182505-set-equiv-function carrier left right)
    '(x))))

(defun q182505-empty-set ()
  (list 'lambda '(x) (q182505-quoted nil)))

(defun q182505-full-set (carrier)
  (list 'lambda '(x)
        (q182505-static-apply-term carrier '(x))))

(defun q182505-complement-set (carrier set)
  (list
   'lambda '(x)
   (q182505-and-terms
    (list
     (q182505-static-apply-term carrier '(x))
     (q182505-not-term
      (q182505-static-apply-term set '(x)))))))

(defun q182505-intersection-set (carrier left right)
  (list
   'lambda '(x)
   (q182505-and-terms
    (list
     (q182505-static-apply-term carrier '(x))
     (q182505-static-apply-term left '(x))
     (q182505-static-apply-term right '(x))))))

(defun q182505-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (q182505-implies-term
    (q182505-static-apply-term domain-carrier '(x))
    (q182505-static-apply-term
     codomain-carrier
     (list (q182505-static-apply-term function '(x)))))))

(defun q182505-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (q182505-universal-p
    (q182505-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q182505-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (q182505-static-apply-term add '(x y)))
         (yz-add (q182505-static-apply-term add '(y z)))
         (xy-mul (q182505-static-apply-term multiply '(x y)))
         (yz-mul (q182505-static-apply-term multiply '(y z)))
         (neg-x (q182505-static-apply-term negate '(x)))
         (inv-x (q182505-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (q182505-implies-term
      (q182505-and-terms
       (list
        (q182505-static-apply-term carrier '(x))
        (q182505-static-apply-term carrier '(y))
        (q182505-static-apply-term carrier '(z))))
      (q182505-and-terms
       (list
        (q182505-static-apply-term carrier (list xy-add))
        (q182505-static-apply-term carrier (list xy-mul))
        (q182505-static-apply-term carrier (list neg-x))
        (q182505-static-apply-term carrier (list inv-x))
        (list 'equal
              (q182505-static-apply-term add (list xy-add 'z))
              (q182505-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (q182505-static-apply-term add '(y x)))
        (list 'equal
              (q182505-static-apply-term
               add (list 'x (q182505-quoted zero)))
              'x)
        (list 'equal
              (q182505-static-apply-term add (list 'x neg-x))
              (q182505-quoted zero))
        (list 'equal
              (q182505-static-apply-term multiply (list xy-mul 'z))
              (q182505-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (q182505-static-apply-term multiply '(y x)))
        (list 'equal
              (q182505-static-apply-term
               multiply (list 'x (q182505-quoted one)))
              'x)
        (q182505-implies-term
         (list 'equal 'x (q182505-quoted zero))
         (list 'equal inv-x (q182505-quoted zero)))
        (q182505-implies-term
         (q182505-not-term
          (list 'equal 'x (q182505-quoted zero)))
         (list 'equal
               (q182505-static-apply-term
                multiply (list 'x inv-x))
               (q182505-quoted one)))
        (list 'equal
              (q182505-static-apply-term multiply (list 'x yz-add))
              (q182505-static-apply-term
               add
               (list
                (q182505-static-apply-term multiply '(x y))
                (q182505-static-apply-term multiply '(x z)))))))))))

(defun q182505-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (q182505-static-apply-term less '(x y)))
        (yx (q182505-static-apply-term less '(y x)))
        (yz (q182505-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (q182505-implies-term
      (q182505-and-terms
       (list
        (q182505-static-apply-term carrier '(x))
        (q182505-static-apply-term carrier '(y))
        (q182505-static-apply-term carrier '(z))))
      (q182505-and-terms
       (list
        (q182505-not-term
         (q182505-static-apply-term less '(x x)))
        (q182505-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q182505-implies-term
         (q182505-and-terms (list xy yz))
         (q182505-static-apply-term less '(x z)))
        (q182505-implies-term
         xy
         (q182505-static-apply-term
          less
          (list
           (q182505-static-apply-term add '(x z))
           (q182505-static-apply-term add '(y z)))))
        (q182505-implies-term
         (q182505-and-terms
          (list
           (q182505-static-apply-term
            less (list (q182505-quoted zero) 'x))
           (q182505-static-apply-term
            less (list (q182505-quoted zero) 'y))))
         (q182505-static-apply-term
          less
          (list
           (q182505-quoted zero)
           (q182505-static-apply-term multiply '(x y)))))))))))

(defun q182505-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (q182505-static-apply-term carrier '(x))
      (q182505-static-apply-term set '(x))))
    (q182505-not-term
     (q182505-static-apply-term
      less (list (q182505-quoted upper) 'x))))))

(defun q182505-upper-bound-p
    (carrier less set upper)
  (and
   (q182505-member-p carrier upper)
   (q182505-valid-set-p carrier set)
   (q182505-universal-p
    (q182505-upper-bound-function carrier less set upper)
    '(x))))

(defun q182505-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (q182505-and-terms
    (list
     (q182505-static-apply-term carrier '(x))
     (q182505-static-apply-term set '(x))))))

(defun q182505-set-nonempty-p (carrier set)
  (and
   (q182505-valid-set-p carrier set)
   (q182505-exists-p
    (q182505-set-nonempty-function carrier set)
    '(x))))

(defun q182505-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'q182505-upper-bound-p
         (q182505-quoted carrier)
         (q182505-quoted less)
         (q182505-quoted set)
         'upper)))

(defun q182505-bounded-above-p (carrier less set)
  (q182505-exists-p
   (q182505-bounded-above-function carrier less set)
   '(upper)))

(defun q182505-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (q182505-implies-term
    (list 'q182505-upper-bound-p
          (q182505-quoted carrier)
          (q182505-quoted less)
          (q182505-quoted set)
          'upper)
    (q182505-not-term
     (q182505-static-apply-term
      less (list 'upper (q182505-quoted supremum)))))))

(defun q182505-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q182505-upper-bound-p carrier less set supremum)
   (q182505-universal-p
    (q182505-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q182505-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (list 'q182505-valid-set-p
            (q182505-quoted carrier) 'set)
      (list 'q182505-set-nonempty-p
            (q182505-quoted carrier) 'set)
      (list 'q182505-bounded-above-p
            (q182505-quoted carrier)
            (q182505-quoted less)
            'set)))
    (list 'q182505-least-upper-bound-p
          (q182505-quoted carrier)
          (q182505-quoted less)
          'set
          (q182505-static-apply-term
           supremum-operation '(set))))))

(defun q182505-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q182505-member-p carrier zero)
   (q182505-member-p carrier one)
   (not (equal zero one))
   (q182505-universal-p
    (q182505-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q182505-universal-p
    (q182505-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q182505-universal-p
    (q182505-completeness-function
     carrier less supremum)
    '(set))
   (q182505-binary-value less zero one)))

(defun q182505-scalar-absolute-value
    (less zero negate value)
  (if (q182505-binary-value less value zero)
      (q182505-unary-value negate value)
    value))
;; Sigma algebras.

(defun q182505-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (q182505-implies-term
    (list 'q182505-set-equiv-p
          (q182505-quoted carrier)
          'left 'right)
    (q182505-iff-term
     (q182505-static-apply-term family '(left))
     (q182505-static-apply-term family '(right))))))

(defun q182505-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (q182505-implies-term
    (q182505-static-apply-term family '(set))
    (list 'q182505-valid-set-p
          (q182505-quoted carrier)
          'set))))

(defun q182505-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (q182505-universal-p
    (q182505-family-extensional-function carrier family)
    '(left right))
   (q182505-universal-p
    (q182505-family-members-valid-function carrier family)
    '(set))))

(defun q182505-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (q182505-and-terms
    (list
     (list 'natp 'n)
     (q182505-apply-term
      (q182505-static-apply-term sequence '(n))
      (list (q182505-quoted x)))))))

(defun q182505-sequence-union-member-p (sequence x)
  (q182505-exists-p
   (q182505-sequence-union-member-function sequence x)
   '(n)))

(defun q182505-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (q182505-and-terms
    (list
     (q182505-static-apply-term carrier '(x))
     (list 'q182505-sequence-union-member-p
           (q182505-quoted sequence)
           'x)))))

(defun q182505-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (q182505-implies-term
    (list 'natp 'n)
    (list 'q182505-valid-set-p
          (q182505-quoted carrier)
          (q182505-static-apply-term sequence '(n))))))

(defun q182505-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (q182505-universal-p
    (q182505-sequence-of-sets-function carrier sequence)
    '(n))))

(defun q182505-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (q182505-implies-term
    (list 'natp 'n)
    (q182505-static-apply-term
     family
     (list (q182505-static-apply-term sequence '(n)))))))

(defun q182505-sequence-members-family-p
    (carrier family sequence)
  (and
   (q182505-sequence-of-sets-p carrier sequence)
   (q182505-universal-p
    (q182505-sequence-members-family-function family sequence)
    '(n))))

(defun q182505-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (q182505-implies-term
    (q182505-static-apply-term family '(set))
    (q182505-static-apply-term
     family
     (list
      (list 'q182505-complement-set
            (q182505-quoted carrier)
            'set))))))

(defun q182505-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (q182505-implies-term
    (list 'q182505-sequence-members-family-p
          (q182505-quoted carrier)
          (q182505-quoted family)
          'sequence)
    (q182505-static-apply-term
     family
     (list
      (list 'q182505-sequence-union-set
            (q182505-quoted carrier)
            'sequence))))))

(defun q182505-sigma-algebra-p (carrier family)
  (and
   (q182505-family-of-sets-p carrier family)
   (q182505-member-p family (q182505-empty-set))
   (q182505-universal-p
    (q182505-sigma-complement-function carrier family)
    '(set))
   (q182505-universal-p
    (q182505-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun q182505-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :q182505-top)
   (and
    (consp value)
    (equal (car value) :q182505-finite)
    (q182505-member-p scalar-carrier (cdr value))
    (not
     (q182505-binary-value scalar-less (cdr value) scalar-zero)))))

(defun q182505-ennreal-finite (value)
  (cons :q182505-finite value))

(defun q182505-ennreal-zero (scalar-zero)
  (q182505-ennreal-finite scalar-zero))

(defun q182505-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :q182505-top) nil)
   ((equal right :q182505-top) t)
   (t
    (q182505-binary-value scalar-less (cdr left) (cdr right)))))

(defun q182505-ennreal-less-equal-p (left right scalar-less)
  (not (q182505-ennreal-less-p right left scalar-less)))

(defun q182505-ennreal-add (left right scalar-add)
  (if (or (equal left :q182505-top)
          (equal right :q182505-top))
      :q182505-top
    (q182505-ennreal-finite
     (q182505-binary-value scalar-add (cdr left) (cdr right)))))

(defun q182505-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (q182505-ennreal-zero scalar-zero))
        (equal right (q182505-ennreal-zero scalar-zero)))
    (q182505-ennreal-zero scalar-zero))
   ((or (equal left :q182505-top)
        (equal right :q182505-top))
    :q182505-top)
   (t
    (q182505-ennreal-finite
     (q182505-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun q182505-ennreal-inverse
    (value scalar-zero scalar-inverse)
  (cond
   ((equal value :q182505-top)
    (q182505-ennreal-zero scalar-zero))
   ((equal value (q182505-ennreal-zero scalar-zero))
    :q182505-top)
   (t
    (q182505-ennreal-finite
     (q182505-unary-value scalar-inverse (cdr value))))))

(defun q182505-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q182505-ennreal-zero scalar-zero)
    (q182505-ennreal-add
     (q182505-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (q182505-unary-value sequence (- count 1))
     scalar-add)))

(defun q182505-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (q182505-implies-term
    (list 'natp 'count)
    (list 'q182505-ennreal-less-equal-p
          (list 'q182505-finite-ennreal-sum
                (q182505-quoted sequence)
                'count
                (q182505-quoted scalar-zero)
                (q182505-quoted scalar-add))
          (q182505-quoted total)
          (q182505-quoted scalar-less)))))

(defun q182505-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (q182505-universal-p
   (q182505-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun q182505-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (list 'q182505-ennreal-p
            'bound
            (q182505-quoted scalar-carrier)
            (q182505-quoted scalar-zero)
            (q182505-quoted scalar-less))
      (list 'q182505-sum-upper-bound-p
            (q182505-quoted sequence)
            'bound
            (q182505-quoted scalar-zero)
            (q182505-quoted scalar-add)
            (q182505-quoted scalar-less))))
    (list 'q182505-ennreal-less-equal-p
          (q182505-quoted total)
          'bound
          (q182505-quoted scalar-less)))))

(defun q182505-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (q182505-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (q182505-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (q182505-universal-p
    (q182505-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun q182505-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (q182505-implies-term
    (list 'q182505-set-equiv-p
          (q182505-quoted carrier)
          'left 'right)
    (list 'equal
          (q182505-static-apply-term measure '(left))
          (q182505-static-apply-term measure '(right))))))

(defun q182505-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (q182505-implies-term
    (list 'q182505-valid-set-p
          (q182505-quoted carrier)
          'set)
    (list 'q182505-ennreal-p
          (q182505-static-apply-term measure '(set))
          (q182505-quoted scalar-carrier)
          (q182505-quoted scalar-zero)
          (q182505-quoted scalar-less)))))

(defun q182505-measure-monotone-function
    (scalar-less carrier measurable measure)
  (list
   'lambda '(left right)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (q182505-static-apply-term measurable '(left))
      (q182505-static-apply-term measurable '(right))
      (list 'q182505-set-subset-p
            (q182505-quoted carrier)
            'left 'right)))
    (list 'q182505-ennreal-less-equal-p
          (q182505-static-apply-term measure '(left))
          (q182505-static-apply-term measure '(right))
          (q182505-quoted scalar-less)))))

(defun q182505-measure-null-subset-function
    (scalar-zero carrier measurable measure)
  (list
   'lambda '(left right)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (q182505-static-apply-term measurable '(left))
      (q182505-static-apply-term measurable '(right))
      (list 'q182505-set-subset-p
            (q182505-quoted carrier)
            'left 'right)
      (list 'equal
            (q182505-static-apply-term measure '(right))
            (list 'q182505-ennreal-zero
                  (q182505-quoted scalar-zero)))))
    (list 'equal
          (q182505-static-apply-term measure '(left))
          (list 'q182505-ennreal-zero
                (q182505-quoted scalar-zero))))))

(defun q182505-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (q182505-static-apply-term
    measure
    (list (q182505-static-apply-term sequence '(n))))))

(defun q182505-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (q182505-implies-term
    (q182505-static-apply-term carrier '(x))
    (q182505-not-term
     (q182505-and-terms
      (list
       (q182505-static-apply-term left '(x))
       (q182505-static-apply-term right '(x))))))))

(defun q182505-disjoint-sets-p (carrier left right)
  (q182505-universal-p
   (q182505-disjoint-sets-function carrier left right)
   '(x)))

(defun q182505-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (q182505-not-term (list 'equal 'm 'n))))
    (list 'q182505-disjoint-sets-p
          (q182505-quoted carrier)
          (q182505-static-apply-term sequence '(m))
          (q182505-static-apply-term sequence '(n))))))

(defun q182505-pairwise-disjoint-p (carrier sequence)
  (q182505-universal-p
   (q182505-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun q182505-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (list 'q182505-sequence-members-family-p
            (q182505-quoted carrier)
            (q182505-quoted measurable)
            'sequence)
      (list 'q182505-pairwise-disjoint-p
            (q182505-quoted carrier)
            'sequence)))
    (list 'q182505-countable-sum-p
          (list 'q182505-measure-sequence-values
                (q182505-quoted measure)
                'sequence)
          (q182505-static-apply-term
           measure
           (list
            (list 'q182505-sequence-union-set
                  (q182505-quoted carrier)
                  'sequence)))
          (q182505-quoted scalar-carrier)
          (q182505-quoted scalar-zero)
          (q182505-quoted scalar-add)
          (q182505-quoted scalar-less)))))

(defun q182505-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (q182505-static-apply-term measurable '(superset))
      (list 'q182505-set-subset-p
            (q182505-quoted carrier)
            (q182505-quoted set)
            'superset)))
    (list 'q182505-ennreal-less-equal-p
          (q182505-quoted lower)
          (q182505-static-apply-term measure '(superset))
          (q182505-quoted scalar-less)))))

(defun q182505-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (q182505-universal-p
   (q182505-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun q182505-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (q182505-implies-term
    (q182505-and-terms
     (list
      (list 'q182505-ennreal-p
            'lower
            (q182505-quoted scalar-carrier)
            (q182505-quoted scalar-zero)
            (q182505-quoted scalar-less))
      (list 'q182505-measurable-superset-lower-bound-p
            (q182505-quoted carrier)
            (q182505-quoted measurable)
            (q182505-quoted measure)
            (q182505-quoted set)
            'lower
            (q182505-quoted scalar-less))))
    (list 'q182505-ennreal-less-equal-p
          'lower
          (q182505-static-apply-term
           measure (list (q182505-quoted set)))
          (q182505-quoted scalar-less)))))

(defun q182505-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (q182505-valid-set-p carrier set)
   (q182505-measurable-superset-lower-bound-p
    carrier measurable measure set
    (q182505-unary-value measure set)
    scalar-less)
   (q182505-universal-p
    (q182505-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun q182505-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (q182505-implies-term
    (list 'q182505-valid-set-p
          (q182505-quoted carrier)
          'set)
    (list 'q182505-outer-value-p
          (q182505-quoted scalar-carrier)
          (q182505-quoted scalar-zero)
          (q182505-quoted scalar-less)
          (q182505-quoted carrier)
          (q182505-quoted measurable)
          (q182505-quoted measure)
          'set))))

(defun q182505-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (q182505-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (q182505-universal-p
    (q182505-measure-extensional-function carrier measure)
    '(left right))
   (q182505-universal-p
    (q182505-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (q182505-universal-p
    (q182505-measure-monotone-function
     scalar-less carrier measurable measure)
    '(left right))
   (q182505-universal-p
    (q182505-measure-null-subset-function
     scalar-zero carrier measurable measure)
    '(left right))
   (equal
    (q182505-unary-value measure (q182505-empty-set))
    (q182505-ennreal-zero scalar-zero))
   (q182505-universal-p
    (q182505-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (q182505-universal-p
    (q182505-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

(defun q182505-finite-measure-p
    (carrier measure)
  (and
   (tamep-functionp carrier)
   (tamep-functionp measure)
   (not
    (equal
     (q182505-unary-value
      measure
      (q182505-full-set carrier))
     :q182505-top))))

;; On a measurable conditioning event, this is definitionally the application
;; of (measure conditioning)^-1 • measure.restrict conditioning.

(defun q182505-conditional-probability
    (scalar-zero scalar-multiply scalar-inverse
     carrier measure event conditioning)
  (q182505-ennreal-multiply
   (q182505-ennreal-inverse
    (q182505-unary-value measure conditioning)
    scalar-zero scalar-inverse)
   (q182505-unary-value
    measure
    (q182505-intersection-set carrier conditioning event))
   scalar-zero scalar-multiply))

(defun thousand-theorems-q182505-bayes-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     sample-carrier sample-measurable sample-measure
     s event-t)
  (implies
   (and
    (q182505-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum)
    (q182505-measure-space-p
     real-carrier real-zero real-add real-less
     sample-carrier sample-measurable sample-measure)
    (q182505-finite-measure-p
     sample-carrier sample-measure)
    (q182505-member-p sample-measurable s)
    (q182505-member-p sample-measurable event-t))
   (equal
    (q182505-conditional-probability
     real-zero real-multiply real-inverse
     sample-carrier sample-measure event-t s)
    (q182505-ennreal-multiply
     (q182505-ennreal-multiply
      (q182505-ennreal-inverse
       (q182505-unary-value sample-measure s)
       real-zero real-inverse)
      (q182505-conditional-probability
       real-zero real-multiply real-inverse
       sample-carrier sample-measure s event-t)
      real-zero real-multiply)
     (q182505-unary-value sample-measure event-t)
     real-zero real-multiply))))

(value-triple :itpeval-statement-checked)
:q
