;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_a5:
;; finiteness of the real common-zero set of the sine- and cosine-weighted
;; oriented integrals of a nonconstant real polynomial. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, and functions are tame APPLY$ function objects. FN-EQUAL
;; supplies unbounded universal quantification, and inequality with a
;; constant-false function supplies internal existential witnesses. The scalar
;; structure is a Dedekind-complete ordered field, hence a presentation of the
;; real field. Borel measure and lower integration are defined extensionally;
;; the interval-length law below selects Lebesgue measure. Sine and cosine are
;; fixed by their convergent real power series. Thus real coefficients, real
;; endpoints, functions, and sets are not replaced by rational data or finite
;; tables.

(defun ht099-quoted (object)
  (list 'quote object))

(defun ht099-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (ht099-term-list (cdr terms)))
    (ht099-quoted nil)))

(defun ht099-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (ht099-term-list arguments)))

(defun ht099-static-apply-term (function arguments)
  (ht099-apply-term
   (ht099-quoted function)
   arguments))

(defun ht099-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht099-and-terms (cdr terms))
            (ht099-quoted nil))
    (ht099-quoted t)))

(defun ht099-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht099-quoted t)
            (ht099-or-terms (cdr terms)))
    (ht099-quoted nil)))

(defun ht099-not-term (term)
  (list 'if term
        (ht099-quoted nil)
        (ht099-quoted t)))

(defun ht099-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (ht099-quoted t)))

(defun ht099-iff-term (left right)
  (list 'if left
        (list 'if right
              (ht099-quoted t)
              (ht099-quoted nil))
        (list 'if right
              (ht099-quoted nil)
              (ht099-quoted t))))

(defun ht099-true-function (formals)
  (list 'lambda formals (ht099-quoted t)))

(defun ht099-false-function (formals)
  (list 'lambda formals (ht099-quoted nil)))

(defun ht099-universal-p (function formals)
  (let ((always-true (ht099-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun ht099-exists-p (function formals)
  (let ((always-false (ht099-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun ht099-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht099-unary-value (function object)
  (apply$ function (list object)))

(defun ht099-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets and arbitrary functions.

(defun ht099-set-subset-function (carrier left right)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term carrier '(x))
      (ht099-static-apply-term left '(x))))
    (ht099-static-apply-term right '(x)))))

(defun ht099-set-subset-p (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (ht099-universal-p
    (ht099-set-subset-function carrier left right)
    '(x))))

(defun ht099-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (ht099-set-subset-p carrier set carrier)))

(defun ht099-set-equiv-function (carrier left right)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term carrier '(x))
    (ht099-iff-term
     (ht099-static-apply-term left '(x))
     (ht099-static-apply-term right '(x))))))

(defun ht099-set-equiv-p (carrier left right)
  (and
   (ht099-valid-set-p carrier left)
   (ht099-valid-set-p carrier right)
   (ht099-universal-p
    (ht099-set-equiv-function carrier left right)
    '(x))))

(defun ht099-empty-set ()
  (list 'lambda '(x) (ht099-quoted nil)))

(defun ht099-full-set (carrier)
  (list 'lambda '(x)
        (ht099-static-apply-term carrier '(x))))

(defun ht099-complement-set (carrier set)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term carrier '(x))
     (ht099-not-term
      (ht099-static-apply-term set '(x)))))))

(defun ht099-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term domain-carrier '(x))
    (ht099-static-apply-term
     codomain-carrier
     (list (ht099-static-apply-term function '(x)))))))

(defun ht099-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (ht099-universal-p
    (ht099-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun ht099-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (ht099-static-apply-term add '(x y)))
         (yz-add (ht099-static-apply-term add '(y z)))
         (xy-mul (ht099-static-apply-term multiply '(x y)))
         (yz-mul (ht099-static-apply-term multiply '(y z)))
         (neg-x (ht099-static-apply-term negate '(x)))
         (inv-x (ht099-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (ht099-implies-term
      (ht099-and-terms
       (list
        (ht099-static-apply-term carrier '(x))
        (ht099-static-apply-term carrier '(y))
        (ht099-static-apply-term carrier '(z))))
      (ht099-and-terms
       (list
        (ht099-static-apply-term carrier (list xy-add))
        (ht099-static-apply-term carrier (list xy-mul))
        (ht099-static-apply-term carrier (list neg-x))
        (ht099-static-apply-term carrier (list inv-x))
        (list 'equal
              (ht099-static-apply-term add (list xy-add 'z))
              (ht099-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (ht099-static-apply-term add '(y x)))
        (list 'equal
              (ht099-static-apply-term
               add (list 'x (ht099-quoted zero)))
              'x)
        (list 'equal
              (ht099-static-apply-term add (list 'x neg-x))
              (ht099-quoted zero))
        (list 'equal
              (ht099-static-apply-term multiply (list xy-mul 'z))
              (ht099-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (ht099-static-apply-term multiply '(y x)))
        (list 'equal
              (ht099-static-apply-term
               multiply (list 'x (ht099-quoted one)))
              'x)
        (ht099-implies-term
         (list 'equal 'x (ht099-quoted zero))
         (list 'equal inv-x (ht099-quoted zero)))
        (ht099-implies-term
         (ht099-not-term
          (list 'equal 'x (ht099-quoted zero)))
         (list 'equal
               (ht099-static-apply-term
                multiply (list 'x inv-x))
               (ht099-quoted one)))
        (list 'equal
              (ht099-static-apply-term multiply (list 'x yz-add))
              (ht099-static-apply-term
               add
               (list
                (ht099-static-apply-term multiply '(x y))
                (ht099-static-apply-term multiply '(x z)))))))))))

(defun ht099-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (ht099-static-apply-term less '(x y)))
        (yx (ht099-static-apply-term less '(y x)))
        (yz (ht099-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (ht099-implies-term
      (ht099-and-terms
       (list
        (ht099-static-apply-term carrier '(x))
        (ht099-static-apply-term carrier '(y))
        (ht099-static-apply-term carrier '(z))))
      (ht099-and-terms
       (list
        (ht099-not-term
         (ht099-static-apply-term less '(x x)))
        (ht099-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (ht099-implies-term
         (ht099-and-terms (list xy yz))
         (ht099-static-apply-term less '(x z)))
        (ht099-implies-term
         xy
         (ht099-static-apply-term
          less
          (list
           (ht099-static-apply-term add '(x z))
           (ht099-static-apply-term add '(y z)))))
        (ht099-implies-term
         (ht099-and-terms
          (list
           (ht099-static-apply-term
            less (list (ht099-quoted zero) 'x))
           (ht099-static-apply-term
            less (list (ht099-quoted zero) 'y))))
         (ht099-static-apply-term
          less
          (list
           (ht099-quoted zero)
           (ht099-static-apply-term multiply '(x y)))))))))))

(defun ht099-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term carrier '(x))
      (ht099-static-apply-term set '(x))))
    (ht099-not-term
     (ht099-static-apply-term
      less (list (ht099-quoted upper) 'x))))))

(defun ht099-upper-bound-p
    (carrier less set upper)
  (and
   (ht099-member-p carrier upper)
   (ht099-valid-set-p carrier set)
   (ht099-universal-p
    (ht099-upper-bound-function carrier less set upper)
    '(x))))

(defun ht099-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term carrier '(x))
     (ht099-static-apply-term set '(x))))))

(defun ht099-set-nonempty-p (carrier set)
  (and
   (ht099-valid-set-p carrier set)
   (ht099-exists-p
    (ht099-set-nonempty-function carrier set)
    '(x))))

(defun ht099-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'ht099-upper-bound-p
         (ht099-quoted carrier)
         (ht099-quoted less)
         (ht099-quoted set)
         'upper)))

(defun ht099-bounded-above-p (carrier less set)
  (ht099-exists-p
   (ht099-bounded-above-function carrier less set)
   '(upper)))

(defun ht099-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (ht099-implies-term
    (list 'ht099-upper-bound-p
          (ht099-quoted carrier)
          (ht099-quoted less)
          (ht099-quoted set)
          'upper)
    (ht099-not-term
     (ht099-static-apply-term
      less (list 'upper (ht099-quoted supremum)))))))

(defun ht099-least-upper-bound-p
    (carrier less set supremum)
  (and
   (ht099-upper-bound-p carrier less set supremum)
   (ht099-universal-p
    (ht099-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun ht099-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-valid-set-p
            (ht099-quoted carrier) 'set)
      (list 'ht099-set-nonempty-p
            (ht099-quoted carrier) 'set)
      (list 'ht099-bounded-above-p
            (ht099-quoted carrier)
            (ht099-quoted less)
            'set)))
    (list 'ht099-least-upper-bound-p
          (ht099-quoted carrier)
          (ht099-quoted less)
          'set
          (ht099-static-apply-term
           supremum-operation '(set))))))

(defun ht099-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (ht099-member-p carrier zero)
   (ht099-member-p carrier one)
   (not (equal zero one))
   (ht099-universal-p
    (ht099-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (ht099-universal-p
    (ht099-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (ht099-universal-p
    (ht099-completeness-function
     carrier less supremum)
    '(set))
   (ht099-binary-value less zero one)))

(defun ht099-scalar-absolute-value
    (less zero negate value)
  (if (ht099-binary-value less value zero)
      (ht099-unary-value negate value)
    value))
;; Sigma algebras.

(defun ht099-family-extensional-function (carrier family)
  (list
   'lambda '(left right)
   (ht099-implies-term
    (list 'ht099-set-equiv-p
          (ht099-quoted carrier)
          'left 'right)
    (ht099-iff-term
     (ht099-static-apply-term family '(left))
     (ht099-static-apply-term family '(right))))))

(defun ht099-family-members-valid-function (carrier family)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-static-apply-term family '(set))
    (list 'ht099-valid-set-p
          (ht099-quoted carrier)
          'set))))

(defun ht099-family-of-sets-p (carrier family)
  (and
   (tamep-functionp family)
   (ht099-universal-p
    (ht099-family-extensional-function carrier family)
    '(left right))
   (ht099-universal-p
    (ht099-family-members-valid-function carrier family)
    '(set))))

(defun ht099-sequence-union-member-function (sequence x)
  (list
   'lambda '(n)
   (ht099-and-terms
    (list
     (list 'natp 'n)
     (ht099-apply-term
      (ht099-static-apply-term sequence '(n))
      (list (ht099-quoted x)))))))

(defun ht099-sequence-union-member-p (sequence x)
  (ht099-exists-p
   (ht099-sequence-union-member-function sequence x)
   '(n)))

(defun ht099-sequence-union-set (carrier sequence)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term carrier '(x))
     (list 'ht099-sequence-union-member-p
           (ht099-quoted sequence)
           'x)))))

(defun ht099-sequence-of-sets-function (carrier sequence)
  (list
   'lambda '(n)
   (ht099-implies-term
    (list 'natp 'n)
    (list 'ht099-valid-set-p
          (ht099-quoted carrier)
          (ht099-static-apply-term sequence '(n))))))

(defun ht099-sequence-of-sets-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (ht099-universal-p
    (ht099-sequence-of-sets-function carrier sequence)
    '(n))))

(defun ht099-sequence-members-family-function (family sequence)
  (list
   'lambda '(n)
   (ht099-implies-term
    (list 'natp 'n)
    (ht099-static-apply-term
     family
     (list (ht099-static-apply-term sequence '(n)))))))

(defun ht099-sequence-members-family-p
    (carrier family sequence)
  (and
   (ht099-sequence-of-sets-p carrier sequence)
   (ht099-universal-p
    (ht099-sequence-members-family-function family sequence)
    '(n))))

(defun ht099-sigma-complement-function (carrier family)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-static-apply-term family '(set))
    (ht099-static-apply-term
     family
     (list
      (list 'ht099-complement-set
            (ht099-quoted carrier)
            'set))))))

(defun ht099-sigma-union-function (carrier family)
  (list
   'lambda '(sequence)
   (ht099-implies-term
    (list 'ht099-sequence-members-family-p
          (ht099-quoted carrier)
          (ht099-quoted family)
          'sequence)
    (ht099-static-apply-term
     family
     (list
      (list 'ht099-sequence-union-set
            (ht099-quoted carrier)
            'sequence))))))

(defun ht099-sigma-algebra-p (carrier family)
  (and
   (ht099-family-of-sets-p carrier family)
   (ht099-member-p family (ht099-empty-set))
   (ht099-universal-p
    (ht099-sigma-complement-function carrier family)
    '(set))
   (ht099-universal-p
    (ht099-sigma-union-function carrier family)
    '(sequence))))

;; Extended nonnegative reals and countable sums.

(defun ht099-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :ht099-top)
   (and
    (consp value)
    (equal (car value) :ht099-finite)
    (ht099-member-p scalar-carrier (cdr value))
    (not
     (ht099-binary-value scalar-less (cdr value) scalar-zero)))))

(defun ht099-ennreal-finite (value)
  (cons :ht099-finite value))

(defun ht099-ennreal-zero (scalar-zero)
  (ht099-ennreal-finite scalar-zero))

(defun ht099-ennreal-less-p (left right scalar-less)
  (cond
   ((equal left :ht099-top) nil)
   ((equal right :ht099-top) t)
   (t
    (ht099-binary-value scalar-less (cdr left) (cdr right)))))

(defun ht099-ennreal-less-equal-p (left right scalar-less)
  (not (ht099-ennreal-less-p right left scalar-less)))

(defun ht099-ennreal-add (left right scalar-add)
  (if (or (equal left :ht099-top)
          (equal right :ht099-top))
      :ht099-top
    (ht099-ennreal-finite
     (ht099-binary-value scalar-add (cdr left) (cdr right)))))

(defun ht099-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left (ht099-ennreal-zero scalar-zero))
        (equal right (ht099-ennreal-zero scalar-zero)))
    (ht099-ennreal-zero scalar-zero))
   ((or (equal left :ht099-top)
        (equal right :ht099-top))
    :ht099-top)
   (t
    (ht099-ennreal-finite
     (ht099-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun ht099-finite-ennreal-sum
    (sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht099-ennreal-zero scalar-zero)
    (ht099-ennreal-add
     (ht099-finite-ennreal-sum
      sequence (- count 1) scalar-zero scalar-add)
     (ht099-unary-value sequence (- count 1))
     scalar-add)))

(defun ht099-sum-upper-bound-function
    (sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda '(count)
   (ht099-implies-term
    (list 'natp 'count)
    (list 'ht099-ennreal-less-equal-p
          (list 'ht099-finite-ennreal-sum
                (ht099-quoted sequence)
                'count
                (ht099-quoted scalar-zero)
                (ht099-quoted scalar-add))
          (ht099-quoted total)
          (ht099-quoted scalar-less)))))

(defun ht099-sum-upper-bound-p
    (sequence total scalar-zero scalar-add scalar-less)
  (ht099-universal-p
   (ht099-sum-upper-bound-function
    sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun ht099-sum-least-function
    (sequence total scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda '(bound)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-ennreal-p
            'bound
            (ht099-quoted scalar-carrier)
            (ht099-quoted scalar-zero)
            (ht099-quoted scalar-less))
      (list 'ht099-sum-upper-bound-p
            (ht099-quoted sequence)
            'bound
            (ht099-quoted scalar-zero)
            (ht099-quoted scalar-add)
            (ht099-quoted scalar-less))))
    (list 'ht099-ennreal-less-equal-p
          (ht099-quoted total)
          'bound
          (ht099-quoted scalar-less)))))

(defun ht099-countable-sum-p
    (sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (tamep-functionp sequence)
   (ht099-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (ht099-sum-upper-bound-p
    sequence total scalar-zero scalar-add scalar-less)
   (ht099-universal-p
    (ht099-sum-least-function
     sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

;; Countably additive measures, including values on arbitrary subsets.

(defun ht099-measure-extensional-function (carrier measure)
  (list
   'lambda '(left right)
   (ht099-implies-term
    (list 'ht099-set-equiv-p
          (ht099-quoted carrier)
          'left 'right)
    (list 'equal
          (ht099-static-apply-term measure '(left))
          (ht099-static-apply-term measure '(right))))))

(defun ht099-measure-values-function
    (scalar-carrier scalar-zero scalar-less carrier measure)
  (list
   'lambda '(set)
   (ht099-implies-term
    (list 'ht099-valid-set-p
          (ht099-quoted carrier)
          'set)
    (list 'ht099-ennreal-p
          (ht099-static-apply-term measure '(set))
          (ht099-quoted scalar-carrier)
          (ht099-quoted scalar-zero)
          (ht099-quoted scalar-less)))))

(defun ht099-measure-sequence-values (measure sequence)
  (list
   'lambda '(n)
   (ht099-static-apply-term
    measure
    (list (ht099-static-apply-term sequence '(n))))))

(defun ht099-disjoint-sets-function (carrier left right)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term carrier '(x))
    (ht099-not-term
     (ht099-and-terms
      (list
       (ht099-static-apply-term left '(x))
       (ht099-static-apply-term right '(x))))))))

(defun ht099-disjoint-sets-p (carrier left right)
  (ht099-universal-p
   (ht099-disjoint-sets-function carrier left right)
   '(x)))

(defun ht099-pairwise-disjoint-function (carrier sequence)
  (list
   'lambda '(m n)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (ht099-not-term (list 'equal 'm 'n))))
    (list 'ht099-disjoint-sets-p
          (ht099-quoted carrier)
          (ht099-static-apply-term sequence '(m))
          (ht099-static-apply-term sequence '(n))))))

(defun ht099-pairwise-disjoint-p (carrier sequence)
  (ht099-universal-p
   (ht099-pairwise-disjoint-function carrier sequence)
   '(m n)))

(defun ht099-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda '(sequence)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-sequence-members-family-p
            (ht099-quoted carrier)
            (ht099-quoted measurable)
            'sequence)
      (list 'ht099-pairwise-disjoint-p
            (ht099-quoted carrier)
            'sequence)))
    (list 'ht099-countable-sum-p
          (list 'ht099-measure-sequence-values
                (ht099-quoted measure)
                'sequence)
          (ht099-static-apply-term
           measure
           (list
            (list 'ht099-sequence-union-set
                  (ht099-quoted carrier)
                  'sequence)))
          (ht099-quoted scalar-carrier)
          (ht099-quoted scalar-zero)
          (ht099-quoted scalar-add)
          (ht099-quoted scalar-less)))))

(defun ht099-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda '(superset)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term measurable '(superset))
      (list 'ht099-set-subset-p
            (ht099-quoted carrier)
            (ht099-quoted set)
            'superset)))
    (list 'ht099-ennreal-less-equal-p
          (ht099-quoted lower)
          (ht099-static-apply-term measure '(superset))
          (ht099-quoted scalar-less)))))

(defun ht099-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (ht099-universal-p
   (ht099-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun ht099-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda '(lower)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-ennreal-p
            'lower
            (ht099-quoted scalar-carrier)
            (ht099-quoted scalar-zero)
            (ht099-quoted scalar-less))
      (list 'ht099-measurable-superset-lower-bound-p
            (ht099-quoted carrier)
            (ht099-quoted measurable)
            (ht099-quoted measure)
            (ht099-quoted set)
            'lower
            (ht099-quoted scalar-less))))
    (list 'ht099-ennreal-less-equal-p
          'lower
          (ht099-static-apply-term
           measure (list (ht099-quoted set)))
          (ht099-quoted scalar-less)))))

(defun ht099-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (ht099-valid-set-p carrier set)
   (ht099-measurable-superset-lower-bound-p
    carrier measurable measure set
    (ht099-unary-value measure set)
    scalar-less)
   (ht099-universal-p
    (ht099-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun ht099-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda '(set)
   (ht099-implies-term
    (list 'ht099-valid-set-p
          (ht099-quoted carrier)
          'set)
    (list 'ht099-outer-value-p
          (ht099-quoted scalar-carrier)
          (ht099-quoted scalar-zero)
          (ht099-quoted scalar-less)
          (ht099-quoted carrier)
          (ht099-quoted measurable)
          (ht099-quoted measure)
          'set))))

(defun ht099-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (ht099-sigma-algebra-p carrier measurable)
   (tamep-functionp measure)
   (ht099-universal-p
    (ht099-measure-extensional-function carrier measure)
    '(left right))
   (ht099-universal-p
    (ht099-measure-values-function
     scalar-carrier scalar-zero scalar-less carrier measure)
    '(set))
   (equal
    (ht099-unary-value measure (ht099-empty-set))
    (ht099-ennreal-zero scalar-zero))
   (ht099-universal-p
    (ht099-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (ht099-universal-p
    (ht099-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; The extended-nonnegative-real carrier and order used by lower integrals.

(defun ht099-ennreal-carrier
    (scalar-carrier scalar-zero scalar-less)
  (list
   'lambda '(value)
   (list 'ht099-ennreal-p
         'value
         (ht099-quoted scalar-carrier)
         (ht099-quoted scalar-zero)
         (ht099-quoted scalar-less))))

(defun ht099-ennreal-less-function (scalar-less)
  (list
   'lambda '(left right)
   (list 'ht099-ennreal-less-p
         'left 'right
         (ht099-quoted scalar-less))))

(defun ht099-null-set-p
    (scalar-zero domain-carrier measure set)
  (and
   (ht099-valid-set-p domain-carrier set)
   (equal
    (ht099-unary-value measure set)
    (ht099-ennreal-zero scalar-zero))))

;; Equality almost everywhere.

(defun ht099-disagreement-set
    (domain-carrier left right)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term domain-carrier '(x))
     (ht099-not-term
      (list 'equal
            (ht099-static-apply-term left '(x))
            (ht099-static-apply-term right '(x))))))))

(defun ht099-ae-equal-p
    (scalar-zero domain-carrier measure codomain-carrier left right)
  (and
   (ht099-function-p domain-carrier codomain-carrier left)
   (ht099-function-p domain-carrier codomain-carrier right)
   (ht099-null-set-p
    scalar-zero domain-carrier measure
    (ht099-disagreement-set domain-carrier left right))))

;; Standard measurability is characterized by measurable upper-ray preimages.

(defun ht099-upper-ray-preimage-set
    (domain-carrier function less threshold)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term domain-carrier '(x))
     (ht099-static-apply-term
      less
      (list (ht099-quoted threshold)
            (ht099-static-apply-term function '(x))))))))

(defun ht099-measurable-upper-rays-function
    (domain-carrier measurable codomain-carrier less function)
  (list
   'lambda '(threshold)
   (ht099-implies-term
    (ht099-static-apply-term codomain-carrier '(threshold))
    (ht099-static-apply-term
     measurable
     (list
      (list 'ht099-upper-ray-preimage-set
            (ht099-quoted domain-carrier)
            (ht099-quoted function)
            (ht099-quoted less)
            'threshold))))))

(defun ht099-measurable-function-p
    (domain-carrier measurable codomain-carrier less function)
  (and
   (ht099-function-p domain-carrier codomain-carrier function)
   (ht099-universal-p
    (ht099-measurable-upper-rays-function
     domain-carrier measurable codomain-carrier less function)
    '(threshold))))

(defun ht099-ae-measurable-witness-function
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (list
   'lambda '(representative)
   (ht099-and-terms
    (list
     (list 'ht099-measurable-function-p
           (ht099-quoted domain-carrier)
           (ht099-quoted measurable)
           (ht099-quoted codomain-carrier)
           (ht099-quoted less)
           'representative)
     (list 'ht099-ae-equal-p
           (ht099-quoted scalar-zero)
           (ht099-quoted domain-carrier)
           (ht099-quoted measure)
           (ht099-quoted codomain-carrier)
           (ht099-quoted function)
           'representative)))))

(defun ht099-ae-measurable-p
    (scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
  (and
   (ht099-function-p domain-carrier codomain-carrier function)
   (ht099-exists-p
    (ht099-ae-measurable-witness-function
     scalar-zero domain-carrier measurable measure
     codomain-carrier less function)
    '(representative))))

;; The lower Lebesgue integral is the supremum of the integrals of measurable
;; finite-range simple functions below the integrand.

(defun ht099-fiber-set (domain-carrier function value)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term domain-carrier '(x))
     (list 'equal
           (ht099-static-apply-term function '(x))
           (ht099-quoted value))))))

(defun ht099-values-in-carrier-p (carrier values)
  (if (consp values)
      (and
       (ht099-member-p carrier (car values))
       (ht099-values-in-carrier-p carrier (cdr values)))
    (equal values nil)))

(defun ht099-value-attained-function
    (domain-carrier function value)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term domain-carrier '(x))
     (list 'equal
           (ht099-static-apply-term function '(x))
           (ht099-quoted value))))))

(defun ht099-value-attained-p
    (domain-carrier function value)
  (ht099-exists-p
   (ht099-value-attained-function
    domain-carrier function value)
   '(x)))

(defun ht099-values-attained-p
    (domain-carrier function values)
  (if (consp values)
      (and
       (ht099-value-attained-p
        domain-carrier function (car values))
       (ht099-values-attained-p
        domain-carrier function (cdr values)))
    (equal values nil)))

(defun ht099-range-in-values-function
    (domain-carrier function values)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term domain-carrier '(x))
    (list 'member-equal
          (ht099-static-apply-term function '(x))
          (ht099-quoted values)))))

(defun ht099-simple-function-p
    (domain-carrier measurable codomain-carrier less function values)
  (and
   (ht099-measurable-function-p
    domain-carrier measurable codomain-carrier less function)
   (true-listp values)
   (no-duplicatesp-equal values)
   (ht099-values-in-carrier-p codomain-carrier values)
   (ht099-values-attained-p domain-carrier function values)
   (ht099-universal-p
    (ht099-range-in-values-function
     domain-carrier function values)
    '(x))))

(defun ht099-finite-simple-integral
    (domain-carrier measure function values
     scalar-zero scalar-add scalar-multiply)
  (if (consp values)
      (ht099-ennreal-add
       (ht099-ennreal-multiply
        (car values)
        (ht099-unary-value
         measure
         (ht099-fiber-set
          domain-carrier function (car values)))
        scalar-zero scalar-multiply)
       (ht099-finite-simple-integral
        domain-carrier measure function (cdr values)
        scalar-zero scalar-add scalar-multiply)
       scalar-add)
    (ht099-ennreal-zero scalar-zero)))

(defun ht099-simple-below-function
    (domain-carrier simple function scalar-less)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term domain-carrier '(x))
    (list 'ht099-ennreal-less-equal-p
          (ht099-static-apply-term simple '(x))
          (ht099-static-apply-term function '(x))
          (ht099-quoted scalar-less)))))

(defun ht099-simple-below-p
    (domain-carrier simple function scalar-less)
  (ht099-universal-p
   (ht099-simple-below-function
    domain-carrier simple function scalar-less)
   '(x)))

(defun ht099-lintegral-upper-bound-function
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (list
   'lambda '(simple values)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-simple-function-p
            (ht099-quoted domain-carrier)
            (ht099-quoted measurable)
            (ht099-quoted ennreal-carrier)
            (ht099-quoted ennreal-less)
            'simple 'values)
      (list 'ht099-simple-below-p
            (ht099-quoted domain-carrier)
            'simple
            (ht099-quoted function)
            (ht099-quoted scalar-less))))
    (list 'ht099-ennreal-less-equal-p
          (list 'ht099-finite-simple-integral
                (ht099-quoted domain-carrier)
                (ht099-quoted measure)
                'simple 'values
                (ht099-quoted scalar-zero)
                (ht099-quoted scalar-add)
                (ht099-quoted scalar-multiply))
          (ht099-quoted bound)
          (ht099-quoted scalar-less)))))

(defun ht099-lintegral-upper-bound-p
    (domain-carrier measurable measure ennreal-carrier ennreal-less
     function bound scalar-zero scalar-add scalar-multiply scalar-less)
  (ht099-universal-p
   (ht099-lintegral-upper-bound-function
    domain-carrier measurable measure ennreal-carrier ennreal-less
    function bound scalar-zero scalar-add scalar-multiply scalar-less)
   '(simple values)))

(defun ht099-lintegral-least-upper-bound-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure ennreal-carrier ennreal-less
     function value)
  (list
   'lambda '(bound)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-ennreal-p
            'bound
            (ht099-quoted scalar-carrier)
            (ht099-quoted scalar-zero)
            (ht099-quoted scalar-less))
      (list 'ht099-lintegral-upper-bound-p
            (ht099-quoted domain-carrier)
            (ht099-quoted measurable)
            (ht099-quoted measure)
            (ht099-quoted ennreal-carrier)
            (ht099-quoted ennreal-less)
            (ht099-quoted function)
            'bound
            (ht099-quoted scalar-zero)
            (ht099-quoted scalar-add)
            (ht099-quoted scalar-multiply)
            (ht099-quoted scalar-less))))
    (list 'ht099-ennreal-less-equal-p
          (ht099-quoted value)
          'bound
          (ht099-quoted scalar-less)))))

(defun ht099-lintegral-value-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure function value)
  (let ((ennreal-carrier
         (ht099-ennreal-carrier
          scalar-carrier scalar-zero scalar-less))
        (ennreal-less
         (ht099-ennreal-less-function scalar-less)))
    (and
     (ht099-function-p
      domain-carrier ennreal-carrier function)
     (ht099-member-p ennreal-carrier value)
     (ht099-lintegral-upper-bound-p
      domain-carrier measurable measure ennreal-carrier ennreal-less
      function value scalar-zero scalar-add scalar-multiply scalar-less)
     (ht099-universal-p
      (ht099-lintegral-least-upper-bound-function
       scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
       domain-carrier measurable measure ennreal-carrier ennreal-less
       function value)
      '(bound)))))

(defun ht099-lintegral-values-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (let ((ennreal-carrier
         (ht099-ennreal-carrier
          scalar-carrier scalar-zero scalar-less)))
    (list
     'lambda '(function)
     (ht099-implies-term
      (list 'ht099-function-p
            (ht099-quoted domain-carrier)
            (ht099-quoted ennreal-carrier)
            'function)
      (list 'ht099-lintegral-value-p
            (ht099-quoted scalar-carrier)
            (ht099-quoted scalar-zero)
            (ht099-quoted scalar-add)
            (ht099-quoted scalar-multiply)
            (ht099-quoted scalar-less)
            (ht099-quoted domain-carrier)
            (ht099-quoted measurable)
            (ht099-quoted measure)
            'function
            (ht099-static-apply-term
             lintegral
             (list
              (ht099-quoted domain-carrier)
              (ht099-quoted measurable)
              (ht099-quoted measure)
              'function)))))))

(defun ht099-lintegral-operation-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
  (and
   (tamep-functionp lintegral)
   (ht099-universal-p
    (ht099-lintegral-values-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-less
     domain-carrier measurable measure lintegral)
    '(function))))

;; For real functions, AE strong measurability is the preceding AE
;; measurability because the real line is separable. Integrability and the
;; Bochner integral are then defined from the exact lower integral.

(defun ht099-real-enorm-function
    (real-zero real-negate real-less function)
  (list
   'lambda '(x)
   (list 'ht099-ennreal-finite
         (list 'ht099-scalar-absolute-value
               (ht099-quoted real-less)
               (ht099-quoted real-zero)
               (ht099-quoted real-negate)
               (ht099-static-apply-term function '(x))))))

(defun ht099-real-positive-part-function
    (real-zero real-less function)
  (list
   'lambda '(x)
   (list 'ht099-ennreal-finite
         (list 'if
               (ht099-static-apply-term
                real-less
                (list
                 (ht099-static-apply-term function '(x))
                 (ht099-quoted real-zero)))
               (ht099-quoted real-zero)
               (ht099-static-apply-term function '(x))))))

(defun ht099-real-negative-part-function
    (real-zero real-negate real-less function)
  (let ((negative-value
         (ht099-static-apply-term
          real-negate
          (list (ht099-static-apply-term function '(x))))))
    (list
     'lambda '(x)
     (list 'ht099-ennreal-finite
           (list 'if
                 (ht099-static-apply-term
                  real-less
                  (list negative-value
                        (ht099-quoted real-zero)))
                 (ht099-quoted real-zero)
                 negative-value)))))

(defun ht099-ennreal-to-real (value real-zero)
  (if (equal value :ht099-top)
      real-zero
    (if (and (consp value)
             (equal (car value) :ht099-finite))
        (cdr value)
      real-zero)))

(defun ht099-integrable-p
    (real-zero real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (and
   (ht099-ae-measurable-p
    real-zero domain-carrier measurable measure
    real-carrier real-less function)
   (ht099-ennreal-less-p
    (apply$
     lintegral
     (list
      domain-carrier measurable measure
      (ht099-real-enorm-function
       real-zero real-negate real-less function)))
    :ht099-top
    real-less)))

(defun ht099-real-integral-value
    (real-zero real-add real-negate real-less
     domain-carrier measurable measure real-carrier function lintegral)
  (if
      (ht099-integrable-p
       real-zero real-negate real-less
       domain-carrier measurable measure real-carrier function lintegral)
      (ht099-binary-value
       real-add
       (ht099-ennreal-to-real
        (apply$
         lintegral
         (list
          domain-carrier measurable measure
          (ht099-real-positive-part-function
           real-zero real-less function)))
        real-zero)
       (ht099-unary-value
        real-negate
        (ht099-ennreal-to-real
         (apply$
          lintegral
          (list
           domain-carrier measurable measure
           (ht099-real-negative-part-function
            real-zero real-negate real-less function)))
         real-zero)))
    real-zero))

;; General topologies and continuous maps.

(defun ht099-union-member-function (family x)
  (list
   'lambda '(set)
   (ht099-and-terms
    (list
     (ht099-static-apply-term family '(set))
     (ht099-apply-term 'set (list (ht099-quoted x)))))))

(defun ht099-union-member-p (family x)
  (ht099-exists-p
   (ht099-union-member-function family x)
   '(set)))

(defun ht099-union-set (carrier family)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term carrier '(x))
     (list 'ht099-union-member-p
           (ht099-quoted family) 'x)))))

(defun ht099-family-members-open-function (topology family)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-static-apply-term family '(set))
    (ht099-static-apply-term topology '(set)))))

(defun ht099-family-members-open-p (topology family)
  (and
   (tamep-functionp family)
   (ht099-universal-p
    (ht099-family-members-open-function topology family)
    '(set))))

(defun ht099-topology-intersection-function
    (carrier topology)
  (list
   'lambda '(left right)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term topology '(left))
      (ht099-static-apply-term topology '(right))))
    (ht099-static-apply-term
     topology
     (list
      (list 'lambda '(x)
            (ht099-and-terms
             (list
              (ht099-static-apply-term
               (ht099-quoted carrier) '(x))
              (ht099-apply-term 'left '(x))
              (ht099-apply-term 'right '(x))))))))))

(defun ht099-topology-union-function
    (carrier topology)
  (list
   'lambda '(family)
   (ht099-implies-term
    (list 'ht099-family-members-open-p
          (ht099-quoted topology) 'family)
    (ht099-static-apply-term
     topology
     (list
      (list 'ht099-union-set
            (ht099-quoted carrier) 'family))))))

(defun ht099-topological-space-p (carrier topology)
  (and
   (ht099-family-of-sets-p carrier topology)
   (ht099-member-p topology (ht099-empty-set))
   (ht099-member-p topology (ht099-full-set carrier))
   (ht099-universal-p
    (ht099-topology-intersection-function carrier topology)
    '(left right))
   (ht099-universal-p
    (ht099-topology-union-function carrier topology)
    '(family))))

(defun ht099-preimage-set
    (domain-carrier function target-set)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term domain-carrier '(x))
     (ht099-static-apply-term
      target-set
      (list (ht099-static-apply-term function '(x))))))))

(defun ht099-continuity-function
    (domain-carrier domain-topology target-topology function)
  (list
   'lambda '(open-set)
   (ht099-implies-term
    (ht099-static-apply-term target-topology '(open-set))
    (ht099-static-apply-term
     domain-topology
     (list
      (list 'ht099-preimage-set
            (ht099-quoted domain-carrier)
            (ht099-quoted function)
            'open-set))))))

(defun ht099-continuous-p
    (domain-carrier domain-topology
     target-carrier target-topology function)
  (and
   (ht099-function-p domain-carrier target-carrier function)
   (ht099-universal-p
    (ht099-continuity-function
     domain-carrier domain-topology target-topology function)
    '(open-set))))

(defun ht099-opens-measurable-function
    (topology measurable)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-static-apply-term topology '(set))
    (ht099-static-apply-term measurable '(set)))))

(defun ht099-opens-measurable-space-p
    (topology measurable)
  (ht099-universal-p
   (ht099-opens-measurable-function topology measurable)
   '(set)))

(defun ht099-topology-subset-sigma-function
    (topology sigma)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-static-apply-term topology '(set))
    (ht099-static-apply-term sigma '(set)))))

(defun ht099-topology-subset-sigma-p (topology sigma)
  (ht099-universal-p
   (ht099-topology-subset-sigma-function topology sigma)
   '(set)))

(defun ht099-borel-member-function
    (carrier topology set)
  (list
   'lambda '(sigma)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'ht099-sigma-algebra-p
            (ht099-quoted carrier) 'sigma)
      (list 'ht099-topology-subset-sigma-p
            (ht099-quoted topology) 'sigma)))
    (ht099-apply-term
     'sigma (list (ht099-quoted set))))))

(defun ht099-borel-member-p (carrier topology set)
  (and
   (ht099-valid-set-p carrier set)
   (ht099-universal-p
    (ht099-borel-member-function carrier topology set)
    '(sigma))))

(defun ht099-borel-space-function
    (carrier topology measurable)
  (list
   'lambda '(set)
   (ht099-implies-term
    (list 'ht099-valid-set-p
          (ht099-quoted carrier) 'set)
    (ht099-iff-term
     (ht099-static-apply-term measurable '(set))
     (list 'ht099-borel-member-p
           (ht099-quoted carrier)
           (ht099-quoted topology)
           'set)))))

(defun ht099-borel-space-p
    (carrier topology measurable)
  (and
   (ht099-sigma-algebra-p carrier measurable)
   (ht099-universal-p
    (ht099-borel-space-function
     carrier topology measurable)
    '(set))))

;; The exact order topology on the represented real field.

(defun ht099-open-interval-subset-function
    (real-carrier real-less lower upper set)
  (list
   'lambda '(y)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term real-carrier '(y))
      (ht099-static-apply-term
       real-less (list (ht099-quoted lower) 'y))
      (ht099-static-apply-term
       real-less (list 'y (ht099-quoted upper)))))
    (ht099-static-apply-term set '(y)))))

(defun ht099-open-interval-subset-p
    (real-carrier real-less lower upper set)
  (ht099-universal-p
   (ht099-open-interval-subset-function
    real-carrier real-less lower upper set)
   '(y)))

(defun ht099-order-neighborhood-witness-function
    (real-carrier real-less set x)
  (list
   'lambda '(bounds)
   (ht099-and-terms
    (list
     (list 'true-listp 'bounds)
     (list 'equal (list 'len 'bounds) '2)
     (ht099-static-apply-term
      real-carrier (list (list 'car 'bounds)))
     (ht099-static-apply-term
      real-carrier (list (list 'cadr 'bounds)))
     (ht099-static-apply-term
      real-less
      (list (list 'car 'bounds) (ht099-quoted x)))
     (ht099-static-apply-term
      real-less
      (list (ht099-quoted x) (list 'cadr 'bounds)))
     (list 'ht099-open-interval-subset-p
           (ht099-quoted real-carrier)
           (ht099-quoted real-less)
           (list 'car 'bounds)
           (list 'cadr 'bounds)
           (ht099-quoted set))))))

(defun ht099-order-neighborhood-p
    (real-carrier real-less set x)
  (ht099-exists-p
   (ht099-order-neighborhood-witness-function
    real-carrier real-less set x)
   '(bounds)))

(defun ht099-order-open-points-function
    (real-carrier real-less set)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term real-carrier '(x))
      (ht099-static-apply-term set '(x))))
    (list 'ht099-order-neighborhood-p
          (ht099-quoted real-carrier)
          (ht099-quoted real-less)
          (ht099-quoted set)
          'x))))

(defun ht099-order-open-p
    (real-carrier real-less set)
  (and
   (ht099-valid-set-p real-carrier set)
   (ht099-universal-p
    (ht099-order-open-points-function
     real-carrier real-less set)
    '(x))))

(defun ht099-order-topology-function
    (real-carrier real-less topology)
  (list
   'lambda '(set)
   (ht099-implies-term
    (list 'ht099-valid-set-p
          (ht099-quoted real-carrier) 'set)
    (ht099-iff-term
     (ht099-static-apply-term topology '(set))
     (list 'ht099-order-open-p
           (ht099-quoted real-carrier)
           (ht099-quoted real-less)
           'set)))))

(defun ht099-order-topology-p
    (real-carrier real-less topology)
  (and
   (ht099-topological-space-p real-carrier topology)
   (ht099-universal-p
    (ht099-order-topology-function
     real-carrier real-less topology)
    '(set))))

;; Arbitrary filters and scalar convergence along them.

(defun ht099-filter-upward-function
    (carrier filter)
  (list
   'lambda '(left right)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term filter '(left))
      (list 'ht099-valid-set-p
            (ht099-quoted carrier) 'right)
      (list 'ht099-set-subset-p
            (ht099-quoted carrier) 'left 'right)))
    (ht099-static-apply-term filter '(right)))))

(defun ht099-filter-intersection-function
    (carrier filter)
  (list
   'lambda '(left right)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term filter '(left))
      (ht099-static-apply-term filter '(right))))
    (ht099-static-apply-term
     filter
     (list
      (list 'lambda '(x)
            (ht099-and-terms
             (list
              (ht099-static-apply-term
               (ht099-quoted carrier) '(x))
              (ht099-apply-term 'left '(x))
              (ht099-apply-term 'right '(x))))))))))

(defun ht099-filter-p (carrier filter)
  (and
   (ht099-family-of-sets-p carrier filter)
   (ht099-member-p filter (ht099-full-set carrier))
   (ht099-universal-p
    (ht099-filter-upward-function carrier filter)
    '(left right))
   (ht099-universal-p
    (ht099-filter-intersection-function carrier filter)
    '(left right))))

(defun ht099-real-ball-event-set
    (index-carrier real-zero real-add real-negate real-less
     values limit epsilon)
  (list
   'lambda '(i)
   (ht099-and-terms
    (list
     (ht099-static-apply-term index-carrier '(i))
     (ht099-static-apply-term
      real-less
      (list
       (list 'ht099-scalar-absolute-value
             (ht099-quoted real-less)
             (ht099-quoted real-zero)
             (ht099-quoted real-negate)
             (ht099-static-apply-term
              real-add
              (list
               (ht099-static-apply-term values '(i))
               (ht099-static-apply-term
                real-negate
                (list (ht099-quoted limit))))))
       (ht099-quoted epsilon)))))))

(defun ht099-real-tendsto-filter-function
    (index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
  (list
   'lambda '(epsilon)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term real-carrier '(epsilon))
      (ht099-static-apply-term
       real-less
       (list (ht099-quoted real-zero) 'epsilon))))
    (ht099-static-apply-term
     filter
     (list
      (list 'ht099-real-ball-event-set
            (ht099-quoted index-carrier)
            (ht099-quoted real-zero)
            (ht099-quoted real-add)
            (ht099-quoted real-negate)
            (ht099-quoted real-less)
            (ht099-quoted values)
            (ht099-quoted limit)
            'epsilon))))))

(defun ht099-real-tendsto-filter-p
    (index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
  (and
   (ht099-function-p index-carrier real-carrier values)
   (ht099-member-p real-carrier limit)
   (ht099-universal-p
    (ht099-real-tendsto-filter-function
     index-carrier filter
     real-carrier real-zero real-add real-negate real-less values limit)
    '(epsilon))))

;; Generic measurability and almost-everywhere measurability.

(defun ht099-generic-measurability-function
    (domain-carrier domain-measurable
     target-measurable function)
  (list
   'lambda '(set)
   (ht099-implies-term
    (ht099-static-apply-term target-measurable '(set))
    (ht099-static-apply-term
     domain-measurable
     (list
      (list 'ht099-preimage-set
            (ht099-quoted domain-carrier)
            (ht099-quoted function)
            'set))))))

(defun ht099-generic-measurable-function-p
    (domain-carrier domain-measurable
     target-carrier target-measurable function)
  (and
   (ht099-function-p domain-carrier target-carrier function)
   (ht099-universal-p
    (ht099-generic-measurability-function
     domain-carrier domain-measurable target-measurable function)
    '(set))))

(defun ht099-generic-ae-measurable-witness-function
    (real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
  (list
   'lambda '(representative)
   (ht099-and-terms
    (list
     (list 'ht099-generic-measurable-function-p
           (ht099-quoted domain-carrier)
           (ht099-quoted domain-measurable)
           (ht099-quoted target-carrier)
           (ht099-quoted target-measurable)
           'representative)
     (list 'ht099-ae-equal-p
           (ht099-quoted real-zero)
           (ht099-quoted domain-carrier)
           (ht099-quoted measure)
           (ht099-quoted target-carrier)
           (ht099-quoted function)
           'representative)))))

(defun ht099-generic-ae-measurable-p
    (real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
  (and
   (ht099-function-p domain-carrier target-carrier function)
   (ht099-exists-p
    (ht099-generic-ae-measurable-witness-function
     real-zero domain-carrier domain-measurable measure
     target-carrier target-measurable function)
    '(representative))))

;; Dependent source spaces and probability measures.

(defun ht099-fiber-carrier (omega-carrier i)
  (list
   'lambda '(x)
   (ht099-static-apply-term
    omega-carrier
    (list (ht099-quoted i) 'x))))

(defun ht099-fiber-measurable (omega-measurable i)
  (list
   'lambda '(set)
   (ht099-static-apply-term
    omega-measurable
    (list (ht099-quoted i) 'set))))

(defun ht099-fiber-measure (mu i)
  (list
   'lambda '(set)
   (ht099-static-apply-term
    mu
    (list (ht099-quoted i) 'set))))

(defun ht099-fiber-random-variable (x-family i)
  (list
   'lambda '(x)
   (ht099-static-apply-term
    x-family
    (list (ht099-quoted i) 'x))))

(defun ht099-probability-measure-p
    (real-carrier real-zero real-one real-add real-less
     carrier measurable measure)
  (and
   (ht099-measure-space-p
    real-carrier real-zero real-add real-less
    carrier measurable measure)
   (equal
    (ht099-unary-value
     measure (ht099-full-set carrier))
    (ht099-ennreal-finite real-one))))

(defun ht099-source-measure-family-function
    (real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
  (list
   'lambda '(i)
   (ht099-implies-term
    (ht099-static-apply-term index-carrier '(i))
    (ht099-and-terms
     (list
      (list 'ht099-probability-measure-p
            (ht099-quoted real-carrier)
            (ht099-quoted real-zero)
            (ht099-quoted real-one)
            (ht099-quoted real-add)
            (ht099-quoted real-less)
            (list 'ht099-fiber-carrier
                  (ht099-quoted omega-carrier) 'i)
            (list 'ht099-fiber-measurable
                  (ht099-quoted omega-measurable) 'i)
            (list 'ht099-fiber-measure
                  (ht099-quoted mu) 'i))
      (list 'ht099-lintegral-operation-p
            (ht099-quoted real-carrier)
            (ht099-quoted real-zero)
            (ht099-quoted real-add)
            (ht099-quoted real-multiply)
            (ht099-quoted real-less)
            (list 'ht099-fiber-carrier
                  (ht099-quoted omega-carrier) 'i)
            (list 'ht099-fiber-measurable
                  (ht099-quoted omega-measurable) 'i)
            (list 'ht099-fiber-measure
                  (ht099-quoted mu) 'i)
            (ht099-quoted lintegral)))))))

(defun ht099-source-measure-family-p
    (real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
  (and
   (tamep-functionp omega-carrier)
   (tamep-functionp omega-measurable)
   (tamep-functionp mu)
   (tamep-functionp lintegral)
   (ht099-universal-p
    (ht099-source-measure-family-function
     real-carrier real-zero real-one real-add real-multiply real-less
     index-carrier omega-carrier omega-measurable mu lintegral)
    '(i))))

(defun ht099-family-ae-measurable-function
    (real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
  (list
   'lambda '(i)
   (ht099-implies-term
    (ht099-static-apply-term index-carrier '(i))
    (list 'ht099-generic-ae-measurable-p
          (ht099-quoted real-zero)
          (list 'ht099-fiber-carrier
                (ht099-quoted omega-carrier) 'i)
          (list 'ht099-fiber-measurable
                (ht099-quoted omega-measurable) 'i)
          (list 'ht099-fiber-measure
                (ht099-quoted mu) 'i)
          (ht099-quoted target-carrier)
          (ht099-quoted target-measurable)
          (list 'ht099-fiber-random-variable
                (ht099-quoted x-family) 'i)))))

(defun ht099-family-ae-measurable-p
    (real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
  (and
   (tamep-functionp x-family)
   (ht099-universal-p
    (ht099-family-ae-measurable-function
     real-zero index-carrier omega-carrier omega-measurable mu
     target-carrier target-measurable x-family)
    '(i))))

;; Bounded continuous test functions and their integrals.

(defun ht099-bound-function
    (domain-carrier real-zero real-negate real-less function bound)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term domain-carrier '(x))
    (ht099-not-term
     (ht099-static-apply-term
      real-less
      (list
       (ht099-quoted bound)
       (list 'ht099-scalar-absolute-value
             (ht099-quoted real-less)
             (ht099-quoted real-zero)
             (ht099-quoted real-negate)
             (ht099-static-apply-term function '(x)))))))))

(defun ht099-bound-witness-function
    (domain-carrier real-carrier real-zero real-negate real-less function)
  (list
   'lambda '(bound)
   (ht099-and-terms
    (list
     (ht099-static-apply-term real-carrier '(bound))
     (ht099-not-term
      (ht099-static-apply-term
       real-less
       (list 'bound (ht099-quoted real-zero))))
     (list 'ht099-universal-p
           (list 'ht099-bound-function
                 (ht099-quoted domain-carrier)
                 (ht099-quoted real-zero)
                 (ht099-quoted real-negate)
                 (ht099-quoted real-less)
                 (ht099-quoted function)
                 'bound)
           (ht099-quoted '(x)))))))

(defun ht099-bounded-continuous-p
    (domain-carrier domain-topology
     real-carrier real-topology real-zero real-negate real-less function)
  (and
   (ht099-continuous-p
    domain-carrier domain-topology
    real-carrier real-topology function)
   (ht099-exists-p
    (ht099-bound-witness-function
     domain-carrier real-carrier real-zero real-negate real-less function)
    '(bound))))

(defun ht099-compose (outer inner)
  (list
   'lambda '(x)
   (ht099-static-apply-term
    outer
    (list (ht099-static-apply-term inner '(x))))))

(defun ht099-compose-family (outer x-family)
  (list
   'lambda '(i x)
   (ht099-static-apply-term
    outer
    (list
     (ht099-static-apply-term x-family '(i x))))))

(defun ht099-test-integral-values
    (real-zero real-add real-negate real-less real-carrier
     omega-carrier omega-measurable mu lintegral x-family test)
  (list
   'lambda '(i)
   (list 'ht099-real-integral-value
         (ht099-quoted real-zero)
         (ht099-quoted real-add)
         (ht099-quoted real-negate)
         (ht099-quoted real-less)
         (list 'ht099-fiber-carrier
               (ht099-quoted omega-carrier) 'i)
         (list 'ht099-fiber-measurable
               (ht099-quoted omega-measurable) 'i)
         (list 'ht099-fiber-measure
               (ht099-quoted mu) 'i)
         (ht099-quoted real-carrier)
         (list 'ht099-compose
               (ht099-quoted test)
               (list 'ht099-fiber-random-variable
                     (ht099-quoted x-family) 'i))
         (ht099-quoted lintegral))))

(defun ht099-test-limit-integral
    (real-zero real-add real-negate real-less real-carrier
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function test)
  (ht099-real-integral-value
   real-zero real-add real-negate real-less
   limit-carrier limit-measurable limit-measure
   real-carrier
   (ht099-compose test limit-function)
   limit-lintegral))

(defun ht099-weak-convergence-test-function
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology)
  (list
   'lambda '(test)
   (ht099-implies-term
    (list 'ht099-bounded-continuous-p
          (ht099-quoted target-carrier)
          (ht099-quoted target-topology)
          (ht099-quoted real-carrier)
          (ht099-quoted real-topology)
          (ht099-quoted real-zero)
          (ht099-quoted real-negate)
          (ht099-quoted real-less)
          'test)
    (list 'ht099-real-tendsto-filter-p
          (ht099-quoted index-carrier)
          (ht099-quoted filter)
          (ht099-quoted real-carrier)
          (ht099-quoted real-zero)
          (ht099-quoted real-add)
          (ht099-quoted real-negate)
          (ht099-quoted real-less)
          (list 'ht099-test-integral-values
                (ht099-quoted real-zero)
                (ht099-quoted real-add)
                (ht099-quoted real-negate)
                (ht099-quoted real-less)
                (ht099-quoted real-carrier)
                (ht099-quoted omega-carrier)
                (ht099-quoted omega-measurable)
                (ht099-quoted mu)
                (ht099-quoted lintegral)
                (ht099-quoted x-family)
                'test)
          (list 'ht099-test-limit-integral
                (ht099-quoted real-zero)
                (ht099-quoted real-add)
                (ht099-quoted real-negate)
                (ht099-quoted real-less)
                (ht099-quoted real-carrier)
                (ht099-quoted limit-carrier)
                (ht099-quoted limit-measurable)
                (ht099-quoted limit-measure)
                (ht099-quoted limit-lintegral)
                (ht099-quoted limit-function)
                'test)))))

(defun ht099-weak-convergence-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology)
  (ht099-universal-p
   (ht099-weak-convergence-test-function
    real-carrier real-zero real-add real-negate real-less real-topology
    index-carrier filter
    omega-carrier omega-measurable mu lintegral x-family
    limit-carrier limit-measurable limit-measure
    limit-lintegral limit-function
    target-carrier target-topology)
   '(test)))

(defun ht099-tendsto-in-distribution-p
    (real-carrier real-zero real-add real-negate real-less real-topology
     index-carrier filter
     omega-carrier omega-measurable mu lintegral x-family
     limit-carrier limit-measurable limit-measure
     limit-lintegral limit-function
     target-carrier target-topology target-measurable)
  (and
   (ht099-family-ae-measurable-p
    real-zero index-carrier omega-carrier omega-measurable mu
    target-carrier target-measurable x-family)
   (ht099-generic-ae-measurable-p
    real-zero limit-carrier limit-measurable limit-measure
    target-carrier target-measurable limit-function)
   (ht099-weak-convergence-p
    real-carrier real-zero real-add real-negate real-less real-topology
    index-carrier filter
    omega-carrier omega-measurable mu lintegral x-family
    limit-carrier limit-measurable limit-measure
    limit-lintegral limit-function
    target-carrier target-topology)))

;; Natural indices and the sequential filter.

(defun ht099-natural-carrier ()
  (list 'lambda '(n) (list 'natp 'n)))

(defun ht099-eventually-from-function (set start)
  (list
   'lambda '(n)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (list 'natp 'n)
      (list '<= (ht099-quoted start) 'n)))
    (ht099-static-apply-term set '(n)))))

(defun ht099-eventually-at-top-p (set)
  (and
   (tamep-functionp set)
   (ht099-exists-p
    (list
     'lambda '(start)
     (ht099-and-terms
      (list
       (list 'natp 'start)
       (list 'ht099-universal-p
             (list 'ht099-eventually-from-function
                   (ht099-quoted set) 'start)
             (ht099-quoted '(n))))))
    '(start))))

(defun ht099-sequential-filter ()
  (list
   'lambda '(set)
   (list 'ht099-eventually-at-top-p 'set)))

;; Exact real powers, factorials, and Taylor partial sums.

(defun ht099-real-nat-value (n real-zero real-one real-add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-zero
    (ht099-binary-value
     real-add
     (ht099-real-nat-value
      (- n 1) real-zero real-one real-add)
     real-one)))

(defun ht099-real-power
    (value exponent real-one real-multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      real-one
    (ht099-binary-value
     real-multiply
     value
     (ht099-real-power
      value (- exponent 1) real-one real-multiply))))

(defun ht099-real-factorial
    (n real-zero real-one real-add real-multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      real-one
    (ht099-binary-value
     real-multiply
     (ht099-real-nat-value n real-zero real-one real-add)
     (ht099-real-factorial
      (- n 1)
      real-zero real-one real-add real-multiply))))

(defun ht099-real-divide
    (numerator denominator real-multiply real-inverse)
  (ht099-binary-value
   real-multiply
   numerator
   (ht099-unary-value real-inverse denominator)))

(defun ht099-alternating-value (k value real-negate)
  (if (equal (mod (nfix k) 2) 0)
      value
    (ht099-unary-value real-negate value)))

(defun ht099-exp-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (term
            (ht099-real-divide
             (ht099-real-power x k real-one real-multiply)
             (ht099-real-factorial
              k real-zero real-one real-add real-multiply)
             real-multiply real-inverse)))
      (ht099-binary-value
       real-add
       (ht099-exp-partial-sum
        k x
        real-zero real-one real-add real-multiply real-inverse)
       term))))

(defun ht099-cos-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-negate real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (exponent (* 2 k))
           (unsigned
            (ht099-real-divide
             (ht099-real-power
              x exponent real-one real-multiply)
             (ht099-real-factorial
              exponent real-zero real-one real-add real-multiply)
             real-multiply real-inverse))
           (term
            (ht099-alternating-value k unsigned real-negate)))
      (ht099-binary-value
       real-add
       (ht099-cos-partial-sum
        k x
        real-zero real-one real-add real-multiply
        real-negate real-inverse)
       term))))

(defun ht099-sin-partial-sum
    (count x
     real-zero real-one real-add real-multiply real-negate real-inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      real-zero
    (let* ((k (- count 1))
           (exponent (+ 1 (* 2 k)))
           (unsigned
            (ht099-real-divide
             (ht099-real-power
              x exponent real-one real-multiply)
             (ht099-real-factorial
              exponent real-zero real-one real-add real-multiply)
             real-multiply real-inverse))
           (term
            (ht099-alternating-value k unsigned real-negate)))
      (ht099-binary-value
       real-add
       (ht099-sin-partial-sum
        k x
        real-zero real-one real-add real-multiply
        real-negate real-inverse)
       term))))

(defun ht099-exp-partial-sum-sequence
    (x real-zero real-one real-add real-multiply real-inverse)
  (list
   'lambda '(n)
   (list
    'ht099-exp-partial-sum
    'n
    (ht099-quoted x)
    (ht099-quoted real-zero)
    (ht099-quoted real-one)
    (ht099-quoted real-add)
    (ht099-quoted real-multiply)
    (ht099-quoted real-inverse))))

(defun ht099-cos-partial-sum-sequence
    (x real-zero real-one real-add real-multiply
       real-negate real-inverse)
  (list
   'lambda '(n)
   (list
    'ht099-cos-partial-sum
    'n
    (ht099-quoted x)
    (ht099-quoted real-zero)
    (ht099-quoted real-one)
    (ht099-quoted real-add)
    (ht099-quoted real-multiply)
    (ht099-quoted real-negate)
    (ht099-quoted real-inverse))))

(defun ht099-sin-partial-sum-sequence
    (x real-zero real-one real-add real-multiply
       real-negate real-inverse)
  (list
   'lambda '(n)
   (list
    'ht099-sin-partial-sum
    'n
    (ht099-quoted x)
    (ht099-quoted real-zero)
    (ht099-quoted real-one)
    (ht099-quoted real-add)
    (ht099-quoted real-multiply)
    (ht099-quoted real-negate)
    (ht099-quoted real-inverse))))

(defun ht099-exp-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term real-carrier '(x))
    (list
     'ht099-real-tendsto-filter-p
     (list 'ht099-natural-carrier)
     (list 'ht099-sequential-filter)
     (ht099-quoted real-carrier)
     (ht099-quoted real-zero)
     (ht099-quoted real-add)
     (ht099-quoted real-negate)
     (ht099-quoted real-less)
     (list
      'ht099-exp-partial-sum-sequence
      'x
      (ht099-quoted real-zero)
      (ht099-quoted real-one)
      (ht099-quoted real-add)
      (ht099-quoted real-multiply)
      (ht099-quoted real-inverse))
     (ht099-static-apply-term exp '(x))))))

(defun ht099-cos-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term real-carrier '(x))
    (list
     'ht099-real-tendsto-filter-p
     (list 'ht099-natural-carrier)
     (list 'ht099-sequential-filter)
     (ht099-quoted real-carrier)
     (ht099-quoted real-zero)
     (ht099-quoted real-add)
     (ht099-quoted real-negate)
     (ht099-quoted real-less)
     (list
      'ht099-cos-partial-sum-sequence
      'x
      (ht099-quoted real-zero)
      (ht099-quoted real-one)
      (ht099-quoted real-add)
      (ht099-quoted real-multiply)
      (ht099-quoted real-negate)
      (ht099-quoted real-inverse))
     (ht099-static-apply-term cos '(x))))))

(defun ht099-sin-values-function
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
  (list
   'lambda '(x)
   (ht099-implies-term
    (ht099-static-apply-term real-carrier '(x))
    (list
     'ht099-real-tendsto-filter-p
     (list 'ht099-natural-carrier)
     (list 'ht099-sequential-filter)
     (ht099-quoted real-carrier)
     (ht099-quoted real-zero)
     (ht099-quoted real-add)
     (ht099-quoted real-negate)
     (ht099-quoted real-less)
     (list
      'ht099-sin-partial-sum-sequence
      'x
      (ht099-quoted real-zero)
      (ht099-quoted real-one)
      (ht099-quoted real-add)
      (ht099-quoted real-multiply)
      (ht099-quoted real-negate)
      (ht099-quoted real-inverse))
     (ht099-static-apply-term sin '(x))))))

(defun ht099-analytic-functions-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp sin cos)
  (and
   (ht099-function-p real-carrier real-carrier exp)
   (ht099-function-p real-carrier real-carrier sin)
   (ht099-function-p real-carrier real-carrier cos)
   (ht099-universal-p
    (ht099-exp-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less exp)
    '(x))
   (ht099-universal-p
    (ht099-sin-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
    '(x))
   (ht099-universal-p
   (ht099-cos-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
    '(x))))

;; The imported analytic infrastructure above is shared statement machinery.
;; Only sine and cosine are needed for this artifact.

(defun putnam-1980-a5-trigonometric-functions-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin cos)
  (and
   (ht099-function-p real-carrier real-carrier sin)
   (ht099-function-p real-carrier real-carrier cos)
   (ht099-universal-p
    (ht099-sin-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less sin)
    '(x))
   (ht099-universal-p
    (ht099-cos-values-function
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less cos)
    '(x))))

;; Coefficients are in ascending-power order. Trailing zero coefficients are
;; harmless, and nonconstancy is the existence of a nonzero positive-degree
;; coefficient.

(defun putnam-1980-a5-coefficients-p (coefficients real-carrier)
  (if (consp coefficients)
      (and
       (ht099-member-p real-carrier (car coefficients))
       (putnam-1980-a5-coefficients-p
        (cdr coefficients) real-carrier))
    (equal coefficients nil)))

(defun putnam-1980-a5-positive-degree-coefficient-p
    (coefficients real-zero)
  (if (consp (cdr coefficients))
      (or
       (not (equal (cadr coefficients) real-zero))
       (putnam-1980-a5-positive-degree-coefficient-p
        (cdr coefficients) real-zero))
    nil))

(defun putnam-1980-a5-polynomial-value
    (coefficients x real-zero real-add real-multiply)
  (if (consp coefficients)
      (ht099-binary-value
       real-add
       (car coefficients)
       (ht099-binary-value
        real-multiply
        x
        (putnam-1980-a5-polynomial-value
         (cdr coefficients) x
         real-zero real-add real-multiply)))
    real-zero))

;; The half-open interval (a,b] is used to define oriented integrals:
;; integral_0^x f = integral_(0,x] f - integral_(x,0] f.

(defun putnam-1980-a5-ioc-set
    (real-carrier real-less lower upper)
  (list
   'lambda '(x)
   (ht099-and-terms
    (list
     (ht099-static-apply-term real-carrier '(x))
     (ht099-static-apply-term
      real-less (list (ht099-quoted lower) 'x))
     (ht099-not-term
      (ht099-static-apply-term
       real-less (list (ht099-quoted upper) 'x)))))))

(defun putnam-1980-a5-lebesgue-interval-law-function
    (real-carrier real-zero real-add real-negate real-less measure)
  (list
   'lambda '(a b)
   (ht099-implies-term
    (ht099-and-terms
     (list
      (ht099-static-apply-term real-carrier '(a))
      (ht099-static-apply-term real-carrier '(b))))
    (list
     'equal
     (ht099-static-apply-term
      measure
      (list
       (list 'putnam-1980-a5-ioc-set
             (ht099-quoted real-carrier)
             (ht099-quoted real-less)
             'a 'b)))
     (list
      'ht099-ennreal-finite
      (list
       'if
       (ht099-static-apply-term real-less '(a b))
       (ht099-static-apply-term
        real-add
        (list
         'b
         (ht099-static-apply-term real-negate '(a))))
       (ht099-quoted real-zero)))))))

(defun putnam-1980-a5-lebesgue-measure-p
    (real-carrier real-zero real-add real-negate real-less
     measurable measure)
  (and
   (ht099-measure-space-p
    real-carrier real-zero real-add real-less
    real-carrier measurable measure)
   (ht099-universal-p
    (putnam-1980-a5-lebesgue-interval-law-function
     real-carrier real-zero real-add real-negate real-less measure)
    '(a b))))

(defun putnam-1980-a5-restricted-integrand-function
    (real-carrier real-zero real-add real-multiply real-less
     coefficients trigonometric-function lower upper)
  (list
   'lambda '(t)
   (list
    'if
    (ht099-and-terms
     (list
      (ht099-static-apply-term real-carrier '(t))
      (ht099-static-apply-term
       real-less (list (ht099-quoted lower) 't))
      (ht099-not-term
       (ht099-static-apply-term
        real-less (list (ht099-quoted upper) 't)))))
    (ht099-static-apply-term
     real-multiply
     (list
      (list
       'putnam-1980-a5-polynomial-value
       (ht099-quoted coefficients)
       't
       (ht099-quoted real-zero)
       (ht099-quoted real-add)
       (ht099-quoted real-multiply))
      (ht099-static-apply-term trigonometric-function '(t))))
    (ht099-quoted real-zero))))

(defun putnam-1980-a5-set-integral
    (real-carrier real-zero real-add real-negate real-less
     measurable measure lintegral function)
  (ht099-real-integral-value
   real-zero real-add real-negate real-less
   real-carrier measurable measure real-carrier function lintegral))

(defun putnam-1980-a5-oriented-integral
    (real-carrier real-zero real-add real-multiply real-negate real-less
     measurable measure lintegral coefficients trigonometric-function x)
  (let
      ((forward
        (putnam-1980-a5-restricted-integrand-function
         real-carrier real-zero real-add real-multiply real-less
         coefficients trigonometric-function real-zero x))
       (backward
        (putnam-1980-a5-restricted-integrand-function
         real-carrier real-zero real-add real-multiply real-less
         coefficients trigonometric-function x real-zero)))
    (ht099-binary-value
     real-add
     (putnam-1980-a5-set-integral
      real-carrier real-zero real-add real-negate real-less
      measurable measure lintegral forward)
     (ht099-unary-value
      real-negate
      (putnam-1980-a5-set-integral
       real-carrier real-zero real-add real-negate real-less
       measurable measure lintegral backward)))))

(defun putnam-1980-a5-common-zero-p
    (real-carrier real-zero real-add real-multiply real-negate real-less
     measurable measure lintegral sin cos coefficients x)
  (and
   (ht099-member-p real-carrier x)
   (equal
    (putnam-1980-a5-oriented-integral
     real-carrier real-zero real-add real-multiply real-negate real-less
     measurable measure lintegral coefficients sin x)
    real-zero)
   (equal
    (putnam-1980-a5-oriented-integral
     real-carrier real-zero real-add real-multiply real-negate real-less
     measurable measure lintegral coefficients cos x)
    real-zero)))

;; A subset is finite exactly when some finite ACL2 list contains all of its
;; members. SOLUTIONS is internally existentially quantified in the final
;; statement; it is not an extra theorem parameter.

(defun-sk putnam-1980-a5-all-common-zeroes-listed-p
    (real-carrier real-zero real-add real-multiply real-negate real-less
     measurable measure lintegral sin cos coefficients solutions)
  (forall (x)
    (implies
     (putnam-1980-a5-common-zero-p
      real-carrier real-zero real-add real-multiply real-negate real-less
      measurable measure lintegral sin cos coefficients x)
     (member-equal x solutions))))

(defun-sk putnambench-putnam-1980-a5-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less real-supremum
     real-topology measurable measure lintegral
     sin cos coefficients)
  (exists (solutions)
    (implies
     (and
      (ht099-real-field-p
       real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less real-supremum)
      (ht099-order-topology-p
       real-carrier real-less real-topology)
      (ht099-borel-space-p
       real-carrier real-topology measurable)
      (putnam-1980-a5-lebesgue-measure-p
       real-carrier real-zero real-add real-negate real-less
       measurable measure)
      (ht099-lintegral-operation-p
       real-carrier real-zero real-add real-multiply real-less
       real-carrier measurable measure lintegral)
      (putnam-1980-a5-trigonometric-functions-p
       real-carrier real-zero real-one real-add real-multiply
       real-negate real-inverse real-less sin cos)
      (putnam-1980-a5-coefficients-p
       coefficients real-carrier)
      (putnam-1980-a5-positive-degree-coefficient-p
       coefficients real-zero))
     (and
      (true-listp solutions)
      (putnam-1980-a5-all-common-zeroes-listed-p
       real-carrier real-zero real-add real-multiply real-negate real-less
       measurable measure lintegral sin cos coefficients solutions)))))

(value-triple :itpeval-statement-checked)
:q
