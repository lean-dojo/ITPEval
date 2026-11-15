;; Statement-only formalization of thousand-theorems corpus artifact Q1097021,
;; "Minkowski's theorem": in a finite-dimensional real normed vector space
;; with additive Haar measure, a convex centrally symmetric set whose measure
;; exceeds 2^dim times the measure of a fundamental domain for a countable
;; additive subgroup contains a nonzero point of that subgroup. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, operations, sequences, and families are tame APPLY$
;; function objects.  FN-EQUAL supplies unbounded universal quantification,
;; and inequality with a constant-false function supplies internal
;; existential quantification.  The scalar structure is a Dedekind-complete
;; ordered field, hence a presentation of the real field.  The explicit basis
;; and coordinate map witness finite dimensionality without fixing a finite
;; carrier.  The norm defines the topology, MEASURABLE is required to be its
;; Borel sigma-algebra, and MEASURE is an extended-nonnegative-real-valued
;; countably additive measure with its outer values on arbitrary sets.  Haar
;; measure, an arbitrary countable additive subgroup, and its measurable
;; fundamental domain are represented with all defining laws explicit.
;;
;; A basis and coordinate map witness finite dimensionality, while a
;; surjective natural-number enumeration witnesses countability of the
;; subgroup. Universally closing the resulting statement over either witness
;; is equivalent to assuming existence of that structure, since the
;; conclusion is independent of the choices and all finite bases have the
;; same length.

(defun q1097021-quoted (object)
  (list 'quote object))

(defun q1097021-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1097021-term-list (cdr terms)))
    (q1097021-quoted nil)))

(defun q1097021-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1097021-term-list arguments)))

(defun q1097021-static-apply-term (function arguments)
  (q1097021-apply-term
   (q1097021-quoted function)
   arguments))

(defun q1097021-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1097021-and-terms (cdr terms))
       (q1097021-quoted nil))
    (q1097021-quoted t)))

(defun q1097021-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1097021-quoted t)
       (q1097021-or-terms (cdr terms)))
    (q1097021-quoted nil)))

(defun q1097021-not-term (term)
  (list
   'if
   term
   (q1097021-quoted nil)
   (q1097021-quoted t)))

(defun q1097021-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1097021-quoted t)))

(defun q1097021-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1097021-quoted t)
    (q1097021-quoted nil))
   (list
    'if
    right
    (q1097021-quoted nil)
    (q1097021-quoted t))))

(defun q1097021-true-function (formals)
  (list 'lambda formals (q1097021-quoted t)))

(defun q1097021-false-function (formals)
  (list 'lambda formals (q1097021-quoted nil)))

(defun q1097021-universal-p (function formals)
  (let ((always-true
         (q1097021-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q1097021-exists-p (function formals)
  (let ((always-false
         (q1097021-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun q1097021-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1097021-unary-value (function object)
  (apply$ function (list object)))

(defun q1097021-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets over an arbitrary carrier.

(defun q1097021-set-subset-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(x))
      (q1097021-static-apply-term left '(x))))
    (q1097021-static-apply-term right '(x)))))

(defun q1097021-set-subset-p
    (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q1097021-universal-p
    (q1097021-set-subset-function carrier left right)
    '(x))))

(defun q1097021-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1097021-set-subset-p carrier set carrier)))

(defun q1097021-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-static-apply-term carrier '(x))
    (q1097021-iff-term
     (q1097021-static-apply-term left '(x))
     (q1097021-static-apply-term right '(x))))))

(defun q1097021-set-equiv-p
    (carrier left right)
  (and
   (q1097021-valid-set-p carrier left)
   (q1097021-valid-set-p carrier right)
   (q1097021-universal-p
    (q1097021-set-equiv-function carrier left right)
    '(x))))

(defun q1097021-empty-set ()
  (list 'lambda '(x) (q1097021-quoted nil)))

(defun q1097021-complement-set (carrier set)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (q1097021-not-term
      (q1097021-static-apply-term set '(x)))))))

(defun q1097021-intersection-set (left right)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term left '(x))
     (q1097021-static-apply-term right '(x))))))

(defun q1097021-symmetric-difference-set
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (q1097021-or-terms
      (list
       (q1097021-and-terms
        (list
         (q1097021-static-apply-term left '(x))
         (q1097021-not-term
          (q1097021-static-apply-term right '(x)))))
       (q1097021-and-terms
        (list
         (q1097021-static-apply-term right '(x))
         (q1097021-not-term
          (q1097021-static-apply-term left '(x)))))))))))

(defun q1097021-set-nonempty-function
    (carrier set)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (q1097021-static-apply-term set '(x))))))

(defun q1097021-set-nonempty-p
    (carrier set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-exists-p
    (q1097021-set-nonempty-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q1097021-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add
          (q1097021-static-apply-term add '(x y)))
         (yz-add
          (q1097021-static-apply-term add '(y z)))
         (xy-mul
          (q1097021-static-apply-term multiply '(x y)))
         (yz-mul
          (q1097021-static-apply-term multiply '(y z)))
         (neg-x
          (q1097021-static-apply-term negate '(x)))
         (inv-x
          (q1097021-static-apply-term inverse '(x))))
    (list
     'lambda
     '(x y z)
     (q1097021-implies-term
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term carrier '(x))
        (q1097021-static-apply-term carrier '(y))
        (q1097021-static-apply-term carrier '(z))))
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term carrier (list xy-add))
        (q1097021-static-apply-term carrier (list xy-mul))
        (q1097021-static-apply-term carrier (list neg-x))
        (q1097021-static-apply-term carrier (list inv-x))
        (list
         'equal
         (q1097021-static-apply-term add (list xy-add 'z))
         (q1097021-static-apply-term add (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q1097021-static-apply-term add '(y x)))
        (list
         'equal
         (q1097021-static-apply-term
          add
          (list 'x (q1097021-quoted zero)))
         'x)
        (list
         'equal
         (q1097021-static-apply-term add (list 'x neg-x))
         (q1097021-quoted zero))
        (list
         'equal
         (q1097021-static-apply-term multiply (list xy-mul 'z))
         (q1097021-static-apply-term multiply (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (q1097021-static-apply-term multiply '(y x)))
        (list
         'equal
         (q1097021-static-apply-term
          multiply
          (list 'x (q1097021-quoted one)))
         'x)
        (q1097021-implies-term
         (list 'equal 'x (q1097021-quoted zero))
         (list 'equal inv-x (q1097021-quoted zero)))
        (q1097021-implies-term
         (q1097021-not-term
          (list 'equal 'x (q1097021-quoted zero)))
         (list
          'equal
          (q1097021-static-apply-term
           multiply
           (list 'x inv-x))
          (q1097021-quoted one)))
        (list
         'equal
         (q1097021-static-apply-term multiply (list 'x yz-add))
         (q1097021-static-apply-term
          add
          (list
           (q1097021-static-apply-term multiply '(x y))
           (q1097021-static-apply-term multiply '(x z)))))))))))

(defun q1097021-order-laws-function
    (carrier zero add multiply less)
  (let ((xy
         (q1097021-static-apply-term less '(x y)))
        (yx
         (q1097021-static-apply-term less '(y x)))
        (yz
         (q1097021-static-apply-term less '(y z))))
    (list
     'lambda
     '(x y z)
     (q1097021-implies-term
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term carrier '(x))
        (q1097021-static-apply-term carrier '(y))
        (q1097021-static-apply-term carrier '(z))))
      (q1097021-and-terms
       (list
        (q1097021-not-term
         (q1097021-static-apply-term less '(x x)))
        (q1097021-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q1097021-implies-term
         (q1097021-and-terms (list xy yz))
         (q1097021-static-apply-term less '(x z)))
        (q1097021-implies-term
         xy
         (q1097021-static-apply-term
          less
          (list
           (q1097021-static-apply-term add '(x z))
           (q1097021-static-apply-term add '(y z)))))
        (q1097021-implies-term
         (q1097021-and-terms
          (list
           (q1097021-static-apply-term
            less
            (list (q1097021-quoted zero) 'x))
           (q1097021-static-apply-term
            less
            (list (q1097021-quoted zero) 'y))))
         (q1097021-static-apply-term
          less
          (list
           (q1097021-quoted zero)
           (q1097021-static-apply-term multiply '(x y)))))))))))

(defun q1097021-upper-bound-function
    (carrier less set upper)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(x))
      (q1097021-static-apply-term set '(x))))
    (q1097021-not-term
     (q1097021-static-apply-term
      less
      (list (q1097021-quoted upper) 'x))))))

(defun q1097021-upper-bound-p
    (carrier less set upper)
  (and
   (q1097021-member-p carrier upper)
   (q1097021-valid-set-p carrier set)
   (q1097021-universal-p
    (q1097021-upper-bound-function
     carrier less set upper)
    '(x))))

(defun q1097021-bounded-above-function
    (carrier less set)
  (list
   'lambda
   '(upper)
   (list
    'q1097021-upper-bound-p
    (q1097021-quoted carrier)
    (q1097021-quoted less)
    (q1097021-quoted set)
    'upper)))

(defun q1097021-bounded-above-p
    (carrier less set)
  (q1097021-exists-p
   (q1097021-bounded-above-function carrier less set)
   '(upper)))

(defun q1097021-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda
   '(upper)
   (q1097021-implies-term
    (list
     'q1097021-upper-bound-p
     (q1097021-quoted carrier)
     (q1097021-quoted less)
     (q1097021-quoted set)
     'upper)
    (q1097021-not-term
     (q1097021-static-apply-term
      less
      (list 'upper (q1097021-quoted supremum)))))))

(defun q1097021-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q1097021-upper-bound-p carrier less set supremum)
   (q1097021-universal-p
    (q1097021-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q1097021-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-valid-set-p
       (q1097021-quoted carrier)
       'set)
      (list
       'q1097021-set-nonempty-p
       (q1097021-quoted carrier)
       'set)
      (list
       'q1097021-bounded-above-p
       (q1097021-quoted carrier)
       (q1097021-quoted less)
       'set)))
    (list
     'q1097021-least-upper-bound-p
     (q1097021-quoted carrier)
     (q1097021-quoted less)
     'set
     (q1097021-static-apply-term
      supremum-operation
      '(set))))))

(defun q1097021-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q1097021-member-p carrier zero)
   (q1097021-member-p carrier one)
   (not (equal zero one))
   (q1097021-member-p
    carrier
    (q1097021-unary-value inverse zero))
   (q1097021-universal-p
    (q1097021-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q1097021-universal-p
    (q1097021-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q1097021-member-p
    carrier
    (q1097021-unary-value supremum
                           (q1097021-empty-set)))
   (q1097021-universal-p
    (q1097021-completeness-function
     carrier less supremum)
    '(set))
   (q1097021-binary-value less zero one)))

(defun q1097021-scalar-nonnegative-p
    (less zero value)
  (not (q1097021-binary-value less value zero)))

(defun q1097021-scalar-positive-p
    (carrier less zero value)
  (and
   (q1097021-member-p carrier value)
   (q1097021-binary-value less zero value)))

(defun q1097021-scalar-absolute-value
    (less zero negate value)
  (if (q1097021-binary-value less value zero)
      (q1097021-unary-value negate value)
    value))

(defun q1097021-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q1097021-binary-value
     add
     one
     (q1097021-field-natural
      (- n 1) zero one add))))

(defun q1097021-field-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q1097021-binary-value
     multiply
     base
     (q1097021-field-power
      base (- exponent 1) one multiply))))

;; Finite-dimensional normed vector spaces over the represented real field.

(defun q1097021-vector-laws-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate smul)
  (let* ((xy
          (q1097021-static-apply-term add '(x y)))
         (yz
          (q1097021-static-apply-term add '(y z)))
         (neg-x
          (q1097021-static-apply-term negate '(x)))
         (a-x
          (q1097021-static-apply-term smul '(a x))))
    (list
     'lambda
     '(a b x y z)
     (q1097021-implies-term
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term scalar-carrier '(a))
        (q1097021-static-apply-term scalar-carrier '(b))
        (q1097021-static-apply-term carrier '(x))
        (q1097021-static-apply-term carrier '(y))
        (q1097021-static-apply-term carrier '(z))))
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term carrier (list xy))
        (q1097021-static-apply-term carrier (list neg-x))
        (q1097021-static-apply-term carrier (list a-x))
        (list
         'equal
         (q1097021-static-apply-term add (list xy 'z))
         (q1097021-static-apply-term add (list 'x yz)))
        (list
         'equal
         xy
         (q1097021-static-apply-term add '(y x)))
        (list
         'equal
         (q1097021-static-apply-term
          add
          (list 'x (q1097021-quoted zero)))
         'x)
        (list
         'equal
         (q1097021-static-apply-term add (list 'x neg-x))
         (q1097021-quoted zero))
        (list
         'equal
         (q1097021-static-apply-term
          smul
          (list (q1097021-quoted scalar-one) 'x))
         'x)
        (list
         'equal
         (q1097021-static-apply-term
          smul
          (list
           (q1097021-static-apply-term
            scalar-multiply
            '(a b))
           'x))
         (q1097021-static-apply-term
          smul
          (list
           'a
           (q1097021-static-apply-term smul '(b x)))))
        (list
         'equal
         (q1097021-static-apply-term
          smul
          (list
           (q1097021-static-apply-term scalar-add '(a b))
           'x))
         (q1097021-static-apply-term
          add
          (list
           a-x
           (q1097021-static-apply-term smul '(b x)))))
        (list
         'equal
         (q1097021-static-apply-term smul (list 'a xy))
         (q1097021-static-apply-term
          add
          (list
           a-x
           (q1097021-static-apply-term smul '(a y)))))
        (list
         'equal
         (q1097021-static-apply-term
          smul
          (list (q1097021-quoted scalar-zero) 'x))
         (q1097021-quoted zero))))))))

(defun q1097021-norm-laws-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-negate
     scalar-less carrier zero add negate smul norm)
  (let* ((norm-x
          (q1097021-static-apply-term norm '(x)))
         (norm-y
          (q1097021-static-apply-term norm '(y)))
         (norm-a-x
          (q1097021-static-apply-term
           norm
           (list
            (q1097021-static-apply-term smul '(a x)))))
         (abs-a
          (list
           'q1097021-scalar-absolute-value
           (q1097021-quoted scalar-less)
           (q1097021-quoted scalar-zero)
           (q1097021-quoted scalar-negate)
           'a)))
    (list
     'lambda
     '(a x y)
     (q1097021-implies-term
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term scalar-carrier '(a))
        (q1097021-static-apply-term carrier '(x))
        (q1097021-static-apply-term carrier '(y))))
      (q1097021-and-terms
       (list
        (q1097021-static-apply-term scalar-carrier (list norm-x))
        (q1097021-not-term
         (q1097021-static-apply-term
          scalar-less
          (list norm-x (q1097021-quoted scalar-zero))))
        (q1097021-iff-term
         (list 'equal norm-x (q1097021-quoted scalar-zero))
         (list 'equal 'x (q1097021-quoted zero)))
        (list
         'equal
         (q1097021-static-apply-term
          norm
          (list
           (q1097021-static-apply-term negate '(x))))
         norm-x)
        (list
         'equal
         norm-a-x
         (q1097021-static-apply-term
          scalar-multiply
          (list abs-a norm-x)))
        (q1097021-not-term
         (q1097021-static-apply-term
          scalar-less
          (list
           (q1097021-static-apply-term
            scalar-add
            (list norm-x norm-y))
           (q1097021-static-apply-term
            norm
            (list
             (q1097021-static-apply-term add '(x y)))))))))))))

(defun q1097021-normed-vector-space-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-less
     carrier zero add negate smul norm)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp negate)
   (tamep-functionp smul)
   (tamep-functionp norm)
   (q1097021-member-p carrier zero)
   (q1097021-universal-p
    (q1097021-vector-laws-function
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate smul)
    '(a b x y z))
   (q1097021-universal-p
    (q1097021-norm-laws-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-negate
     scalar-less carrier zero add negate smul norm)
    '(a x y))))

(defun q1097021-coefficient-list-p
    (coefficients basis scalar-carrier)
  (if (consp basis)
      (and
       (consp coefficients)
       (q1097021-member-p scalar-carrier (car coefficients))
       (q1097021-coefficient-list-p
        (cdr coefficients)
        (cdr basis)
        scalar-carrier))
    (equal coefficients nil)))

(defun q1097021-basis-elements-p
    (basis carrier)
  (if (consp basis)
      (and
       (q1097021-member-p carrier (car basis))
       (q1097021-basis-elements-p
        (cdr basis) carrier))
    (equal basis nil)))

(defun q1097021-linear-combination
    (coefficients basis vector-zero vector-add smul)
  (if (consp basis)
      (q1097021-binary-value
       vector-add
       (q1097021-binary-value
        smul
        (car coefficients)
        (car basis))
       (q1097021-linear-combination
        (cdr coefficients)
        (cdr basis)
        vector-zero vector-add smul))
    vector-zero))

(defun q1097021-all-zero-coefficients-p
    (coefficients scalar-zero)
  (if (consp coefficients)
      (and
       (equal (car coefficients) scalar-zero)
       (q1097021-all-zero-coefficients-p
        (cdr coefficients) scalar-zero))
    (equal coefficients nil)))

(defun q1097021-basis-independence-function
    (basis scalar-carrier scalar-zero
           vector-zero vector-add smul)
  (list
   'lambda
   '(coefficients)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-coefficient-list-p
       'coefficients
       (q1097021-quoted basis)
       (q1097021-quoted scalar-carrier))
      (list
       'equal
       (list
        'q1097021-linear-combination
        'coefficients
        (q1097021-quoted basis)
        (q1097021-quoted vector-zero)
        (q1097021-quoted vector-add)
        (q1097021-quoted smul))
       (q1097021-quoted vector-zero))))
    (list
     'q1097021-all-zero-coefficients-p
     'coefficients
     (q1097021-quoted scalar-zero)))))

(defun q1097021-basis-spanning-function
    (basis coordinates scalar-carrier carrier
           vector-zero vector-add smul)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-static-apply-term carrier '(x))
    (q1097021-and-terms
     (list
      (list
       'q1097021-coefficient-list-p
       (q1097021-static-apply-term coordinates '(x))
       (q1097021-quoted basis)
       (q1097021-quoted scalar-carrier))
      (list
       'equal
       (list
        'q1097021-linear-combination
        (q1097021-static-apply-term coordinates '(x))
        (q1097021-quoted basis)
        (q1097021-quoted vector-zero)
        (q1097021-quoted vector-add)
        (q1097021-quoted smul))
       'x))))))

(defun q1097021-finite-basis-p
    (basis coordinates scalar-carrier scalar-zero
           carrier vector-zero vector-add smul)
  (and
   (true-listp basis)
   (tamep-functionp coordinates)
   (q1097021-basis-elements-p basis carrier)
   (q1097021-universal-p
    (q1097021-basis-independence-function
     basis scalar-carrier scalar-zero
     vector-zero vector-add smul)
    '(coefficients))
   (q1097021-universal-p
    (q1097021-basis-spanning-function
     basis coordinates scalar-carrier carrier
     vector-zero vector-add smul)
    '(x))))

;; Norm topology, convergence, and compactness.

(defun q1097021-vector-difference
    (add negate left right)
  (q1097021-binary-value
   add left (q1097021-unary-value negate right)))

(defun q1097021-distance-less-p
    (scalar-less vector-add vector-negate norm
                 left right epsilon)
  (q1097021-binary-value
   scalar-less
   (q1097021-unary-value
    norm
    (q1097021-vector-difference
     vector-add vector-negate left right))
   epsilon))

(defun q1097021-ball-subset-function
    (carrier vector-add vector-negate norm scalar-less
             center epsilon set)
  (list
   'lambda
   '(y)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(y))
      (list
       'q1097021-distance-less-p
       (q1097021-quoted scalar-less)
       (q1097021-quoted vector-add)
       (q1097021-quoted vector-negate)
       (q1097021-quoted norm)
       (q1097021-quoted center)
       'y
       (q1097021-quoted epsilon))))
    (q1097021-static-apply-term set '(y)))))

(defun q1097021-ball-subset-p
    (carrier vector-add vector-negate norm scalar-less
             center epsilon set)
  (q1097021-universal-p
   (q1097021-ball-subset-function
    carrier vector-add vector-negate norm scalar-less
    center epsilon set)
   '(y)))

(defun q1097021-open-radius-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set x)
  (list
   'lambda
   '(epsilon)
   (q1097021-and-terms
    (list
     (list
      'q1097021-scalar-positive-p
      (q1097021-quoted scalar-carrier)
      (q1097021-quoted scalar-less)
      (q1097021-quoted scalar-zero)
      'epsilon)
     (list
      'q1097021-ball-subset-p
      (q1097021-quoted carrier)
      (q1097021-quoted vector-add)
      (q1097021-quoted vector-negate)
      (q1097021-quoted norm)
      (q1097021-quoted scalar-less)
      (q1097021-quoted x)
      'epsilon
      (q1097021-quoted set))))))

(defun q1097021-open-radius-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set x)
  (q1097021-exists-p
   (q1097021-open-radius-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm set x)
   '(epsilon)))

(defun q1097021-open-set-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(x))
      (q1097021-static-apply-term set '(x))))
    (list
     'q1097021-open-radius-exists-p
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-less)
     (q1097021-quoted carrier)
     (q1097021-quoted vector-add)
     (q1097021-quoted vector-negate)
     (q1097021-quoted norm)
     (q1097021-quoted set)
     'x))))

(defun q1097021-open-set-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-universal-p
    (q1097021-open-set-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    '(x))))

(defun q1097021-sequence-in-set-function
    (carrier set sequence)
  (list
   'lambda
   '(n)
   (q1097021-implies-term
    (list 'natp 'n)
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term
       carrier
       (list
        (q1097021-static-apply-term sequence '(n))))
      (q1097021-static-apply-term
       set
       (list
        (q1097021-static-apply-term sequence '(n)))))))))

(defun q1097021-sequence-in-set-p
    (carrier set sequence)
  (and
   (tamep-functionp sequence)
   (q1097021-universal-p
    (q1097021-sequence-in-set-function
     carrier set sequence)
    '(n))))

(defun q1097021-convergence-tail-function
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon start)
  (list
   'lambda
   '(n)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q1097021-quoted start) 'n)))
    (list
     'q1097021-distance-less-p
     (q1097021-quoted scalar-less)
     (q1097021-quoted vector-add)
     (q1097021-quoted vector-negate)
     (q1097021-quoted norm)
     (q1097021-static-apply-term sequence '(n))
     (q1097021-quoted limit)
     (q1097021-quoted epsilon)))))

(defun q1097021-convergence-tail-p
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon start)
  (and
   (natp start)
   (q1097021-universal-p
    (q1097021-convergence-tail-function
     vector-add vector-negate norm scalar-less
     sequence limit epsilon start)
    '(n))))

(defun q1097021-convergence-start-function
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon)
  (list
   'lambda
   '(start)
   (list
    'q1097021-convergence-tail-p
    (q1097021-quoted vector-add)
    (q1097021-quoted vector-negate)
    (q1097021-quoted norm)
    (q1097021-quoted scalar-less)
    (q1097021-quoted sequence)
    (q1097021-quoted limit)
    (q1097021-quoted epsilon)
    'start)))

(defun q1097021-convergence-start-exists-p
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon)
  (q1097021-exists-p
   (q1097021-convergence-start-function
    vector-add vector-negate norm scalar-less
    sequence limit epsilon)
   '(start)))

(defun q1097021-convergence-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     vector-add vector-negate norm sequence limit)
  (list
   'lambda
   '(epsilon)
   (q1097021-implies-term
    (list
     'q1097021-scalar-positive-p
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-less)
     (q1097021-quoted scalar-zero)
     'epsilon)
    (list
     'q1097021-convergence-start-exists-p
     (q1097021-quoted vector-add)
     (q1097021-quoted vector-negate)
     (q1097021-quoted norm)
     (q1097021-quoted scalar-less)
     (q1097021-quoted sequence)
     (q1097021-quoted limit)
     'epsilon))))

(defun q1097021-converges-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm sequence limit)
  (and
   (tamep-functionp sequence)
   (q1097021-member-p carrier limit)
   (q1097021-universal-p
    (q1097021-convergence-epsilon-function
     scalar-carrier scalar-zero scalar-less
     vector-add vector-negate norm sequence limit)
    '(epsilon))))

(defun q1097021-subsequence-laws-function
    (subsequence)
  (list
   'lambda
   '(m n)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)))
    (q1097021-and-terms
     (list
      (list
       'natp
       (q1097021-static-apply-term subsequence '(m)))
      (q1097021-implies-term
       (list '< 'm 'n)
       (list
        '<
        (q1097021-static-apply-term subsequence '(m))
        (q1097021-static-apply-term subsequence '(n)))))))))

(defun q1097021-subsequence-p (subsequence)
  (and
   (tamep-functionp subsequence)
   (q1097021-universal-p
    (q1097021-subsequence-laws-function subsequence)
    '(m n))))

(defun q1097021-compose-sequence
    (sequence subsequence)
  (list
   'lambda
   '(n)
   (q1097021-static-apply-term
    sequence
    (list
     (q1097021-static-apply-term subsequence '(n))))))

(defun q1097021-compact-witness-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     set sequence subsequence limit)
  (and
   (q1097021-subsequence-p subsequence)
   (q1097021-member-p carrier limit)
   (q1097021-member-p set limit)
   (q1097021-converges-p
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm
    (q1097021-compose-sequence sequence subsequence)
    limit)))

(defun q1097021-compact-witness-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set sequence)
  (list
   'lambda
   '(subsequence limit)
   (list
    'q1097021-compact-witness-p
    (q1097021-quoted scalar-carrier)
    (q1097021-quoted scalar-zero)
    (q1097021-quoted scalar-less)
    (q1097021-quoted carrier)
    (q1097021-quoted vector-add)
    (q1097021-quoted vector-negate)
    (q1097021-quoted norm)
    (q1097021-quoted set)
    (q1097021-quoted sequence)
    'subsequence
    'limit)))

(defun q1097021-compact-witness-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set sequence)
  (q1097021-exists-p
   (q1097021-compact-witness-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm set sequence)
   '(subsequence limit)))

(defun q1097021-compact-set-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (list
   'lambda
   '(sequence)
   (q1097021-implies-term
    (list
     'q1097021-sequence-in-set-p
     (q1097021-quoted carrier)
     (q1097021-quoted set)
     'sequence)
    (list
     'q1097021-compact-witness-exists-p
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-less)
     (q1097021-quoted carrier)
     (q1097021-quoted vector-add)
     (q1097021-quoted vector-negate)
     (q1097021-quoted norm)
     (q1097021-quoted set)
     'sequence))))

(defun q1097021-compact-set-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-universal-p
    (q1097021-compact-set-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    '(sequence))))

;; The Borel sigma-algebra generated by the norm topology.

(defun q1097021-family-extensional-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-valid-set-p
       (q1097021-quoted carrier)
       'left)
      (list
       'q1097021-valid-set-p
       (q1097021-quoted carrier)
       'right)
      (list
       'q1097021-set-equiv-p
       (q1097021-quoted carrier)
       'left
       'right)))
    (q1097021-iff-term
     (q1097021-static-apply-term family '(left))
     (q1097021-static-apply-term family '(right))))))

(defun q1097021-family-members-valid-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (q1097021-static-apply-term family '(set))
    (list
     'q1097021-valid-set-p
     (q1097021-quoted carrier)
     'set))))

(defun q1097021-family-of-sets-p
    (carrier family)
  (and
   (tamep-functionp family)
   (q1097021-universal-p
    (q1097021-family-extensional-function carrier family)
    '(left right))
   (q1097021-universal-p
    (q1097021-family-members-valid-function carrier family)
    '(set))))

(defun q1097021-sequence-union-member-function
    (sequence x)
  (list
   'lambda
   '(n)
   (q1097021-and-terms
    (list
     (list 'natp 'n)
     (q1097021-apply-term
      (q1097021-static-apply-term sequence '(n))
      (list (q1097021-quoted x)))))))

(defun q1097021-sequence-union-member-p
    (sequence x)
  (q1097021-exists-p
   (q1097021-sequence-union-member-function sequence x)
   '(n)))

(defun q1097021-sequence-union-set
    (carrier sequence)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (list
      'q1097021-sequence-union-member-p
      (q1097021-quoted sequence)
      'x)))))

(defun q1097021-sequence-of-sets-function
    (carrier sequence)
  (list
   'lambda
   '(n)
   (q1097021-implies-term
    (list 'natp 'n)
    (list
     'q1097021-valid-set-p
     (q1097021-quoted carrier)
     (q1097021-static-apply-term sequence '(n))))))

(defun q1097021-sequence-of-sets-p
    (carrier sequence)
  (and
   (tamep-functionp sequence)
   (q1097021-universal-p
    (q1097021-sequence-of-sets-function
     carrier sequence)
    '(n))))

(defun q1097021-sequence-members-family-function
    (family sequence)
  (list
   'lambda
   '(n)
   (q1097021-implies-term
    (list 'natp 'n)
    (q1097021-static-apply-term
     family
     (list
      (q1097021-static-apply-term sequence '(n)))))))

(defun q1097021-sequence-members-family-p
    (carrier family sequence)
  (and
   (q1097021-sequence-of-sets-p carrier sequence)
   (q1097021-universal-p
    (q1097021-sequence-members-family-function
     family sequence)
    '(n))))

(defun q1097021-sigma-complement-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (q1097021-static-apply-term family '(set))
    (q1097021-static-apply-term
     family
     (list
      (list
       'q1097021-complement-set
       (q1097021-quoted carrier)
       'set))))))

(defun q1097021-sigma-union-function
    (carrier family)
  (list
   'lambda
   '(sequence)
   (q1097021-implies-term
    (list
     'q1097021-sequence-members-family-p
     (q1097021-quoted carrier)
     (q1097021-quoted family)
     'sequence)
    (q1097021-static-apply-term
     family
     (list
      (list
       'q1097021-sequence-union-set
       (q1097021-quoted carrier)
       'sequence))))))

(defun q1097021-sigma-algebra-p
    (carrier family)
  (and
   (q1097021-family-of-sets-p carrier family)
   (q1097021-member-p family (q1097021-empty-set))
   (q1097021-universal-p
    (q1097021-sigma-complement-function carrier family)
    '(set))
   (q1097021-universal-p
    (q1097021-sigma-union-function carrier family)
    '(sequence))))

(defun q1097021-contains-open-sets-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm family)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (list
     'q1097021-open-set-p
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-less)
     (q1097021-quoted carrier)
     (q1097021-quoted vector-add)
     (q1097021-quoted vector-negate)
     (q1097021-quoted norm)
     'set)
    (q1097021-static-apply-term family '(set)))))

(defun q1097021-contains-open-sets-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm family)
  (q1097021-universal-p
   (q1097021-contains-open-sets-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm family)
   '(set)))

(defun q1097021-family-subset-function
    (left right)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (q1097021-static-apply-term left '(set))
    (q1097021-static-apply-term right '(set)))))

(defun q1097021-family-subset-p
    (left right)
  (q1097021-universal-p
   (q1097021-family-subset-function left right)
   '(set)))

(defun q1097021-borel-minimality-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
  (list
   'lambda
   '(candidate)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-sigma-algebra-p
       (q1097021-quoted carrier)
       'candidate)
      (list
       'q1097021-contains-open-sets-p
       (q1097021-quoted scalar-carrier)
       (q1097021-quoted scalar-zero)
       (q1097021-quoted scalar-less)
       (q1097021-quoted carrier)
       (q1097021-quoted vector-add)
       (q1097021-quoted vector-negate)
       (q1097021-quoted norm)
       'candidate)))
    (list
     'q1097021-family-subset-p
     (q1097021-quoted measurable)
     'candidate))))

(defun q1097021-borel-space-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
  (and
   (q1097021-sigma-algebra-p carrier measurable)
   (q1097021-contains-open-sets-p
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm measurable)
   (q1097021-universal-p
    (q1097021-borel-minimality-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
    '(candidate))))

;; Extended nonnegative real values built from the represented real field.

(defun q1097021-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :q1097021-top)
   (and
    (consp value)
    (equal (car value) :q1097021-finite)
    (q1097021-member-p scalar-carrier (cdr value))
    (q1097021-scalar-nonnegative-p
     scalar-less scalar-zero (cdr value)))))

(defun q1097021-ennreal-finite (value)
  (cons :q1097021-finite value))

(defun q1097021-ennreal-zero (scalar-zero)
  (q1097021-ennreal-finite scalar-zero))

(defun q1097021-ennreal-less-p
    (left right scalar-less)
  (cond
   ((equal left :q1097021-top) nil)
   ((equal right :q1097021-top) t)
   (t
    (q1097021-binary-value
     scalar-less (cdr left) (cdr right)))))

(defun q1097021-ennreal-less-equal-p
    (left right scalar-less)
  (not
   (q1097021-ennreal-less-p
    right left scalar-less)))

(defun q1097021-ennreal-add
    (left right scalar-add)
  (if (or (equal left :q1097021-top)
          (equal right :q1097021-top))
      :q1097021-top
    (q1097021-ennreal-finite
     (q1097021-binary-value
      scalar-add (cdr left) (cdr right)))))

(defun q1097021-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left
               (q1097021-ennreal-zero scalar-zero))
        (equal right
               (q1097021-ennreal-zero scalar-zero)))
    (q1097021-ennreal-zero scalar-zero))
   ((or (equal left :q1097021-top)
        (equal right :q1097021-top))
    :q1097021-top)
   (t
    (q1097021-ennreal-finite
     (q1097021-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun q1097021-ennreal-two-power
    (dimension scalar-zero scalar-one scalar-add scalar-multiply)
  (q1097021-ennreal-finite
   (q1097021-field-power
    (q1097021-field-natural
     2 scalar-zero scalar-one scalar-add)
    dimension scalar-one scalar-multiply)))

;; Countably additive Borel measures and their values on arbitrary sets.

(defun q1097021-measure-extensional-function
    (carrier measure)
  (list
   'lambda
   '(left right)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-set-equiv-p
       (q1097021-quoted carrier)
       'left
       'right)))
    (list
     'equal
     (q1097021-static-apply-term measure '(left))
     (q1097021-static-apply-term measure '(right))))))

(defun q1097021-measure-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measure)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (list
     'q1097021-valid-set-p
     (q1097021-quoted carrier)
     'set)
    (list
     'q1097021-ennreal-p
     (q1097021-static-apply-term measure '(set))
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-less)))))

(defun q1097021-finite-measure-sum
    (measure sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q1097021-ennreal-zero scalar-zero)
    (q1097021-ennreal-add
     (q1097021-finite-measure-sum
      measure sequence (- count 1)
      scalar-zero scalar-add)
     (q1097021-unary-value
      measure
      (q1097021-unary-value
       sequence (- count 1)))
     scalar-add)))

(defun q1097021-sum-upper-bound-function
    (measure sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda
   '(count)
   (q1097021-implies-term
    (list 'natp 'count)
    (list
     'q1097021-ennreal-less-equal-p
     (list
      'q1097021-finite-measure-sum
      (q1097021-quoted measure)
      (q1097021-quoted sequence)
      'count
      (q1097021-quoted scalar-zero)
      (q1097021-quoted scalar-add))
     (q1097021-quoted total)
     (q1097021-quoted scalar-less)))))

(defun q1097021-sum-upper-bound-p
    (measure sequence total scalar-zero scalar-add scalar-less)
  (q1097021-universal-p
   (q1097021-sum-upper-bound-function
    measure sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun q1097021-sum-least-function
    (measure sequence total
             scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda
   '(bound)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-ennreal-p
       'bound
       (q1097021-quoted scalar-carrier)
       (q1097021-quoted scalar-zero)
       (q1097021-quoted scalar-less))
      (list
       'q1097021-sum-upper-bound-p
       (q1097021-quoted measure)
       (q1097021-quoted sequence)
       'bound
       (q1097021-quoted scalar-zero)
       (q1097021-quoted scalar-add)
       (q1097021-quoted scalar-less))))
    (list
     'q1097021-ennreal-less-equal-p
     (q1097021-quoted total)
     'bound
     (q1097021-quoted scalar-less)))))

(defun q1097021-countable-sum-p
    (measure sequence total
             scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (q1097021-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (q1097021-sum-upper-bound-p
    measure sequence total
    scalar-zero scalar-add scalar-less)
   (q1097021-universal-p
    (q1097021-sum-least-function
     measure sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

(defun q1097021-disjoint-sets-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-static-apply-term carrier '(x))
    (q1097021-not-term
     (q1097021-and-terms
      (list
       (q1097021-static-apply-term left '(x))
       (q1097021-static-apply-term right '(x))))))))

(defun q1097021-disjoint-sets-p
    (carrier left right)
  (q1097021-universal-p
   (q1097021-disjoint-sets-function carrier left right)
   '(x)))

(defun q1097021-pairwise-disjoint-sequence-function
    (carrier sequence)
  (list
   'lambda
   '(m n)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (q1097021-not-term (list 'equal 'm 'n))))
    (list
     'q1097021-disjoint-sets-p
     (q1097021-quoted carrier)
     (q1097021-static-apply-term sequence '(m))
     (q1097021-static-apply-term sequence '(n))))))

(defun q1097021-pairwise-disjoint-sequence-p
    (carrier sequence)
  (q1097021-universal-p
   (q1097021-pairwise-disjoint-sequence-function
    carrier sequence)
   '(m n)))

(defun q1097021-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda
   '(sequence)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-sequence-members-family-p
       (q1097021-quoted carrier)
       (q1097021-quoted measurable)
       'sequence)
      (list
       'q1097021-pairwise-disjoint-sequence-p
       (q1097021-quoted carrier)
       'sequence)))
    (list
     'q1097021-countable-sum-p
     (q1097021-quoted measure)
     'sequence
     (q1097021-static-apply-term
      measure
      (list
       (list
        'q1097021-sequence-union-set
        (q1097021-quoted carrier)
        'sequence)))
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-add)
     (q1097021-quoted scalar-less)))))

(defun q1097021-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda
   '(superset)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term measurable '(superset))
      (list
       'q1097021-set-subset-p
       (q1097021-quoted carrier)
       (q1097021-quoted set)
       'superset)))
    (list
     'q1097021-ennreal-less-equal-p
     (q1097021-quoted lower)
     (q1097021-static-apply-term measure '(superset))
     (q1097021-quoted scalar-less)))))

(defun q1097021-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (q1097021-universal-p
   (q1097021-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun q1097021-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda
   '(lower)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-ennreal-p
       'lower
       (q1097021-quoted scalar-carrier)
       (q1097021-quoted scalar-zero)
       (q1097021-quoted scalar-less))
      (list
       'q1097021-measurable-superset-lower-bound-p
       (q1097021-quoted carrier)
       (q1097021-quoted measurable)
       (q1097021-quoted measure)
       (q1097021-quoted set)
       'lower
       (q1097021-quoted scalar-less))))
    (list
     'q1097021-ennreal-less-equal-p
     'lower
     (q1097021-static-apply-term measure (list (q1097021-quoted set)))
     (q1097021-quoted scalar-less)))))

(defun q1097021-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-measurable-superset-lower-bound-p
    carrier measurable measure set
    (q1097021-unary-value measure set)
    scalar-less)
   (q1097021-universal-p
    (q1097021-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun q1097021-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (list
     'q1097021-valid-set-p
     (q1097021-quoted carrier)
     'set)
    (list
     'q1097021-outer-value-p
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-less)
     (q1097021-quoted carrier)
     (q1097021-quoted measurable)
     (q1097021-quoted measure)
     'set))))

(defun q1097021-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (tamep-functionp measure)
   (q1097021-universal-p
    (q1097021-measure-extensional-function
     carrier measure)
    '(left right))
   (q1097021-universal-p
    (q1097021-measure-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measure)
    '(set))
   (equal
    (q1097021-unary-value measure (q1097021-empty-set))
    (q1097021-ennreal-zero scalar-zero))
   (q1097021-universal-p
    (q1097021-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (q1097021-universal-p
    (q1097021-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; Haar measure: translation invariance, compact finiteness, and positivity
;; on every nonempty open set.

(defun q1097021-translate-set
    (carrier vector-add vector-negate shift set)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (q1097021-static-apply-term
      set
      (list
       (q1097021-static-apply-term
        vector-add
        (list
         (q1097021-static-apply-term
          vector-negate
          (list (q1097021-quoted shift)))
         'x))))))))

(defun q1097021-translation-invariance-function
    (carrier vector-add vector-negate measure)
  (list
   'lambda
   '(shift set)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(shift))
      (list
       'q1097021-valid-set-p
       (q1097021-quoted carrier)
       'set)))
    (list
     'equal
     (q1097021-static-apply-term
      measure
      (list
       (list
        'q1097021-translate-set
        (q1097021-quoted carrier)
        (q1097021-quoted vector-add)
        (q1097021-quoted vector-negate)
        'shift
        'set)))
     (q1097021-static-apply-term measure '(set))))))

(defun q1097021-compact-finite-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (list
     'q1097021-compact-set-p
     (q1097021-quoted scalar-carrier)
     (q1097021-quoted scalar-zero)
     (q1097021-quoted scalar-less)
     (q1097021-quoted carrier)
     (q1097021-quoted vector-add)
     (q1097021-quoted vector-negate)
     (q1097021-quoted norm)
     'set)
    (q1097021-not-term
     (list
      'equal
      (q1097021-static-apply-term measure '(set))
      (q1097021-quoted :q1097021-top))))))

(defun q1097021-open-positive-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
  (list
   'lambda
   '(set)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (list
       'q1097021-open-set-p
       (q1097021-quoted scalar-carrier)
       (q1097021-quoted scalar-zero)
       (q1097021-quoted scalar-less)
       (q1097021-quoted carrier)
       (q1097021-quoted vector-add)
       (q1097021-quoted vector-negate)
       (q1097021-quoted norm)
       'set)
      (list
       'q1097021-set-nonempty-p
       (q1097021-quoted carrier)
       'set)))
    (list
     'q1097021-ennreal-less-p
     (list
      'q1097021-ennreal-zero
      (q1097021-quoted scalar-zero))
     (q1097021-static-apply-term measure '(set))
     (q1097021-quoted scalar-less)))))

(defun q1097021-add-haar-measure-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
  (and
   (q1097021-universal-p
    (q1097021-translation-invariance-function
     carrier vector-add vector-negate measure)
    '(shift set))
   (q1097021-universal-p
    (q1097021-compact-finite-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
    '(set))
   (q1097021-universal-p
    (q1097021-open-positive-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
    '(set))))

;; Countable additive subgroups and measurable fundamental domains.

(defun q1097021-add-subgroup-laws-function
    (carrier add negate subgroup)
  (list
   'lambda
   '(x y)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term subgroup '(x))
      (q1097021-static-apply-term subgroup '(y))))
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(x))
      (q1097021-static-apply-term carrier '(y))
      (q1097021-static-apply-term
       subgroup
       (list
        (q1097021-static-apply-term add '(x y))))
      (q1097021-static-apply-term
       subgroup
       (list
        (q1097021-static-apply-term negate '(x)))))))))

(defun q1097021-add-subgroup-p
    (carrier zero add negate subgroup)
  (and
   (q1097021-valid-set-p carrier subgroup)
   (q1097021-member-p subgroup zero)
   (q1097021-universal-p
    (q1097021-add-subgroup-laws-function
     carrier add negate subgroup)
    '(x y))))

(defun q1097021-enumeration-values-function
    (subgroup enumeration)
  (list
   'lambda
   '(n)
   (q1097021-implies-term
    (list 'natp 'n)
    (q1097021-static-apply-term
     subgroup
     (list
      (q1097021-static-apply-term enumeration '(n)))))))

(defun q1097021-enumeration-hit-function
    (enumeration x)
  (list
   'lambda
   '(n)
   (q1097021-and-terms
    (list
     (list 'natp 'n)
     (list
      'equal
      (q1097021-static-apply-term enumeration '(n))
      (q1097021-quoted x))))))

(defun q1097021-enumeration-hits-p
    (enumeration x)
  (q1097021-exists-p
   (q1097021-enumeration-hit-function enumeration x)
   '(n)))

(defun q1097021-enumeration-covers-function
    (subgroup enumeration)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-static-apply-term subgroup '(x))
    (list
     'q1097021-enumeration-hits-p
     (q1097021-quoted enumeration)
     'x))))

(defun q1097021-countable-subgroup-p
    (subgroup enumeration)
  (and
   (tamep-functionp enumeration)
   (q1097021-universal-p
    (q1097021-enumeration-values-function
     subgroup enumeration)
    '(n))
   (q1097021-universal-p
    (q1097021-enumeration-covers-function
     subgroup enumeration)
    '(x))))

(defun q1097021-null-measurable-witness-function
    (scalar-zero carrier measurable measure set)
  (list
   'lambda
   '(measurable-set)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term
      measurable
      '(measurable-set))
     (list
      'equal
      (q1097021-static-apply-term
       measure
       (list
        (list
         'q1097021-symmetric-difference-set
         (q1097021-quoted carrier)
         (q1097021-quoted set)
         'measurable-set)))
      (list
       'q1097021-ennreal-zero
       (q1097021-quoted scalar-zero)))))))

(defun q1097021-null-measurable-set-p
    (scalar-zero carrier measurable measure set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-exists-p
    (q1097021-null-measurable-witness-function
     scalar-zero carrier measurable measure set)
    '(measurable-set))))

(defun q1097021-covering-shift-function
    (subgroup vector-add fundamental-set x)
  (list
   'lambda
   '(g)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term subgroup '(g))
     (q1097021-static-apply-term
      fundamental-set
      (list
       (q1097021-static-apply-term
        vector-add
        (list 'g (q1097021-quoted x)))))))))

(defun q1097021-covering-shift-exists-p
    (subgroup vector-add fundamental-set x)
  (q1097021-exists-p
   (q1097021-covering-shift-function
    subgroup vector-add fundamental-set x)
   '(g)))

(defun q1097021-cover-failure-set
    (carrier subgroup vector-add fundamental-set)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (q1097021-not-term
      (list
       'q1097021-covering-shift-exists-p
       (q1097021-quoted subgroup)
       (q1097021-quoted vector-add)
       (q1097021-quoted fundamental-set)
       'x))))))

(defun q1097021-fundamental-ae-covers-p
    (scalar-zero carrier subgroup vector-add
     fundamental-set measure)
  (equal
   (q1097021-unary-value
    measure
    (q1097021-cover-failure-set
     carrier subgroup vector-add fundamental-set))
   (q1097021-ennreal-zero scalar-zero)))

(defun q1097021-aedisjoint-translates-function
    (scalar-zero carrier subgroup vector-add vector-negate
     fundamental-set measure)
  (list
   'lambda
   '(g h)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term subgroup '(g))
      (q1097021-static-apply-term subgroup '(h))
      (q1097021-not-term (list 'equal 'g 'h))))
    (list
     'equal
     (q1097021-static-apply-term
      measure
      (list
       (list
        'q1097021-intersection-set
        (list
         'q1097021-translate-set
         (q1097021-quoted carrier)
         (q1097021-quoted vector-add)
         (q1097021-quoted vector-negate)
         'g
         (q1097021-quoted fundamental-set))
        (list
         'q1097021-translate-set
         (q1097021-quoted carrier)
         (q1097021-quoted vector-add)
         (q1097021-quoted vector-negate)
         'h
         (q1097021-quoted fundamental-set)))))
     (list
      'q1097021-ennreal-zero
      (q1097021-quoted scalar-zero))))))

(defun q1097021-add-fundamental-domain-p
    (scalar-zero carrier subgroup vector-add vector-negate
     measurable measure fundamental-set)
  (and
   (q1097021-null-measurable-set-p
    scalar-zero carrier measurable measure fundamental-set)
   (q1097021-fundamental-ae-covers-p
    scalar-zero carrier subgroup vector-add
    fundamental-set measure)
   (q1097021-universal-p
    (q1097021-aedisjoint-translates-function
     scalar-zero carrier subgroup vector-add vector-negate
     fundamental-set measure)
    '(g h))))

;; Symmetry, convexity, the strict covolume inequality, and the internal
;; nonzero lattice-point conclusion.

(defun q1097021-symmetric-set-function
    (carrier vector-negate set)
  (list
   'lambda
   '(x)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term carrier '(x))
      (q1097021-static-apply-term set '(x))))
    (q1097021-static-apply-term
     set
     (list
      (q1097021-static-apply-term vector-negate '(x)))))))

(defun q1097021-symmetric-set-p
    (carrier vector-negate set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-universal-p
    (q1097021-symmetric-set-function
     carrier vector-negate set)
    '(x))))

(defun q1097021-convex-set-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
  (list
   'lambda
   '(a b x y)
   (q1097021-implies-term
    (q1097021-and-terms
     (list
      (q1097021-static-apply-term scalar-carrier '(a))
      (q1097021-static-apply-term scalar-carrier '(b))
      (q1097021-not-term
       (q1097021-static-apply-term
        scalar-less
        (list 'a (q1097021-quoted scalar-zero))))
      (q1097021-not-term
       (q1097021-static-apply-term
        scalar-less
        (list 'b (q1097021-quoted scalar-zero))))
      (list
       'equal
       (q1097021-static-apply-term scalar-add '(a b))
       (q1097021-quoted scalar-one))
      (q1097021-static-apply-term carrier '(x))
      (q1097021-static-apply-term carrier '(y))
      (q1097021-static-apply-term set '(x))
      (q1097021-static-apply-term set '(y))))
    (q1097021-static-apply-term
     set
     (list
      (q1097021-static-apply-term
       vector-add
       (list
        (q1097021-static-apply-term smul '(a x))
        (q1097021-static-apply-term smul '(b y)))))))))

(defun q1097021-convex-set-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
  (and
   (q1097021-valid-set-p carrier set)
   (q1097021-universal-p
    (q1097021-convex-set-function
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
    '(a b x y))))

(defun q1097021-large-measure-p
    (basis scalar-zero scalar-one scalar-add scalar-multiply scalar-less
     measure fundamental-set set)
  (q1097021-ennreal-less-p
   (q1097021-ennreal-multiply
    (q1097021-unary-value measure fundamental-set)
    (q1097021-ennreal-two-power
     (len basis)
     scalar-zero scalar-one scalar-add scalar-multiply)
    scalar-zero scalar-multiply)
   (q1097021-unary-value measure set)
   scalar-less))

(defun q1097021-nonzero-lattice-point-function
    (carrier vector-zero subgroup set)
  (list
   'lambda
   '(x)
   (q1097021-and-terms
    (list
     (q1097021-static-apply-term carrier '(x))
     (q1097021-static-apply-term subgroup '(x))
     (q1097021-not-term
      (list 'equal 'x (q1097021-quoted vector-zero)))
     (q1097021-static-apply-term set '(x))))))

(defun q1097021-nonzero-lattice-point-exists-p
    (carrier vector-zero subgroup set)
  (q1097021-exists-p
   (q1097021-nonzero-lattice-point-function
    carrier vector-zero subgroup set)
   '(x)))

(defun thousand-theorems-q1097021-minkowski-theorem-statement
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse scalar-less scalar-supremum
     carrier vector-zero vector-add vector-negate smul norm
     basis coordinates measurable measure subgroup enumeration
     fundamental-set set)
  (implies
   (and
    (q1097021-real-field-p
     scalar-carrier scalar-zero scalar-one
     scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-less scalar-supremum)
    (q1097021-normed-vector-space-p
     scalar-carrier scalar-zero scalar-one
     scalar-add scalar-multiply scalar-negate scalar-less
     carrier vector-zero vector-add vector-negate smul norm)
    (q1097021-finite-basis-p
     basis coordinates scalar-carrier scalar-zero
     carrier vector-zero vector-add smul)
    (q1097021-borel-space-p
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
    (q1097021-measure-space-p
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    (q1097021-add-haar-measure-p
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
    (q1097021-add-subgroup-p
     carrier vector-zero vector-add vector-negate subgroup)
    (q1097021-countable-subgroup-p subgroup enumeration)
    (q1097021-add-fundamental-domain-p
     scalar-zero carrier subgroup vector-add vector-negate
     measurable measure fundamental-set)
    (q1097021-symmetric-set-p carrier vector-negate set)
    (q1097021-convex-set-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
    (q1097021-large-measure-p
     basis scalar-zero scalar-one scalar-add scalar-multiply scalar-less
     measure fundamental-set set))
   (q1097021-nonzero-lattice-point-exists-p
    carrier vector-zero subgroup set)))

(value-triple :itpeval-statement-checked)
:q
