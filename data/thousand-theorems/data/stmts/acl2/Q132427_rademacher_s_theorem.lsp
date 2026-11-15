;; Statement-only formalization of thousand-theorems corpus artifact Q132427,
;; "Rademacher's theorem": a map between finite-dimensional real normed vector
;; spaces that is Lipschitz on a measurable set is differentiable within that
;; set almost everywhere for an additive Haar measure. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers, sets, operations, sequences, and families are tame APPLY$
;; function objects.  FN-EQUAL supplies unbounded universal quantification,
;; and inequality with a constant-false function supplies internal
;; existential quantification.  The scalar structure is a Dedekind-complete
;; ordered field, hence a presentation of the real field.  Explicit finite
;; bases and coordinate maps witness finite dimensionality without fixing
;; finite carriers.  The domain norm defines its Borel sigma-algebra, and the
;; measure has extended-nonnegative-real outer values on arbitrary sets.
;; Lipschitz continuity and the Frechet derivative within the set are expanded
;; below, including the internal existential quantifier over the derivative.

(defun q132427-quoted (object)
  (list 'quote object))

(defun q132427-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q132427-term-list (cdr terms)))
    (q132427-quoted nil)))

(defun q132427-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q132427-term-list arguments)))

(defun q132427-static-apply-term (function arguments)
  (q132427-apply-term
   (q132427-quoted function)
   arguments))

(defun q132427-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q132427-and-terms (cdr terms))
       (q132427-quoted nil))
    (q132427-quoted t)))

(defun q132427-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q132427-quoted t)
       (q132427-or-terms (cdr terms)))
    (q132427-quoted nil)))

(defun q132427-not-term (term)
  (list
   'if
   term
   (q132427-quoted nil)
   (q132427-quoted t)))

(defun q132427-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q132427-quoted t)))

(defun q132427-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q132427-quoted t)
    (q132427-quoted nil))
   (list
    'if
    right
    (q132427-quoted nil)
    (q132427-quoted t))))

(defun q132427-true-function (formals)
  (list 'lambda formals (q132427-quoted t)))

(defun q132427-false-function (formals)
  (list 'lambda formals (q132427-quoted nil)))

(defun q132427-universal-p (function formals)
  (let ((always-true
         (q132427-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q132427-exists-p (function formals)
  (let ((always-false
         (q132427-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun q132427-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q132427-unary-value (function object)
  (apply$ function (list object)))

(defun q132427-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets over an arbitrary carrier.

(defun q132427-set-subset-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term carrier '(x))
      (q132427-static-apply-term left '(x))))
    (q132427-static-apply-term right '(x)))))

(defun q132427-set-subset-p
    (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q132427-universal-p
    (q132427-set-subset-function carrier left right)
    '(x))))

(defun q132427-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q132427-set-subset-p carrier set carrier)))

(defun q132427-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-static-apply-term carrier '(x))
    (q132427-iff-term
     (q132427-static-apply-term left '(x))
     (q132427-static-apply-term right '(x))))))

(defun q132427-set-equiv-p
    (carrier left right)
  (and
   (q132427-valid-set-p carrier left)
   (q132427-valid-set-p carrier right)
   (q132427-universal-p
    (q132427-set-equiv-function carrier left right)
    '(x))))

(defun q132427-empty-set ()
  (list 'lambda '(x) (q132427-quoted nil)))

(defun q132427-complement-set (carrier set)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term carrier '(x))
     (q132427-not-term
      (q132427-static-apply-term set '(x)))))))

(defun q132427-intersection-set (left right)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term left '(x))
     (q132427-static-apply-term right '(x))))))

(defun q132427-symmetric-difference-set
    (carrier left right)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term carrier '(x))
     (q132427-or-terms
      (list
       (q132427-and-terms
        (list
         (q132427-static-apply-term left '(x))
         (q132427-not-term
          (q132427-static-apply-term right '(x)))))
       (q132427-and-terms
        (list
         (q132427-static-apply-term right '(x))
         (q132427-not-term
          (q132427-static-apply-term left '(x)))))))))))

(defun q132427-set-nonempty-function
    (carrier set)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term carrier '(x))
     (q132427-static-apply-term set '(x))))))

(defun q132427-set-nonempty-p
    (carrier set)
  (and
   (q132427-valid-set-p carrier set)
   (q132427-exists-p
    (q132427-set-nonempty-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q132427-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add
          (q132427-static-apply-term add '(x y)))
         (yz-add
          (q132427-static-apply-term add '(y z)))
         (xy-mul
          (q132427-static-apply-term multiply '(x y)))
         (yz-mul
          (q132427-static-apply-term multiply '(y z)))
         (neg-x
          (q132427-static-apply-term negate '(x)))
         (inv-x
          (q132427-static-apply-term inverse '(x))))
    (list
     'lambda
     '(x y z)
     (q132427-implies-term
      (q132427-and-terms
       (list
        (q132427-static-apply-term carrier '(x))
        (q132427-static-apply-term carrier '(y))
        (q132427-static-apply-term carrier '(z))))
      (q132427-and-terms
       (list
        (q132427-static-apply-term carrier (list xy-add))
        (q132427-static-apply-term carrier (list xy-mul))
        (q132427-static-apply-term carrier (list neg-x))
        (q132427-static-apply-term carrier (list inv-x))
        (list
         'equal
         (q132427-static-apply-term add (list xy-add 'z))
         (q132427-static-apply-term add (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q132427-static-apply-term add '(y x)))
        (list
         'equal
         (q132427-static-apply-term
          add
          (list 'x (q132427-quoted zero)))
         'x)
        (list
         'equal
         (q132427-static-apply-term add (list 'x neg-x))
         (q132427-quoted zero))
        (list
         'equal
         (q132427-static-apply-term multiply (list xy-mul 'z))
         (q132427-static-apply-term multiply (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (q132427-static-apply-term multiply '(y x)))
        (list
         'equal
         (q132427-static-apply-term
          multiply
          (list 'x (q132427-quoted one)))
         'x)
        (q132427-implies-term
         (list 'equal 'x (q132427-quoted zero))
         (list 'equal inv-x (q132427-quoted zero)))
        (q132427-implies-term
         (q132427-not-term
          (list 'equal 'x (q132427-quoted zero)))
         (list
          'equal
          (q132427-static-apply-term
           multiply
           (list 'x inv-x))
          (q132427-quoted one)))
        (list
         'equal
         (q132427-static-apply-term multiply (list 'x yz-add))
         (q132427-static-apply-term
          add
          (list
           (q132427-static-apply-term multiply '(x y))
           (q132427-static-apply-term multiply '(x z)))))))))))

(defun q132427-order-laws-function
    (carrier zero add multiply less)
  (let ((xy
         (q132427-static-apply-term less '(x y)))
        (yx
         (q132427-static-apply-term less '(y x)))
        (yz
         (q132427-static-apply-term less '(y z))))
    (list
     'lambda
     '(x y z)
     (q132427-implies-term
      (q132427-and-terms
       (list
        (q132427-static-apply-term carrier '(x))
        (q132427-static-apply-term carrier '(y))
        (q132427-static-apply-term carrier '(z))))
      (q132427-and-terms
       (list
        (q132427-not-term
         (q132427-static-apply-term less '(x x)))
        (q132427-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q132427-implies-term
         (q132427-and-terms (list xy yz))
         (q132427-static-apply-term less '(x z)))
        (q132427-implies-term
         xy
         (q132427-static-apply-term
          less
          (list
           (q132427-static-apply-term add '(x z))
           (q132427-static-apply-term add '(y z)))))
        (q132427-implies-term
         (q132427-and-terms
          (list
           (q132427-static-apply-term
            less
            (list (q132427-quoted zero) 'x))
           (q132427-static-apply-term
            less
            (list (q132427-quoted zero) 'y))))
         (q132427-static-apply-term
          less
          (list
           (q132427-quoted zero)
           (q132427-static-apply-term multiply '(x y)))))))))))

(defun q132427-upper-bound-function
    (carrier less set upper)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term carrier '(x))
      (q132427-static-apply-term set '(x))))
    (q132427-not-term
     (q132427-static-apply-term
      less
      (list (q132427-quoted upper) 'x))))))

(defun q132427-upper-bound-p
    (carrier less set upper)
  (and
   (q132427-member-p carrier upper)
   (q132427-valid-set-p carrier set)
   (q132427-universal-p
    (q132427-upper-bound-function
     carrier less set upper)
    '(x))))

(defun q132427-bounded-above-function
    (carrier less set)
  (list
   'lambda
   '(upper)
   (list
    'q132427-upper-bound-p
    (q132427-quoted carrier)
    (q132427-quoted less)
    (q132427-quoted set)
    'upper)))

(defun q132427-bounded-above-p
    (carrier less set)
  (q132427-exists-p
   (q132427-bounded-above-function carrier less set)
   '(upper)))

(defun q132427-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda
   '(upper)
   (q132427-implies-term
    (list
     'q132427-upper-bound-p
     (q132427-quoted carrier)
     (q132427-quoted less)
     (q132427-quoted set)
     'upper)
    (q132427-not-term
     (q132427-static-apply-term
      less
      (list 'upper (q132427-quoted supremum)))))))

(defun q132427-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q132427-upper-bound-p carrier less set supremum)
   (q132427-universal-p
    (q132427-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q132427-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-valid-set-p
       (q132427-quoted carrier)
       'set)
      (list
       'q132427-set-nonempty-p
       (q132427-quoted carrier)
       'set)
      (list
       'q132427-bounded-above-p
       (q132427-quoted carrier)
       (q132427-quoted less)
       'set)))
    (list
     'q132427-least-upper-bound-p
     (q132427-quoted carrier)
     (q132427-quoted less)
     'set
     (q132427-static-apply-term
      supremum-operation
      '(set))))))

(defun q132427-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q132427-member-p carrier zero)
   (q132427-member-p carrier one)
   (not (equal zero one))
   (q132427-member-p
    carrier
    (q132427-unary-value inverse zero))
   (q132427-universal-p
    (q132427-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q132427-universal-p
    (q132427-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q132427-member-p
    carrier
    (q132427-unary-value supremum
                           (q132427-empty-set)))
   (q132427-universal-p
    (q132427-completeness-function
     carrier less supremum)
    '(set))
   (q132427-binary-value less zero one)))

(defun q132427-scalar-nonnegative-p
    (less zero value)
  (not (q132427-binary-value less value zero)))

(defun q132427-scalar-positive-p
    (carrier less zero value)
  (and
   (q132427-member-p carrier value)
   (q132427-binary-value less zero value)))

(defun q132427-scalar-absolute-value
    (less zero negate value)
  (if (q132427-binary-value less value zero)
      (q132427-unary-value negate value)
    value))

(defun q132427-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q132427-binary-value
     add
     one
     (q132427-field-natural
      (- n 1) zero one add))))

(defun q132427-field-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q132427-binary-value
     multiply
     base
     (q132427-field-power
      base (- exponent 1) one multiply))))

;; Finite-dimensional normed vector spaces over the represented real field.

(defun q132427-vector-laws-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate smul)
  (let* ((xy
          (q132427-static-apply-term add '(x y)))
         (yz
          (q132427-static-apply-term add '(y z)))
         (neg-x
          (q132427-static-apply-term negate '(x)))
         (a-x
          (q132427-static-apply-term smul '(a x))))
    (list
     'lambda
     '(a b x y z)
     (q132427-implies-term
      (q132427-and-terms
       (list
        (q132427-static-apply-term scalar-carrier '(a))
        (q132427-static-apply-term scalar-carrier '(b))
        (q132427-static-apply-term carrier '(x))
        (q132427-static-apply-term carrier '(y))
        (q132427-static-apply-term carrier '(z))))
      (q132427-and-terms
       (list
        (q132427-static-apply-term carrier (list xy))
        (q132427-static-apply-term carrier (list neg-x))
        (q132427-static-apply-term carrier (list a-x))
        (list
         'equal
         (q132427-static-apply-term add (list xy 'z))
         (q132427-static-apply-term add (list 'x yz)))
        (list
         'equal
         xy
         (q132427-static-apply-term add '(y x)))
        (list
         'equal
         (q132427-static-apply-term
          add
          (list 'x (q132427-quoted zero)))
         'x)
        (list
         'equal
         (q132427-static-apply-term add (list 'x neg-x))
         (q132427-quoted zero))
        (list
         'equal
         (q132427-static-apply-term
          smul
          (list (q132427-quoted scalar-one) 'x))
         'x)
        (list
         'equal
         (q132427-static-apply-term
          smul
          (list
           (q132427-static-apply-term
            scalar-multiply
            '(a b))
           'x))
         (q132427-static-apply-term
          smul
          (list
           'a
           (q132427-static-apply-term smul '(b x)))))
        (list
         'equal
         (q132427-static-apply-term
          smul
          (list
           (q132427-static-apply-term scalar-add '(a b))
           'x))
         (q132427-static-apply-term
          add
          (list
           a-x
           (q132427-static-apply-term smul '(b x)))))
        (list
         'equal
         (q132427-static-apply-term smul (list 'a xy))
         (q132427-static-apply-term
          add
          (list
           a-x
           (q132427-static-apply-term smul '(a y)))))
        (list
         'equal
         (q132427-static-apply-term
          smul
          (list (q132427-quoted scalar-zero) 'x))
         (q132427-quoted zero))))))))

(defun q132427-norm-laws-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-negate
     scalar-less carrier zero add negate smul norm)
  (let* ((norm-x
          (q132427-static-apply-term norm '(x)))
         (norm-y
          (q132427-static-apply-term norm '(y)))
         (norm-a-x
          (q132427-static-apply-term
           norm
           (list
            (q132427-static-apply-term smul '(a x)))))
         (abs-a
          (list
           'q132427-scalar-absolute-value
           (q132427-quoted scalar-less)
           (q132427-quoted scalar-zero)
           (q132427-quoted scalar-negate)
           'a)))
    (list
     'lambda
     '(a x y)
     (q132427-implies-term
      (q132427-and-terms
       (list
        (q132427-static-apply-term scalar-carrier '(a))
        (q132427-static-apply-term carrier '(x))
        (q132427-static-apply-term carrier '(y))))
      (q132427-and-terms
       (list
        (q132427-static-apply-term scalar-carrier (list norm-x))
        (q132427-not-term
         (q132427-static-apply-term
          scalar-less
          (list norm-x (q132427-quoted scalar-zero))))
        (q132427-iff-term
         (list 'equal norm-x (q132427-quoted scalar-zero))
         (list 'equal 'x (q132427-quoted zero)))
        (list
         'equal
         (q132427-static-apply-term
          norm
          (list
           (q132427-static-apply-term negate '(x))))
         norm-x)
        (list
         'equal
         norm-a-x
         (q132427-static-apply-term
          scalar-multiply
          (list abs-a norm-x)))
        (q132427-not-term
         (q132427-static-apply-term
          scalar-less
          (list
           (q132427-static-apply-term
            scalar-add
            (list norm-x norm-y))
           (q132427-static-apply-term
            norm
            (list
             (q132427-static-apply-term add '(x y)))))))))))))

(defun q132427-normed-vector-space-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-less
     carrier zero add negate smul norm)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp negate)
   (tamep-functionp smul)
   (tamep-functionp norm)
   (q132427-member-p carrier zero)
   (q132427-universal-p
    (q132427-vector-laws-function
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate smul)
    '(a b x y z))
   (q132427-universal-p
    (q132427-norm-laws-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-negate
     scalar-less carrier zero add negate smul norm)
    '(a x y))))

(defun q132427-coefficient-list-p
    (coefficients basis scalar-carrier)
  (if (consp basis)
      (and
       (consp coefficients)
       (q132427-member-p scalar-carrier (car coefficients))
       (q132427-coefficient-list-p
        (cdr coefficients)
        (cdr basis)
        scalar-carrier))
    (equal coefficients nil)))

(defun q132427-basis-elements-p
    (basis carrier)
  (if (consp basis)
      (and
       (q132427-member-p carrier (car basis))
       (q132427-basis-elements-p
        (cdr basis) carrier))
    (equal basis nil)))

(defun q132427-linear-combination
    (coefficients basis vector-zero vector-add smul)
  (if (consp basis)
      (q132427-binary-value
       vector-add
       (q132427-binary-value
        smul
        (car coefficients)
        (car basis))
       (q132427-linear-combination
        (cdr coefficients)
        (cdr basis)
        vector-zero vector-add smul))
    vector-zero))

(defun q132427-all-zero-coefficients-p
    (coefficients scalar-zero)
  (if (consp coefficients)
      (and
       (equal (car coefficients) scalar-zero)
       (q132427-all-zero-coefficients-p
        (cdr coefficients) scalar-zero))
    (equal coefficients nil)))

(defun q132427-basis-independence-function
    (basis scalar-carrier scalar-zero
           vector-zero vector-add smul)
  (list
   'lambda
   '(coefficients)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-coefficient-list-p
       'coefficients
       (q132427-quoted basis)
       (q132427-quoted scalar-carrier))
      (list
       'equal
       (list
        'q132427-linear-combination
        'coefficients
        (q132427-quoted basis)
        (q132427-quoted vector-zero)
        (q132427-quoted vector-add)
        (q132427-quoted smul))
       (q132427-quoted vector-zero))))
    (list
     'q132427-all-zero-coefficients-p
     'coefficients
     (q132427-quoted scalar-zero)))))

(defun q132427-basis-spanning-function
    (basis coordinates scalar-carrier carrier
           vector-zero vector-add smul)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-static-apply-term carrier '(x))
    (q132427-and-terms
     (list
      (list
       'q132427-coefficient-list-p
       (q132427-static-apply-term coordinates '(x))
       (q132427-quoted basis)
       (q132427-quoted scalar-carrier))
      (list
       'equal
       (list
        'q132427-linear-combination
        (q132427-static-apply-term coordinates '(x))
        (q132427-quoted basis)
        (q132427-quoted vector-zero)
        (q132427-quoted vector-add)
        (q132427-quoted smul))
       'x))))))

(defun q132427-finite-basis-p
    (basis coordinates scalar-carrier scalar-zero
           carrier vector-zero vector-add smul)
  (and
   (true-listp basis)
   (tamep-functionp coordinates)
   (q132427-basis-elements-p basis carrier)
   (q132427-universal-p
    (q132427-basis-independence-function
     basis scalar-carrier scalar-zero
     vector-zero vector-add smul)
    '(coefficients))
   (q132427-universal-p
    (q132427-basis-spanning-function
     basis coordinates scalar-carrier carrier
     vector-zero vector-add smul)
    '(x))))

;; Norm topology, convergence, and compactness.

(defun q132427-vector-difference
    (add negate left right)
  (q132427-binary-value
   add left (q132427-unary-value negate right)))

(defun q132427-distance-less-p
    (scalar-less vector-add vector-negate norm
                 left right epsilon)
  (q132427-binary-value
   scalar-less
   (q132427-unary-value
    norm
    (q132427-vector-difference
     vector-add vector-negate left right))
   epsilon))

(defun q132427-ball-subset-function
    (carrier vector-add vector-negate norm scalar-less
             center epsilon set)
  (list
   'lambda
   '(y)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term carrier '(y))
      (list
       'q132427-distance-less-p
       (q132427-quoted scalar-less)
       (q132427-quoted vector-add)
       (q132427-quoted vector-negate)
       (q132427-quoted norm)
       (q132427-quoted center)
       'y
       (q132427-quoted epsilon))))
    (q132427-static-apply-term set '(y)))))

(defun q132427-ball-subset-p
    (carrier vector-add vector-negate norm scalar-less
             center epsilon set)
  (q132427-universal-p
   (q132427-ball-subset-function
    carrier vector-add vector-negate norm scalar-less
    center epsilon set)
   '(y)))

(defun q132427-open-radius-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set x)
  (list
   'lambda
   '(epsilon)
   (q132427-and-terms
    (list
     (list
      'q132427-scalar-positive-p
      (q132427-quoted scalar-carrier)
      (q132427-quoted scalar-less)
      (q132427-quoted scalar-zero)
      'epsilon)
     (list
      'q132427-ball-subset-p
      (q132427-quoted carrier)
      (q132427-quoted vector-add)
      (q132427-quoted vector-negate)
      (q132427-quoted norm)
      (q132427-quoted scalar-less)
      (q132427-quoted x)
      'epsilon
      (q132427-quoted set))))))

(defun q132427-open-radius-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set x)
  (q132427-exists-p
   (q132427-open-radius-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm set x)
   '(epsilon)))

(defun q132427-open-set-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term carrier '(x))
      (q132427-static-apply-term set '(x))))
    (list
     'q132427-open-radius-exists-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted carrier)
     (q132427-quoted vector-add)
     (q132427-quoted vector-negate)
     (q132427-quoted norm)
     (q132427-quoted set)
     'x))))

(defun q132427-open-set-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (and
   (q132427-valid-set-p carrier set)
   (q132427-universal-p
    (q132427-open-set-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    '(x))))

(defun q132427-sequence-in-set-function
    (carrier set sequence)
  (list
   'lambda
   '(n)
   (q132427-implies-term
    (list 'natp 'n)
    (q132427-and-terms
     (list
      (q132427-static-apply-term
       carrier
       (list
        (q132427-static-apply-term sequence '(n))))
      (q132427-static-apply-term
       set
       (list
        (q132427-static-apply-term sequence '(n)))))))))

(defun q132427-sequence-in-set-p
    (carrier set sequence)
  (and
   (tamep-functionp sequence)
   (q132427-universal-p
    (q132427-sequence-in-set-function
     carrier set sequence)
    '(n))))

(defun q132427-convergence-tail-function
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon start)
  (list
   'lambda
   '(n)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q132427-quoted start) 'n)))
    (list
     'q132427-distance-less-p
     (q132427-quoted scalar-less)
     (q132427-quoted vector-add)
     (q132427-quoted vector-negate)
     (q132427-quoted norm)
     (q132427-static-apply-term sequence '(n))
     (q132427-quoted limit)
     (q132427-quoted epsilon)))))

(defun q132427-convergence-tail-p
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon start)
  (and
   (natp start)
   (q132427-universal-p
    (q132427-convergence-tail-function
     vector-add vector-negate norm scalar-less
     sequence limit epsilon start)
    '(n))))

(defun q132427-convergence-start-function
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon)
  (list
   'lambda
   '(start)
   (list
    'q132427-convergence-tail-p
    (q132427-quoted vector-add)
    (q132427-quoted vector-negate)
    (q132427-quoted norm)
    (q132427-quoted scalar-less)
    (q132427-quoted sequence)
    (q132427-quoted limit)
    (q132427-quoted epsilon)
    'start)))

(defun q132427-convergence-start-exists-p
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon)
  (q132427-exists-p
   (q132427-convergence-start-function
    vector-add vector-negate norm scalar-less
    sequence limit epsilon)
   '(start)))

(defun q132427-convergence-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     vector-add vector-negate norm sequence limit)
  (list
   'lambda
   '(epsilon)
   (q132427-implies-term
    (list
     'q132427-scalar-positive-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-less)
     (q132427-quoted scalar-zero)
     'epsilon)
    (list
     'q132427-convergence-start-exists-p
     (q132427-quoted vector-add)
     (q132427-quoted vector-negate)
     (q132427-quoted norm)
     (q132427-quoted scalar-less)
     (q132427-quoted sequence)
     (q132427-quoted limit)
     'epsilon))))

(defun q132427-converges-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm sequence limit)
  (and
   (tamep-functionp sequence)
   (q132427-member-p carrier limit)
   (q132427-universal-p
    (q132427-convergence-epsilon-function
     scalar-carrier scalar-zero scalar-less
     vector-add vector-negate norm sequence limit)
    '(epsilon))))

(defun q132427-subsequence-laws-function
    (subsequence)
  (list
   'lambda
   '(m n)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)))
    (q132427-and-terms
     (list
      (list
       'natp
       (q132427-static-apply-term subsequence '(m)))
      (q132427-implies-term
       (list '< 'm 'n)
       (list
        '<
        (q132427-static-apply-term subsequence '(m))
        (q132427-static-apply-term subsequence '(n)))))))))

(defun q132427-subsequence-p (subsequence)
  (and
   (tamep-functionp subsequence)
   (q132427-universal-p
    (q132427-subsequence-laws-function subsequence)
    '(m n))))

(defun q132427-compose-sequence
    (sequence subsequence)
  (list
   'lambda
   '(n)
   (q132427-static-apply-term
    sequence
    (list
     (q132427-static-apply-term subsequence '(n))))))

(defun q132427-compact-witness-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     set sequence subsequence limit)
  (and
   (q132427-subsequence-p subsequence)
   (q132427-member-p carrier limit)
   (q132427-member-p set limit)
   (q132427-converges-p
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm
    (q132427-compose-sequence sequence subsequence)
    limit)))

(defun q132427-compact-witness-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set sequence)
  (list
   'lambda
   '(subsequence limit)
   (list
    'q132427-compact-witness-p
    (q132427-quoted scalar-carrier)
    (q132427-quoted scalar-zero)
    (q132427-quoted scalar-less)
    (q132427-quoted carrier)
    (q132427-quoted vector-add)
    (q132427-quoted vector-negate)
    (q132427-quoted norm)
    (q132427-quoted set)
    (q132427-quoted sequence)
    'subsequence
    'limit)))

(defun q132427-compact-witness-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set sequence)
  (q132427-exists-p
   (q132427-compact-witness-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm set sequence)
   '(subsequence limit)))

(defun q132427-compact-set-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (list
   'lambda
   '(sequence)
   (q132427-implies-term
    (list
     'q132427-sequence-in-set-p
     (q132427-quoted carrier)
     (q132427-quoted set)
     'sequence)
    (list
     'q132427-compact-witness-exists-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted carrier)
     (q132427-quoted vector-add)
     (q132427-quoted vector-negate)
     (q132427-quoted norm)
     (q132427-quoted set)
     'sequence))))

(defun q132427-compact-set-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (and
   (q132427-valid-set-p carrier set)
   (q132427-universal-p
    (q132427-compact-set-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    '(sequence))))

;; The Borel sigma-algebra generated by the norm topology.

(defun q132427-family-extensional-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-valid-set-p
       (q132427-quoted carrier)
       'left)
      (list
       'q132427-valid-set-p
       (q132427-quoted carrier)
       'right)
      (list
       'q132427-set-equiv-p
       (q132427-quoted carrier)
       'left
       'right)))
    (q132427-iff-term
     (q132427-static-apply-term family '(left))
     (q132427-static-apply-term family '(right))))))

(defun q132427-family-members-valid-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (q132427-static-apply-term family '(set))
    (list
     'q132427-valid-set-p
     (q132427-quoted carrier)
     'set))))

(defun q132427-family-of-sets-p
    (carrier family)
  (and
   (tamep-functionp family)
   (q132427-universal-p
    (q132427-family-extensional-function carrier family)
    '(left right))
   (q132427-universal-p
    (q132427-family-members-valid-function carrier family)
    '(set))))

(defun q132427-sequence-union-member-function
    (sequence x)
  (list
   'lambda
   '(n)
   (q132427-and-terms
    (list
     (list 'natp 'n)
     (q132427-apply-term
      (q132427-static-apply-term sequence '(n))
      (list (q132427-quoted x)))))))

(defun q132427-sequence-union-member-p
    (sequence x)
  (q132427-exists-p
   (q132427-sequence-union-member-function sequence x)
   '(n)))

(defun q132427-sequence-union-set
    (carrier sequence)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term carrier '(x))
     (list
      'q132427-sequence-union-member-p
      (q132427-quoted sequence)
      'x)))))

(defun q132427-sequence-of-sets-function
    (carrier sequence)
  (list
   'lambda
   '(n)
   (q132427-implies-term
    (list 'natp 'n)
    (list
     'q132427-valid-set-p
     (q132427-quoted carrier)
     (q132427-static-apply-term sequence '(n))))))

(defun q132427-sequence-of-sets-p
    (carrier sequence)
  (and
   (tamep-functionp sequence)
   (q132427-universal-p
    (q132427-sequence-of-sets-function
     carrier sequence)
    '(n))))

(defun q132427-sequence-members-family-function
    (family sequence)
  (list
   'lambda
   '(n)
   (q132427-implies-term
    (list 'natp 'n)
    (q132427-static-apply-term
     family
     (list
      (q132427-static-apply-term sequence '(n)))))))

(defun q132427-sequence-members-family-p
    (carrier family sequence)
  (and
   (q132427-sequence-of-sets-p carrier sequence)
   (q132427-universal-p
    (q132427-sequence-members-family-function
     family sequence)
    '(n))))

(defun q132427-sigma-complement-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (q132427-static-apply-term family '(set))
    (q132427-static-apply-term
     family
     (list
      (list
       'q132427-complement-set
       (q132427-quoted carrier)
       'set))))))

(defun q132427-sigma-union-function
    (carrier family)
  (list
   'lambda
   '(sequence)
   (q132427-implies-term
    (list
     'q132427-sequence-members-family-p
     (q132427-quoted carrier)
     (q132427-quoted family)
     'sequence)
    (q132427-static-apply-term
     family
     (list
      (list
       'q132427-sequence-union-set
       (q132427-quoted carrier)
       'sequence))))))

(defun q132427-sigma-algebra-p
    (carrier family)
  (and
   (q132427-family-of-sets-p carrier family)
   (q132427-member-p family (q132427-empty-set))
   (q132427-universal-p
    (q132427-sigma-complement-function carrier family)
    '(set))
   (q132427-universal-p
    (q132427-sigma-union-function carrier family)
    '(sequence))))

(defun q132427-contains-open-sets-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm family)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (list
     'q132427-open-set-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted carrier)
     (q132427-quoted vector-add)
     (q132427-quoted vector-negate)
     (q132427-quoted norm)
     'set)
    (q132427-static-apply-term family '(set)))))

(defun q132427-contains-open-sets-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm family)
  (q132427-universal-p
   (q132427-contains-open-sets-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm family)
   '(set)))

(defun q132427-family-subset-function
    (left right)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (q132427-static-apply-term left '(set))
    (q132427-static-apply-term right '(set)))))

(defun q132427-family-subset-p
    (left right)
  (q132427-universal-p
   (q132427-family-subset-function left right)
   '(set)))

(defun q132427-borel-minimality-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
  (list
   'lambda
   '(candidate)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-sigma-algebra-p
       (q132427-quoted carrier)
       'candidate)
      (list
       'q132427-contains-open-sets-p
       (q132427-quoted scalar-carrier)
       (q132427-quoted scalar-zero)
       (q132427-quoted scalar-less)
       (q132427-quoted carrier)
       (q132427-quoted vector-add)
       (q132427-quoted vector-negate)
       (q132427-quoted norm)
       'candidate)))
    (list
     'q132427-family-subset-p
     (q132427-quoted measurable)
     'candidate))))

(defun q132427-borel-space-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
  (and
   (q132427-sigma-algebra-p carrier measurable)
   (q132427-contains-open-sets-p
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm measurable)
   (q132427-universal-p
    (q132427-borel-minimality-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measurable)
    '(candidate))))

;; Extended nonnegative real values built from the represented real field.

(defun q132427-ennreal-p
    (value scalar-carrier scalar-zero scalar-less)
  (or
   (equal value :q132427-top)
   (and
    (consp value)
    (equal (car value) :q132427-finite)
    (q132427-member-p scalar-carrier (cdr value))
    (q132427-scalar-nonnegative-p
     scalar-less scalar-zero (cdr value)))))

(defun q132427-ennreal-finite (value)
  (cons :q132427-finite value))

(defun q132427-ennreal-zero (scalar-zero)
  (q132427-ennreal-finite scalar-zero))

(defun q132427-ennreal-less-p
    (left right scalar-less)
  (cond
   ((equal left :q132427-top) nil)
   ((equal right :q132427-top) t)
   (t
    (q132427-binary-value
     scalar-less (cdr left) (cdr right)))))

(defun q132427-ennreal-less-equal-p
    (left right scalar-less)
  (not
   (q132427-ennreal-less-p
    right left scalar-less)))

(defun q132427-ennreal-add
    (left right scalar-add)
  (if (or (equal left :q132427-top)
          (equal right :q132427-top))
      :q132427-top
    (q132427-ennreal-finite
     (q132427-binary-value
      scalar-add (cdr left) (cdr right)))))

(defun q132427-ennreal-multiply
    (left right scalar-zero scalar-multiply)
  (cond
   ((or (equal left
               (q132427-ennreal-zero scalar-zero))
        (equal right
               (q132427-ennreal-zero scalar-zero)))
    (q132427-ennreal-zero scalar-zero))
   ((or (equal left :q132427-top)
        (equal right :q132427-top))
    :q132427-top)
   (t
    (q132427-ennreal-finite
     (q132427-binary-value
      scalar-multiply (cdr left) (cdr right))))))

(defun q132427-ennreal-two-power
    (dimension scalar-zero scalar-one scalar-add scalar-multiply)
  (q132427-ennreal-finite
   (q132427-field-power
    (q132427-field-natural
     2 scalar-zero scalar-one scalar-add)
    dimension scalar-one scalar-multiply)))

;; Countably additive Borel measures and their values on arbitrary sets.

(defun q132427-measure-extensional-function
    (carrier measure)
  (list
   'lambda
   '(left right)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-set-equiv-p
       (q132427-quoted carrier)
       'left
       'right)))
    (list
     'equal
     (q132427-static-apply-term measure '(left))
     (q132427-static-apply-term measure '(right))))))

(defun q132427-measure-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measure)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (list
     'q132427-valid-set-p
     (q132427-quoted carrier)
     'set)
    (list
     'q132427-ennreal-p
     (q132427-static-apply-term measure '(set))
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)))))

(defun q132427-finite-measure-sum
    (measure sequence count scalar-zero scalar-add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q132427-ennreal-zero scalar-zero)
    (q132427-ennreal-add
     (q132427-finite-measure-sum
      measure sequence (- count 1)
      scalar-zero scalar-add)
     (q132427-unary-value
      measure
      (q132427-unary-value
       sequence (- count 1)))
     scalar-add)))

(defun q132427-sum-upper-bound-function
    (measure sequence total scalar-zero scalar-add scalar-less)
  (list
   'lambda
   '(count)
   (q132427-implies-term
    (list 'natp 'count)
    (list
     'q132427-ennreal-less-equal-p
     (list
      'q132427-finite-measure-sum
      (q132427-quoted measure)
      (q132427-quoted sequence)
      'count
      (q132427-quoted scalar-zero)
      (q132427-quoted scalar-add))
     (q132427-quoted total)
     (q132427-quoted scalar-less)))))

(defun q132427-sum-upper-bound-p
    (measure sequence total scalar-zero scalar-add scalar-less)
  (q132427-universal-p
   (q132427-sum-upper-bound-function
    measure sequence total scalar-zero scalar-add scalar-less)
   '(count)))

(defun q132427-sum-least-function
    (measure sequence total
             scalar-carrier scalar-zero scalar-add scalar-less)
  (list
   'lambda
   '(bound)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-ennreal-p
       'bound
       (q132427-quoted scalar-carrier)
       (q132427-quoted scalar-zero)
       (q132427-quoted scalar-less))
      (list
       'q132427-sum-upper-bound-p
       (q132427-quoted measure)
       (q132427-quoted sequence)
       'bound
       (q132427-quoted scalar-zero)
       (q132427-quoted scalar-add)
       (q132427-quoted scalar-less))))
    (list
     'q132427-ennreal-less-equal-p
     (q132427-quoted total)
     'bound
     (q132427-quoted scalar-less)))))

(defun q132427-countable-sum-p
    (measure sequence total
             scalar-carrier scalar-zero scalar-add scalar-less)
  (and
   (q132427-ennreal-p
    total scalar-carrier scalar-zero scalar-less)
   (q132427-sum-upper-bound-p
    measure sequence total
    scalar-zero scalar-add scalar-less)
   (q132427-universal-p
    (q132427-sum-least-function
     measure sequence total
     scalar-carrier scalar-zero scalar-add scalar-less)
    '(bound))))

(defun q132427-disjoint-sets-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-static-apply-term carrier '(x))
    (q132427-not-term
     (q132427-and-terms
      (list
       (q132427-static-apply-term left '(x))
       (q132427-static-apply-term right '(x))))))))

(defun q132427-disjoint-sets-p
    (carrier left right)
  (q132427-universal-p
   (q132427-disjoint-sets-function carrier left right)
   '(x)))

(defun q132427-pairwise-disjoint-sequence-function
    (carrier sequence)
  (list
   'lambda
   '(m n)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)
      (q132427-not-term (list 'equal 'm 'n))))
    (list
     'q132427-disjoint-sets-p
     (q132427-quoted carrier)
     (q132427-static-apply-term sequence '(m))
     (q132427-static-apply-term sequence '(n))))))

(defun q132427-pairwise-disjoint-sequence-p
    (carrier sequence)
  (q132427-universal-p
   (q132427-pairwise-disjoint-sequence-function
    carrier sequence)
   '(m n)))

(defun q132427-countable-additivity-function
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (list
   'lambda
   '(sequence)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-sequence-members-family-p
       (q132427-quoted carrier)
       (q132427-quoted measurable)
       'sequence)
      (list
       'q132427-pairwise-disjoint-sequence-p
       (q132427-quoted carrier)
       'sequence)))
    (list
     'q132427-countable-sum-p
     (q132427-quoted measure)
     'sequence
     (q132427-static-apply-term
      measure
      (list
       (list
        'q132427-sequence-union-set
        (q132427-quoted carrier)
        'sequence)))
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-add)
     (q132427-quoted scalar-less)))))

(defun q132427-measurable-superset-lower-bound-function
    (carrier measurable measure set lower scalar-less)
  (list
   'lambda
   '(superset)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term measurable '(superset))
      (list
       'q132427-set-subset-p
       (q132427-quoted carrier)
       (q132427-quoted set)
       'superset)))
    (list
     'q132427-ennreal-less-equal-p
     (q132427-quoted lower)
     (q132427-static-apply-term measure '(superset))
     (q132427-quoted scalar-less)))))

(defun q132427-measurable-superset-lower-bound-p
    (carrier measurable measure set lower scalar-less)
  (q132427-universal-p
   (q132427-measurable-superset-lower-bound-function
    carrier measurable measure set lower scalar-less)
   '(superset)))

(defun q132427-outer-value-lower-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (list
   'lambda
   '(lower)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-ennreal-p
       'lower
       (q132427-quoted scalar-carrier)
       (q132427-quoted scalar-zero)
       (q132427-quoted scalar-less))
      (list
       'q132427-measurable-superset-lower-bound-p
       (q132427-quoted carrier)
       (q132427-quoted measurable)
       (q132427-quoted measure)
       (q132427-quoted set)
       'lower
       (q132427-quoted scalar-less))))
    (list
     'q132427-ennreal-less-equal-p
     'lower
     (q132427-static-apply-term measure (list (q132427-quoted set)))
     (q132427-quoted scalar-less)))))

(defun q132427-outer-value-p
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
  (and
   (q132427-valid-set-p carrier set)
   (q132427-measurable-superset-lower-bound-p
    carrier measurable measure set
    (q132427-unary-value measure set)
    scalar-less)
   (q132427-universal-p
    (q132427-outer-value-lower-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure set)
    '(lower))))

(defun q132427-outer-values-function
    (scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (list
     'q132427-valid-set-p
     (q132427-quoted carrier)
     'set)
    (list
     'q132427-outer-value-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted carrier)
     (q132427-quoted measurable)
     (q132427-quoted measure)
     'set))))

(defun q132427-measure-space-p
    (scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
  (and
   (tamep-functionp measure)
   (q132427-universal-p
    (q132427-measure-extensional-function
     carrier measure)
    '(left right))
   (q132427-universal-p
    (q132427-measure-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measure)
    '(set))
   (equal
    (q132427-unary-value measure (q132427-empty-set))
    (q132427-ennreal-zero scalar-zero))
   (q132427-universal-p
    (q132427-countable-additivity-function
     scalar-carrier scalar-zero scalar-add scalar-less
     carrier measurable measure)
    '(sequence))
   (q132427-universal-p
    (q132427-outer-values-function
     scalar-carrier scalar-zero scalar-less
     carrier measurable measure)
    '(set))))

;; Haar measure: translation invariance, compact finiteness, and positivity
;; on every nonempty open set.

(defun q132427-translate-set
    (carrier vector-add vector-negate shift set)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term carrier '(x))
     (q132427-static-apply-term
      set
      (list
       (q132427-static-apply-term
        vector-add
        (list
         (q132427-static-apply-term
          vector-negate
          (list (q132427-quoted shift)))
         'x))))))))

(defun q132427-translation-invariance-function
    (carrier vector-add vector-negate measure)
  (list
   'lambda
   '(shift set)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term carrier '(shift))
      (list
       'q132427-valid-set-p
       (q132427-quoted carrier)
       'set)))
    (list
     'equal
     (q132427-static-apply-term
      measure
      (list
       (list
        'q132427-translate-set
        (q132427-quoted carrier)
        (q132427-quoted vector-add)
        (q132427-quoted vector-negate)
        'shift
        'set)))
     (q132427-static-apply-term measure '(set))))))

(defun q132427-compact-finite-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (list
     'q132427-compact-set-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted carrier)
     (q132427-quoted vector-add)
     (q132427-quoted vector-negate)
     (q132427-quoted norm)
     'set)
    (q132427-not-term
     (list
      'equal
      (q132427-static-apply-term measure '(set))
      (q132427-quoted :q132427-top))))))

(defun q132427-open-positive-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
  (list
   'lambda
   '(set)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (list
       'q132427-open-set-p
       (q132427-quoted scalar-carrier)
       (q132427-quoted scalar-zero)
       (q132427-quoted scalar-less)
       (q132427-quoted carrier)
       (q132427-quoted vector-add)
       (q132427-quoted vector-negate)
       (q132427-quoted norm)
       'set)
      (list
       'q132427-set-nonempty-p
       (q132427-quoted carrier)
       'set)))
    (list
     'q132427-ennreal-less-p
     (list
      'q132427-ennreal-zero
      (q132427-quoted scalar-zero))
     (q132427-static-apply-term measure '(set))
     (q132427-quoted scalar-less)))))

(defun q132427-add-haar-measure-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
  (and
   (q132427-universal-p
    (q132427-translation-invariance-function
     carrier vector-add vector-negate measure)
    '(shift set))
   (q132427-universal-p
    (q132427-compact-finite-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
    '(set))
   (q132427-universal-p
    (q132427-open-positive-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm measure)
    '(set))))

;; Typed functions and continuous linear maps.

(defun q132427-scalar-less-equal-p (less left right)
  (not (q132427-binary-value less right left)))

(defun q132427-function-values-function
    (domain-carrier codomain-carrier function)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-static-apply-term domain-carrier '(x))
    (q132427-static-apply-term
     codomain-carrier
     (list
      (q132427-static-apply-term function '(x)))))))

(defun q132427-function-p
    (domain-carrier codomain-carrier function)
  (and
   (tamep-functionp function)
   (q132427-universal-p
    (q132427-function-values-function
     domain-carrier codomain-carrier function)
    '(x))))

(defun q132427-linear-map-laws-function
    (scalar-carrier domain-carrier codomain-carrier
     scalar-add domain-add codomain-add
     domain-smul codomain-smul mapping)
  (declare (ignore scalar-add))
  (list
   'lambda
   '(a x y)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term scalar-carrier '(a))
      (q132427-static-apply-term domain-carrier '(x))
      (q132427-static-apply-term domain-carrier '(y))))
    (q132427-and-terms
     (list
      (q132427-static-apply-term
       codomain-carrier
       (list (q132427-static-apply-term mapping '(x))))
      (list
       'equal
       (q132427-static-apply-term
        mapping
        (list (q132427-static-apply-term domain-add '(x y))))
       (q132427-static-apply-term
        codomain-add
        (list
         (q132427-static-apply-term mapping '(x))
         (q132427-static-apply-term mapping '(y)))))
      (list
       'equal
       (q132427-static-apply-term
        mapping
        (list (q132427-static-apply-term domain-smul '(a x))))
       (q132427-static-apply-term
        codomain-smul
        (list
         'a
         (q132427-static-apply-term mapping '(x))))))))))

(defun q132427-linear-map-p
    (scalar-carrier domain-carrier codomain-carrier
     scalar-add domain-add codomain-add
     domain-smul codomain-smul mapping)
  (and
   (tamep-functionp mapping)
   (q132427-universal-p
    (q132427-linear-map-laws-function
     scalar-carrier domain-carrier codomain-carrier
     scalar-add domain-add codomain-add
     domain-smul codomain-smul mapping)
    '(a x y))))

(defun q132427-linear-continuity-delta-function
    (domain-carrier domain-norm codomain-norm scalar-less
     mapping epsilon delta)
  (list
   'lambda
   '(x)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term domain-carrier '(x))
      (q132427-static-apply-term
       scalar-less
       (list
        (q132427-static-apply-term domain-norm '(x))
        (q132427-quoted delta)))))
    (q132427-static-apply-term
     scalar-less
     (list
      (q132427-static-apply-term
       codomain-norm
       (list (q132427-static-apply-term mapping '(x))))
      (q132427-quoted epsilon))))))

(defun q132427-linear-continuity-delta-p
    (domain-carrier domain-norm codomain-norm scalar-less
     mapping epsilon delta)
  (q132427-universal-p
   (q132427-linear-continuity-delta-function
    domain-carrier domain-norm codomain-norm scalar-less
    mapping epsilon delta)
   '(x)))

(defun q132427-linear-continuity-witness-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier domain-norm codomain-norm mapping epsilon)
  (list
   'lambda
   '(delta)
   (q132427-and-terms
    (list
     (list
      'q132427-scalar-positive-p
      (q132427-quoted scalar-carrier)
      (q132427-quoted scalar-less)
      (q132427-quoted scalar-zero)
      'delta)
     (list
      'q132427-linear-continuity-delta-p
      (q132427-quoted domain-carrier)
      (q132427-quoted domain-norm)
      (q132427-quoted codomain-norm)
      (q132427-quoted scalar-less)
      (q132427-quoted mapping)
      (q132427-quoted epsilon)
      'delta)))))

(defun q132427-linear-continuity-witness-exists-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier domain-norm codomain-norm mapping epsilon)
  (q132427-exists-p
   (q132427-linear-continuity-witness-function
    scalar-carrier scalar-zero scalar-less
    domain-carrier domain-norm codomain-norm mapping epsilon)
   '(delta)))

(defun q132427-linear-continuity-function
    (scalar-carrier scalar-zero scalar-less
     domain-carrier domain-norm codomain-norm mapping)
  (list
   'lambda
   '(epsilon)
   (q132427-implies-term
    (list
     'q132427-scalar-positive-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-less)
     (q132427-quoted scalar-zero)
     'epsilon)
    (list
     'q132427-linear-continuity-witness-exists-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted domain-carrier)
     (q132427-quoted domain-norm)
     (q132427-quoted codomain-norm)
     (q132427-quoted mapping)
     'epsilon))))

(defun q132427-continuous-linear-map-p
    (scalar-carrier scalar-zero scalar-less
     domain-carrier domain-add domain-smul domain-norm
     codomain-carrier codomain-add codomain-smul codomain-norm
     scalar-add mapping)
  (and
   (q132427-linear-map-p
    scalar-carrier domain-carrier codomain-carrier
    scalar-add domain-add codomain-add
    domain-smul codomain-smul mapping)
   (q132427-universal-p
    (q132427-linear-continuity-function
     scalar-carrier scalar-zero scalar-less
     domain-carrier domain-norm codomain-norm mapping)
    '(epsilon))))

;; Lipschitz continuity on an arbitrary set.

(defun q132427-lipschitz-on-function
    (scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set constant)
  (list
   'lambda
   '(x y)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term domain-carrier '(x))
      (q132427-static-apply-term domain-carrier '(y))
      (q132427-static-apply-term set '(x))
      (q132427-static-apply-term set '(y))))
    (q132427-not-term
     (q132427-static-apply-term
      scalar-less
      (list
       (q132427-static-apply-term
        scalar-multiply
        (list
         (q132427-quoted constant)
         (q132427-static-apply-term
          domain-norm
          (list
           (list
            'q132427-vector-difference
            (q132427-quoted domain-add)
            (q132427-quoted domain-negate)
            'x
            'y)))))
       (q132427-static-apply-term
        codomain-norm
        (list
         (list
          'q132427-vector-difference
          (q132427-quoted codomain-add)
          (q132427-quoted codomain-negate)
          (q132427-static-apply-term function '(x))
          (q132427-static-apply-term function '(y)))))))))))

(defun q132427-lipschitz-on-with-p
    (scalar-carrier scalar-zero scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set constant)
  (and
   (q132427-member-p scalar-carrier constant)
   (q132427-scalar-nonnegative-p scalar-less scalar-zero constant)
   (q132427-universal-p
    (q132427-lipschitz-on-function
     scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set constant)
    '(x y))))

;; Frechet differentiability within a set.

(defun q132427-derivative-remainder
    (domain-add domain-negate
     codomain-add codomain-negate
     function linear-map x y)
  (let* ((increment
          (q132427-vector-difference
           domain-add domain-negate y x))
         (function-increment
          (q132427-vector-difference
           codomain-add codomain-negate
           (q132427-unary-value function y)
           (q132427-unary-value function x))))
    (q132427-vector-difference
     codomain-add codomain-negate
     function-increment
     (q132427-unary-value linear-map increment))))

(defun q132427-derivative-bound-function
    (scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set linear-map point epsilon delta)
  (list
   'lambda
   '(y)
   (q132427-implies-term
    (q132427-and-terms
     (list
      (q132427-static-apply-term domain-carrier '(y))
      (q132427-static-apply-term set '(y))
      (list
       'q132427-distance-less-p
       (q132427-quoted scalar-less)
       (q132427-quoted domain-add)
       (q132427-quoted domain-negate)
       (q132427-quoted domain-norm)
       'y
       (q132427-quoted point)
       (q132427-quoted delta))))
    (q132427-not-term
     (q132427-static-apply-term
      scalar-less
      (list
       (q132427-static-apply-term
        scalar-multiply
        (list
         (q132427-quoted epsilon)
         (q132427-static-apply-term
          domain-norm
          (list
           (list
            'q132427-vector-difference
            (q132427-quoted domain-add)
            (q132427-quoted domain-negate)
            'y
            (q132427-quoted point))))))
       (q132427-static-apply-term
        codomain-norm
        (list
         (list
          'q132427-derivative-remainder
          (q132427-quoted domain-add)
          (q132427-quoted domain-negate)
          (q132427-quoted codomain-add)
          (q132427-quoted codomain-negate)
          (q132427-quoted function)
          (q132427-quoted linear-map)
          (q132427-quoted point)
          'y)))))))))

(defun q132427-derivative-bound-p
    (scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set linear-map point epsilon delta)
  (q132427-universal-p
   (q132427-derivative-bound-function
    scalar-less scalar-multiply
    domain-carrier domain-add domain-negate domain-norm
    codomain-add codomain-negate codomain-norm
    function set linear-map point epsilon delta)
   '(y)))

(defun q132427-derivative-delta-function
    (scalar-carrier scalar-zero scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set linear-map point epsilon)
  (list
   'lambda
   '(delta)
   (q132427-and-terms
    (list
     (list
      'q132427-scalar-positive-p
      (q132427-quoted scalar-carrier)
      (q132427-quoted scalar-less)
      (q132427-quoted scalar-zero)
      'delta)
     (list
      'q132427-derivative-bound-p
      (q132427-quoted scalar-less)
      (q132427-quoted scalar-multiply)
      (q132427-quoted domain-carrier)
      (q132427-quoted domain-add)
      (q132427-quoted domain-negate)
      (q132427-quoted domain-norm)
      (q132427-quoted codomain-add)
      (q132427-quoted codomain-negate)
      (q132427-quoted codomain-norm)
      (q132427-quoted function)
      (q132427-quoted set)
      (q132427-quoted linear-map)
      (q132427-quoted point)
      (q132427-quoted epsilon)
      'delta)))))

(defun q132427-derivative-delta-exists-p
    (scalar-carrier scalar-zero scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set linear-map point epsilon)
  (q132427-exists-p
   (q132427-derivative-delta-function
    scalar-carrier scalar-zero scalar-less scalar-multiply
    domain-carrier domain-add domain-negate domain-norm
    codomain-add codomain-negate codomain-norm
    function set linear-map point epsilon)
   '(delta)))

(defun q132427-has-fderiv-within-function
    (scalar-carrier scalar-zero scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set linear-map point)
  (list
   'lambda
   '(epsilon)
   (q132427-implies-term
    (list
     'q132427-scalar-positive-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-less)
     (q132427-quoted scalar-zero)
     'epsilon)
    (list
     'q132427-derivative-delta-exists-p
     (q132427-quoted scalar-carrier)
     (q132427-quoted scalar-zero)
     (q132427-quoted scalar-less)
     (q132427-quoted scalar-multiply)
     (q132427-quoted domain-carrier)
     (q132427-quoted domain-add)
     (q132427-quoted domain-negate)
     (q132427-quoted domain-norm)
     (q132427-quoted codomain-add)
     (q132427-quoted codomain-negate)
     (q132427-quoted codomain-norm)
     (q132427-quoted function)
     (q132427-quoted set)
     (q132427-quoted linear-map)
     (q132427-quoted point)
     'epsilon))))

(defun q132427-has-fderiv-within-at-p
    (scalar-carrier scalar-zero scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set linear-map point)
  (q132427-universal-p
   (q132427-has-fderiv-within-function
    scalar-carrier scalar-zero scalar-less scalar-multiply
    domain-carrier domain-add domain-negate domain-norm
    codomain-add codomain-negate codomain-norm
    function set linear-map point)
   '(epsilon)))

(defun q132427-differentiable-witness-function
    (scalar-carrier scalar-zero scalar-add scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-smul domain-norm
     codomain-carrier codomain-add codomain-negate codomain-smul codomain-norm
     function set point)
  (list
   'lambda
   '(linear-map)
   (q132427-and-terms
    (list
     (list
      'q132427-continuous-linear-map-p
      (q132427-quoted scalar-carrier)
      (q132427-quoted scalar-zero)
      (q132427-quoted scalar-less)
      (q132427-quoted domain-carrier)
      (q132427-quoted domain-add)
      (q132427-quoted domain-smul)
      (q132427-quoted domain-norm)
      (q132427-quoted codomain-carrier)
      (q132427-quoted codomain-add)
      (q132427-quoted codomain-smul)
      (q132427-quoted codomain-norm)
      (q132427-quoted scalar-add)
      'linear-map)
     (list
      'q132427-has-fderiv-within-at-p
      (q132427-quoted scalar-carrier)
      (q132427-quoted scalar-zero)
      (q132427-quoted scalar-less)
      (q132427-quoted scalar-multiply)
      (q132427-quoted domain-carrier)
      (q132427-quoted domain-add)
      (q132427-quoted domain-negate)
      (q132427-quoted domain-norm)
      (q132427-quoted codomain-add)
      (q132427-quoted codomain-negate)
      (q132427-quoted codomain-norm)
      (q132427-quoted function)
      (q132427-quoted set)
      'linear-map
      (q132427-quoted point))))))

(defun q132427-differentiable-within-at-p
    (scalar-carrier scalar-zero scalar-add scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-smul domain-norm
     codomain-carrier codomain-add codomain-negate codomain-smul codomain-norm
     function set point)
  (and
   (q132427-member-p domain-carrier point)
   (q132427-exists-p
    (q132427-differentiable-witness-function
     scalar-carrier scalar-zero scalar-add scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-smul domain-norm
     codomain-carrier codomain-add codomain-negate codomain-smul codomain-norm
     function set point)
    '(linear-map))))

;; The failure set is measured by outer measure. Since the source set is
;; measurable, its nullity is exactly almost-everywhere differentiability for
;; the restricted measure.

(defun q132427-nondifferentiability-set
    (scalar-carrier scalar-zero scalar-add scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-smul domain-norm
     codomain-carrier codomain-add codomain-negate codomain-smul codomain-norm
     function set)
  (list
   'lambda
   '(x)
   (q132427-and-terms
    (list
     (q132427-static-apply-term domain-carrier '(x))
     (q132427-static-apply-term set '(x))
     (q132427-not-term
      (list
       'q132427-differentiable-within-at-p
       (q132427-quoted scalar-carrier)
       (q132427-quoted scalar-zero)
       (q132427-quoted scalar-add)
       (q132427-quoted scalar-less)
       (q132427-quoted scalar-multiply)
       (q132427-quoted domain-carrier)
       (q132427-quoted domain-add)
       (q132427-quoted domain-negate)
       (q132427-quoted domain-smul)
       (q132427-quoted domain-norm)
       (q132427-quoted codomain-carrier)
       (q132427-quoted codomain-add)
       (q132427-quoted codomain-negate)
       (q132427-quoted codomain-smul)
       (q132427-quoted codomain-norm)
       (q132427-quoted function)
       (q132427-quoted set)
       'x))))))

(defun q132427-null-set-p
    (scalar-zero carrier measure set)
  (and
   (q132427-valid-set-p carrier set)
   (equal
    (q132427-unary-value measure set)
    (q132427-ennreal-zero scalar-zero))))

(defun thousand-theorems-q132427-rademacher-s-theorem-statement
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse scalar-less scalar-supremum
     domain-carrier domain-zero domain-add domain-negate domain-smul domain-norm
     domain-basis domain-coordinates
     codomain-carrier codomain-zero codomain-add codomain-negate
     codomain-smul codomain-norm codomain-basis codomain-coordinates
     measurable measure function set constant)
  (implies
   (and
    (q132427-real-field-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse scalar-less scalar-supremum)
    (q132427-normed-vector-space-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-less
     domain-carrier domain-zero domain-add domain-negate domain-smul domain-norm)
    (q132427-finite-basis-p
     domain-basis domain-coordinates scalar-carrier scalar-zero
     domain-carrier domain-zero domain-add domain-smul)
    (q132427-normed-vector-space-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-less
     codomain-carrier codomain-zero codomain-add codomain-negate
     codomain-smul codomain-norm)
    (q132427-finite-basis-p
     codomain-basis codomain-coordinates scalar-carrier scalar-zero
     codomain-carrier codomain-zero codomain-add codomain-smul)
    (q132427-borel-space-p
     scalar-carrier scalar-zero scalar-less
     domain-carrier domain-add domain-negate domain-norm measurable)
    (q132427-measure-space-p
     scalar-carrier scalar-zero scalar-add scalar-less
     domain-carrier measurable measure)
    (q132427-add-haar-measure-p
     scalar-carrier scalar-zero scalar-less
     domain-carrier domain-add domain-negate domain-norm measure)
    (q132427-function-p domain-carrier codomain-carrier function)
    (q132427-valid-set-p domain-carrier set)
    (q132427-member-p measurable set)
    (q132427-lipschitz-on-with-p
     scalar-carrier scalar-zero scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-norm
     codomain-add codomain-negate codomain-norm
     function set constant))
   (q132427-null-set-p
    scalar-zero domain-carrier measure
    (q132427-nondifferentiability-set
     scalar-carrier scalar-zero scalar-add scalar-less scalar-multiply
     domain-carrier domain-add domain-negate domain-smul domain-norm
     codomain-carrier codomain-add codomain-negate codomain-smul codomain-norm
     function set))))

(value-triple :itpeval-statement-checked)
:q
