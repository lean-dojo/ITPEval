;; Statement-only formalization of thousand-theorems corpus artifact Q1144897,
;; "Brouwer fixed-point theorem": every continuous self-map of a nonempty
;; compact convex subset of a finite-dimensional real normed space has a fixed
;; point. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Sets and maps are tame APPLY$ function objects. FN-EQUAL provides
;; unbounded universal quantification, while inequality with a constant-false
;; function provides internal existential quantification. A
;; Dedekind-complete ordered field presents the real numbers. An explicit
;; finite basis presents an arbitrary finite-dimensional real normed space;
;; this is linearly homeomorphic to Euclidean coordinate space, with the same
;; compact, convex, continuous, self-map, and fixed-point predicates.

(defun q1144897-quoted (object)
  (list 'quote object))

(defun q1144897-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1144897-term-list (cdr terms)))
    (q1144897-quoted nil)))

(defun q1144897-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1144897-term-list arguments)))

(defun q1144897-static-apply-term (function arguments)
  (q1144897-apply-term
   (q1144897-quoted function)
   arguments))

(defun q1144897-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1144897-and-terms (cdr terms))
       (q1144897-quoted nil))
    (q1144897-quoted t)))

(defun q1144897-or-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1144897-quoted t)
       (q1144897-or-terms (cdr terms)))
    (q1144897-quoted nil)))

(defun q1144897-not-term (term)
  (list
   'if
   term
   (q1144897-quoted nil)
   (q1144897-quoted t)))

(defun q1144897-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1144897-quoted t)))

(defun q1144897-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1144897-quoted t)
    (q1144897-quoted nil))
   (list
    'if
    right
    (q1144897-quoted nil)
    (q1144897-quoted t))))

(defun q1144897-true-function (formals)
  (list 'lambda formals (q1144897-quoted t)))

(defun q1144897-false-function (formals)
  (list 'lambda formals (q1144897-quoted nil)))

(defun q1144897-universal-p (function formals)
  (let ((always-true
         (q1144897-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q1144897-exists-p (function formals)
  (let ((always-false
         (q1144897-false-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-false)
     (not (fn-equal function always-false)))))

(defun q1144897-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1144897-unary-value (function object)
  (apply$ function (list object)))

(defun q1144897-binary-value (function left right)
  (apply$ function (list left right)))

;; Sets over an arbitrary carrier.

(defun q1144897-set-subset-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(x))
      (q1144897-static-apply-term left '(x))))
    (q1144897-static-apply-term right '(x)))))

(defun q1144897-set-subset-p
    (carrier left right)
  (and
   (tamep-functionp carrier)
   (tamep-functionp left)
   (tamep-functionp right)
   (q1144897-universal-p
    (q1144897-set-subset-function carrier left right)
    '(x))))

(defun q1144897-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1144897-set-subset-p carrier set carrier)))

(defun q1144897-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-static-apply-term carrier '(x))
    (q1144897-iff-term
     (q1144897-static-apply-term left '(x))
     (q1144897-static-apply-term right '(x))))))

(defun q1144897-set-equiv-p
    (carrier left right)
  (and
   (q1144897-valid-set-p carrier left)
   (q1144897-valid-set-p carrier right)
   (q1144897-universal-p
    (q1144897-set-equiv-function carrier left right)
    '(x))))

(defun q1144897-empty-set ()
  (list 'lambda '(x) (q1144897-quoted nil)))

(defun q1144897-complement-set (carrier set)
  (list
   'lambda
   '(x)
   (q1144897-and-terms
    (list
     (q1144897-static-apply-term carrier '(x))
     (q1144897-not-term
      (q1144897-static-apply-term set '(x)))))))

(defun q1144897-intersection-set (left right)
  (list
   'lambda
   '(x)
   (q1144897-and-terms
    (list
     (q1144897-static-apply-term left '(x))
     (q1144897-static-apply-term right '(x))))))

(defun q1144897-symmetric-difference-set
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1144897-and-terms
    (list
     (q1144897-static-apply-term carrier '(x))
     (q1144897-or-terms
      (list
       (q1144897-and-terms
        (list
         (q1144897-static-apply-term left '(x))
         (q1144897-not-term
          (q1144897-static-apply-term right '(x)))))
       (q1144897-and-terms
        (list
         (q1144897-static-apply-term right '(x))
         (q1144897-not-term
          (q1144897-static-apply-term left '(x)))))))))))

(defun q1144897-set-nonempty-function
    (carrier set)
  (list
   'lambda
   '(x)
   (q1144897-and-terms
    (list
     (q1144897-static-apply-term carrier '(x))
     (q1144897-static-apply-term set '(x))))))

(defun q1144897-set-nonempty-p
    (carrier set)
  (and
   (q1144897-valid-set-p carrier set)
   (q1144897-exists-p
    (q1144897-set-nonempty-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun q1144897-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add
          (q1144897-static-apply-term add '(x y)))
         (yz-add
          (q1144897-static-apply-term add '(y z)))
         (xy-mul
          (q1144897-static-apply-term multiply '(x y)))
         (yz-mul
          (q1144897-static-apply-term multiply '(y z)))
         (neg-x
          (q1144897-static-apply-term negate '(x)))
         (inv-x
          (q1144897-static-apply-term inverse '(x))))
    (list
     'lambda
     '(x y z)
     (q1144897-implies-term
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term carrier '(x))
        (q1144897-static-apply-term carrier '(y))
        (q1144897-static-apply-term carrier '(z))))
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term carrier (list xy-add))
        (q1144897-static-apply-term carrier (list xy-mul))
        (q1144897-static-apply-term carrier (list neg-x))
        (q1144897-static-apply-term carrier (list inv-x))
        (list
         'equal
         (q1144897-static-apply-term add (list xy-add 'z))
         (q1144897-static-apply-term add (list 'x yz-add)))
        (list
         'equal
         xy-add
         (q1144897-static-apply-term add '(y x)))
        (list
         'equal
         (q1144897-static-apply-term
          add
          (list 'x (q1144897-quoted zero)))
         'x)
        (list
         'equal
         (q1144897-static-apply-term add (list 'x neg-x))
         (q1144897-quoted zero))
        (list
         'equal
         (q1144897-static-apply-term multiply (list xy-mul 'z))
         (q1144897-static-apply-term multiply (list 'x yz-mul)))
        (list
         'equal
         xy-mul
         (q1144897-static-apply-term multiply '(y x)))
        (list
         'equal
         (q1144897-static-apply-term
          multiply
          (list 'x (q1144897-quoted one)))
         'x)
        (q1144897-implies-term
         (list 'equal 'x (q1144897-quoted zero))
         (list 'equal inv-x (q1144897-quoted zero)))
        (q1144897-implies-term
         (q1144897-not-term
          (list 'equal 'x (q1144897-quoted zero)))
         (list
          'equal
          (q1144897-static-apply-term
           multiply
           (list 'x inv-x))
          (q1144897-quoted one)))
        (list
         'equal
         (q1144897-static-apply-term multiply (list 'x yz-add))
         (q1144897-static-apply-term
          add
          (list
           (q1144897-static-apply-term multiply '(x y))
           (q1144897-static-apply-term multiply '(x z)))))))))))

(defun q1144897-order-laws-function
    (carrier zero add multiply less)
  (let ((xy
         (q1144897-static-apply-term less '(x y)))
        (yx
         (q1144897-static-apply-term less '(y x)))
        (yz
         (q1144897-static-apply-term less '(y z))))
    (list
     'lambda
     '(x y z)
     (q1144897-implies-term
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term carrier '(x))
        (q1144897-static-apply-term carrier '(y))
        (q1144897-static-apply-term carrier '(z))))
      (q1144897-and-terms
       (list
        (q1144897-not-term
         (q1144897-static-apply-term less '(x x)))
        (q1144897-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (q1144897-implies-term
         (q1144897-and-terms (list xy yz))
         (q1144897-static-apply-term less '(x z)))
        (q1144897-implies-term
         xy
         (q1144897-static-apply-term
          less
          (list
           (q1144897-static-apply-term add '(x z))
           (q1144897-static-apply-term add '(y z)))))
        (q1144897-implies-term
         (q1144897-and-terms
          (list
           (q1144897-static-apply-term
            less
            (list (q1144897-quoted zero) 'x))
           (q1144897-static-apply-term
            less
            (list (q1144897-quoted zero) 'y))))
         (q1144897-static-apply-term
          less
          (list
           (q1144897-quoted zero)
           (q1144897-static-apply-term multiply '(x y)))))))))))

(defun q1144897-upper-bound-function
    (carrier less set upper)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(x))
      (q1144897-static-apply-term set '(x))))
    (q1144897-not-term
     (q1144897-static-apply-term
      less
      (list (q1144897-quoted upper) 'x))))))

(defun q1144897-upper-bound-p
    (carrier less set upper)
  (and
   (q1144897-member-p carrier upper)
   (q1144897-valid-set-p carrier set)
   (q1144897-universal-p
    (q1144897-upper-bound-function
     carrier less set upper)
    '(x))))

(defun q1144897-bounded-above-function
    (carrier less set)
  (list
   'lambda
   '(upper)
   (list
    'q1144897-upper-bound-p
    (q1144897-quoted carrier)
    (q1144897-quoted less)
    (q1144897-quoted set)
    'upper)))

(defun q1144897-bounded-above-p
    (carrier less set)
  (q1144897-exists-p
   (q1144897-bounded-above-function carrier less set)
   '(upper)))

(defun q1144897-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda
   '(upper)
   (q1144897-implies-term
    (list
     'q1144897-upper-bound-p
     (q1144897-quoted carrier)
     (q1144897-quoted less)
     (q1144897-quoted set)
     'upper)
    (q1144897-not-term
     (q1144897-static-apply-term
      less
      (list 'upper (q1144897-quoted supremum)))))))

(defun q1144897-least-upper-bound-p
    (carrier less set supremum)
  (and
   (q1144897-upper-bound-p carrier less set supremum)
   (q1144897-universal-p
    (q1144897-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun q1144897-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda
   '(set)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (list
       'q1144897-valid-set-p
       (q1144897-quoted carrier)
       'set)
      (list
       'q1144897-set-nonempty-p
       (q1144897-quoted carrier)
       'set)
      (list
       'q1144897-bounded-above-p
       (q1144897-quoted carrier)
       (q1144897-quoted less)
       'set)))
    (list
     'q1144897-least-upper-bound-p
     (q1144897-quoted carrier)
     (q1144897-quoted less)
     'set
     (q1144897-static-apply-term
      supremum-operation
      '(set))))))

(defun q1144897-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (q1144897-member-p carrier zero)
   (q1144897-member-p carrier one)
   (not (equal zero one))
   (q1144897-member-p
    carrier
    (q1144897-unary-value inverse zero))
   (q1144897-universal-p
    (q1144897-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (q1144897-universal-p
    (q1144897-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (q1144897-member-p
    carrier
    (q1144897-unary-value supremum
                           (q1144897-empty-set)))
   (q1144897-universal-p
    (q1144897-completeness-function
     carrier less supremum)
    '(set))
   (q1144897-binary-value less zero one)))

(defun q1144897-scalar-nonnegative-p
    (less zero value)
  (not (q1144897-binary-value less value zero)))

(defun q1144897-scalar-positive-p
    (carrier less zero value)
  (and
   (q1144897-member-p carrier value)
   (q1144897-binary-value less zero value)))

(defun q1144897-scalar-absolute-value
    (less zero negate value)
  (if (q1144897-binary-value less value zero)
      (q1144897-unary-value negate value)
    value))

(defun q1144897-field-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (q1144897-binary-value
     add
     one
     (q1144897-field-natural
      (- n 1) zero one add))))

(defun q1144897-field-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (q1144897-binary-value
     multiply
     base
     (q1144897-field-power
      base (- exponent 1) one multiply))))

;; Finite-dimensional normed vector spaces over the represented real field.

(defun q1144897-vector-laws-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate smul)
  (let* ((xy
          (q1144897-static-apply-term add '(x y)))
         (yz
          (q1144897-static-apply-term add '(y z)))
         (neg-x
          (q1144897-static-apply-term negate '(x)))
         (a-x
          (q1144897-static-apply-term smul '(a x))))
    (list
     'lambda
     '(a b x y z)
     (q1144897-implies-term
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term scalar-carrier '(a))
        (q1144897-static-apply-term scalar-carrier '(b))
        (q1144897-static-apply-term carrier '(x))
        (q1144897-static-apply-term carrier '(y))
        (q1144897-static-apply-term carrier '(z))))
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term carrier (list xy))
        (q1144897-static-apply-term carrier (list neg-x))
        (q1144897-static-apply-term carrier (list a-x))
        (list
         'equal
         (q1144897-static-apply-term add (list xy 'z))
         (q1144897-static-apply-term add (list 'x yz)))
        (list
         'equal
         xy
         (q1144897-static-apply-term add '(y x)))
        (list
         'equal
         (q1144897-static-apply-term
          add
          (list 'x (q1144897-quoted zero)))
         'x)
        (list
         'equal
         (q1144897-static-apply-term add (list 'x neg-x))
         (q1144897-quoted zero))
        (list
         'equal
         (q1144897-static-apply-term
          smul
          (list (q1144897-quoted scalar-one) 'x))
         'x)
        (list
         'equal
         (q1144897-static-apply-term
          smul
          (list
           (q1144897-static-apply-term
            scalar-multiply
            '(a b))
           'x))
         (q1144897-static-apply-term
          smul
          (list
           'a
           (q1144897-static-apply-term smul '(b x)))))
        (list
         'equal
         (q1144897-static-apply-term
          smul
          (list
           (q1144897-static-apply-term scalar-add '(a b))
           'x))
         (q1144897-static-apply-term
          add
          (list
           a-x
           (q1144897-static-apply-term smul '(b x)))))
        (list
         'equal
         (q1144897-static-apply-term smul (list 'a xy))
         (q1144897-static-apply-term
          add
          (list
           a-x
           (q1144897-static-apply-term smul '(a y)))))
        (list
         'equal
         (q1144897-static-apply-term
          smul
          (list (q1144897-quoted scalar-zero) 'x))
         (q1144897-quoted zero))))))))

(defun q1144897-norm-laws-function
    (scalar-carrier scalar-zero scalar-add scalar-multiply scalar-negate
     scalar-less carrier zero add negate smul norm)
  (let* ((norm-x
          (q1144897-static-apply-term norm '(x)))
         (norm-y
          (q1144897-static-apply-term norm '(y)))
         (norm-a-x
          (q1144897-static-apply-term
           norm
           (list
            (q1144897-static-apply-term smul '(a x)))))
         (abs-a
          (list
           'q1144897-scalar-absolute-value
           (q1144897-quoted scalar-less)
           (q1144897-quoted scalar-zero)
           (q1144897-quoted scalar-negate)
           'a)))
    (list
     'lambda
     '(a x y)
     (q1144897-implies-term
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term scalar-carrier '(a))
        (q1144897-static-apply-term carrier '(x))
        (q1144897-static-apply-term carrier '(y))))
      (q1144897-and-terms
       (list
        (q1144897-static-apply-term scalar-carrier (list norm-x))
        (q1144897-not-term
         (q1144897-static-apply-term
          scalar-less
          (list norm-x (q1144897-quoted scalar-zero))))
        (q1144897-iff-term
         (list 'equal norm-x (q1144897-quoted scalar-zero))
         (list 'equal 'x (q1144897-quoted zero)))
        (list
         'equal
         (q1144897-static-apply-term
          norm
          (list
           (q1144897-static-apply-term negate '(x))))
         norm-x)
        (list
         'equal
         norm-a-x
         (q1144897-static-apply-term
          scalar-multiply
          (list abs-a norm-x)))
        (q1144897-not-term
         (q1144897-static-apply-term
          scalar-less
          (list
           (q1144897-static-apply-term
            scalar-add
            (list norm-x norm-y))
           (q1144897-static-apply-term
            norm
            (list
             (q1144897-static-apply-term add '(x y)))))))))))))

(defun q1144897-normed-vector-space-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-less
     carrier zero add negate smul norm)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp negate)
   (tamep-functionp smul)
   (tamep-functionp norm)
   (q1144897-member-p carrier zero)
   (q1144897-universal-p
    (q1144897-vector-laws-function
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add negate smul)
    '(a b x y z))
   (q1144897-universal-p
    (q1144897-norm-laws-function
     scalar-carrier scalar-zero scalar-add scalar-multiply scalar-negate
     scalar-less carrier zero add negate smul norm)
    '(a x y))))

(defun q1144897-coefficient-list-p
    (coefficients basis scalar-carrier)
  (if (consp basis)
      (and
       (consp coefficients)
       (q1144897-member-p scalar-carrier (car coefficients))
       (q1144897-coefficient-list-p
        (cdr coefficients)
        (cdr basis)
        scalar-carrier))
    (equal coefficients nil)))

(defun q1144897-basis-elements-p
    (basis carrier)
  (if (consp basis)
      (and
       (q1144897-member-p carrier (car basis))
       (q1144897-basis-elements-p
        (cdr basis) carrier))
    (equal basis nil)))

(defun q1144897-linear-combination
    (coefficients basis vector-zero vector-add smul)
  (if (consp basis)
      (q1144897-binary-value
       vector-add
       (q1144897-binary-value
        smul
        (car coefficients)
        (car basis))
       (q1144897-linear-combination
        (cdr coefficients)
        (cdr basis)
        vector-zero vector-add smul))
    vector-zero))

(defun q1144897-all-zero-coefficients-p
    (coefficients scalar-zero)
  (if (consp coefficients)
      (and
       (equal (car coefficients) scalar-zero)
       (q1144897-all-zero-coefficients-p
        (cdr coefficients) scalar-zero))
    (equal coefficients nil)))

(defun q1144897-basis-independence-function
    (basis scalar-carrier scalar-zero
           vector-zero vector-add smul)
  (list
   'lambda
   '(coefficients)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (list
       'q1144897-coefficient-list-p
       'coefficients
       (q1144897-quoted basis)
       (q1144897-quoted scalar-carrier))
      (list
       'equal
       (list
        'q1144897-linear-combination
        'coefficients
        (q1144897-quoted basis)
        (q1144897-quoted vector-zero)
        (q1144897-quoted vector-add)
        (q1144897-quoted smul))
       (q1144897-quoted vector-zero))))
    (list
     'q1144897-all-zero-coefficients-p
     'coefficients
     (q1144897-quoted scalar-zero)))))

(defun q1144897-basis-spanning-function
    (basis coordinates scalar-carrier carrier
           vector-zero vector-add smul)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-static-apply-term carrier '(x))
    (q1144897-and-terms
     (list
      (list
       'q1144897-coefficient-list-p
       (q1144897-static-apply-term coordinates '(x))
       (q1144897-quoted basis)
       (q1144897-quoted scalar-carrier))
      (list
       'equal
       (list
        'q1144897-linear-combination
        (q1144897-static-apply-term coordinates '(x))
        (q1144897-quoted basis)
        (q1144897-quoted vector-zero)
        (q1144897-quoted vector-add)
        (q1144897-quoted smul))
       'x))))))

(defun q1144897-finite-basis-p
    (basis coordinates scalar-carrier scalar-zero
           carrier vector-zero vector-add smul)
  (and
   (true-listp basis)
   (tamep-functionp coordinates)
   (q1144897-basis-elements-p basis carrier)
   (q1144897-universal-p
    (q1144897-basis-independence-function
     basis scalar-carrier scalar-zero
     vector-zero vector-add smul)
    '(coefficients))
   (q1144897-universal-p
    (q1144897-basis-spanning-function
     basis coordinates scalar-carrier carrier
     vector-zero vector-add smul)
    '(x))))

;; Norm topology, convergence, and compactness.

(defun q1144897-vector-difference
    (add negate left right)
  (q1144897-binary-value
   add left (q1144897-unary-value negate right)))

(defun q1144897-distance-less-p
    (scalar-less vector-add vector-negate norm
                 left right epsilon)
  (q1144897-binary-value
   scalar-less
   (q1144897-unary-value
    norm
    (q1144897-vector-difference
     vector-add vector-negate left right))
   epsilon))

(defun q1144897-ball-subset-function
    (carrier vector-add vector-negate norm scalar-less
             center epsilon set)
  (list
   'lambda
   '(y)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(y))
      (list
       'q1144897-distance-less-p
       (q1144897-quoted scalar-less)
       (q1144897-quoted vector-add)
       (q1144897-quoted vector-negate)
       (q1144897-quoted norm)
       (q1144897-quoted center)
       'y
       (q1144897-quoted epsilon))))
    (q1144897-static-apply-term set '(y)))))

(defun q1144897-ball-subset-p
    (carrier vector-add vector-negate norm scalar-less
             center epsilon set)
  (q1144897-universal-p
   (q1144897-ball-subset-function
    carrier vector-add vector-negate norm scalar-less
    center epsilon set)
   '(y)))

(defun q1144897-open-radius-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set x)
  (list
   'lambda
   '(epsilon)
   (q1144897-and-terms
    (list
     (list
      'q1144897-scalar-positive-p
      (q1144897-quoted scalar-carrier)
      (q1144897-quoted scalar-less)
      (q1144897-quoted scalar-zero)
      'epsilon)
     (list
      'q1144897-ball-subset-p
      (q1144897-quoted carrier)
      (q1144897-quoted vector-add)
      (q1144897-quoted vector-negate)
      (q1144897-quoted norm)
      (q1144897-quoted scalar-less)
      (q1144897-quoted x)
      'epsilon
      (q1144897-quoted set))))))

(defun q1144897-open-radius-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set x)
  (q1144897-exists-p
   (q1144897-open-radius-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm set x)
   '(epsilon)))

(defun q1144897-open-set-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(x))
      (q1144897-static-apply-term set '(x))))
    (list
     'q1144897-open-radius-exists-p
     (q1144897-quoted scalar-carrier)
     (q1144897-quoted scalar-zero)
     (q1144897-quoted scalar-less)
     (q1144897-quoted carrier)
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-quoted set)
     'x))))

(defun q1144897-open-set-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (and
   (q1144897-valid-set-p carrier set)
   (q1144897-universal-p
    (q1144897-open-set-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    '(x))))

(defun q1144897-sequence-in-set-function
    (carrier set sequence)
  (list
   'lambda
   '(n)
   (q1144897-implies-term
    (list 'natp 'n)
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term
       carrier
       (list
        (q1144897-static-apply-term sequence '(n))))
      (q1144897-static-apply-term
       set
       (list
        (q1144897-static-apply-term sequence '(n)))))))))

(defun q1144897-sequence-in-set-p
    (carrier set sequence)
  (and
   (tamep-functionp sequence)
   (q1144897-universal-p
    (q1144897-sequence-in-set-function
     carrier set sequence)
    '(n))))

(defun q1144897-convergence-tail-function
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon start)
  (list
   'lambda
   '(n)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (list 'natp 'n)
      (list '<= (q1144897-quoted start) 'n)))
    (list
     'q1144897-distance-less-p
     (q1144897-quoted scalar-less)
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-static-apply-term sequence '(n))
     (q1144897-quoted limit)
     (q1144897-quoted epsilon)))))

(defun q1144897-convergence-tail-p
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon start)
  (and
   (natp start)
   (q1144897-universal-p
    (q1144897-convergence-tail-function
     vector-add vector-negate norm scalar-less
     sequence limit epsilon start)
    '(n))))

(defun q1144897-convergence-start-function
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon)
  (list
   'lambda
   '(start)
   (list
    'q1144897-convergence-tail-p
    (q1144897-quoted vector-add)
    (q1144897-quoted vector-negate)
    (q1144897-quoted norm)
    (q1144897-quoted scalar-less)
    (q1144897-quoted sequence)
    (q1144897-quoted limit)
    (q1144897-quoted epsilon)
    'start)))

(defun q1144897-convergence-start-exists-p
    (vector-add vector-negate norm scalar-less
                sequence limit epsilon)
  (q1144897-exists-p
   (q1144897-convergence-start-function
    vector-add vector-negate norm scalar-less
    sequence limit epsilon)
   '(start)))

(defun q1144897-convergence-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     vector-add vector-negate norm sequence limit)
  (list
   'lambda
   '(epsilon)
   (q1144897-implies-term
    (list
     'q1144897-scalar-positive-p
     (q1144897-quoted scalar-carrier)
     (q1144897-quoted scalar-less)
     (q1144897-quoted scalar-zero)
     'epsilon)
    (list
     'q1144897-convergence-start-exists-p
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-quoted scalar-less)
     (q1144897-quoted sequence)
     (q1144897-quoted limit)
     'epsilon))))

(defun q1144897-converges-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm sequence limit)
  (and
   (tamep-functionp sequence)
   (q1144897-member-p carrier limit)
   (q1144897-universal-p
    (q1144897-convergence-epsilon-function
     scalar-carrier scalar-zero scalar-less
     vector-add vector-negate norm sequence limit)
    '(epsilon))))

(defun q1144897-subsequence-laws-function
    (subsequence)
  (list
   'lambda
   '(m n)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (list 'natp 'm)
      (list 'natp 'n)))
    (q1144897-and-terms
     (list
      (list
       'natp
       (q1144897-static-apply-term subsequence '(m)))
      (q1144897-implies-term
       (list '< 'm 'n)
       (list
        '<
        (q1144897-static-apply-term subsequence '(m))
        (q1144897-static-apply-term subsequence '(n)))))))))

(defun q1144897-subsequence-p (subsequence)
  (and
   (tamep-functionp subsequence)
   (q1144897-universal-p
    (q1144897-subsequence-laws-function subsequence)
    '(m n))))

(defun q1144897-compose-sequence
    (sequence subsequence)
  (list
   'lambda
   '(n)
   (q1144897-static-apply-term
    sequence
    (list
     (q1144897-static-apply-term subsequence '(n))))))

(defun q1144897-compact-witness-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     set sequence subsequence limit)
  (and
   (q1144897-subsequence-p subsequence)
   (q1144897-member-p carrier limit)
   (q1144897-member-p set limit)
   (q1144897-converges-p
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm
    (q1144897-compose-sequence sequence subsequence)
    limit)))

(defun q1144897-compact-witness-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set sequence)
  (list
   'lambda
   '(subsequence limit)
   (list
    'q1144897-compact-witness-p
    (q1144897-quoted scalar-carrier)
    (q1144897-quoted scalar-zero)
    (q1144897-quoted scalar-less)
    (q1144897-quoted carrier)
    (q1144897-quoted vector-add)
    (q1144897-quoted vector-negate)
    (q1144897-quoted norm)
    (q1144897-quoted set)
    (q1144897-quoted sequence)
    'subsequence
    'limit)))

(defun q1144897-compact-witness-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set sequence)
  (q1144897-exists-p
   (q1144897-compact-witness-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm set sequence)
   '(subsequence limit)))

(defun q1144897-compact-set-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (list
   'lambda
   '(sequence)
   (q1144897-implies-term
    (list
     'q1144897-sequence-in-set-p
     (q1144897-quoted carrier)
     (q1144897-quoted set)
     'sequence)
    (list
     'q1144897-compact-witness-exists-p
     (q1144897-quoted scalar-carrier)
     (q1144897-quoted scalar-zero)
     (q1144897-quoted scalar-less)
     (q1144897-quoted carrier)
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-quoted set)
     'sequence))))

(defun q1144897-compact-set-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
  (and
   (q1144897-valid-set-p carrier set)
   (q1144897-universal-p
    (q1144897-compact-set-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    '(sequence))))

;; Functions and continuity in the norm topology.

(defun q1144897-function-values-function
    (carrier function)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-static-apply-term carrier '(x))
    (q1144897-static-apply-term
     carrier
     (list (q1144897-static-apply-term function '(x)))))))

(defun q1144897-endomap-p
    (carrier function)
  (and
   (tamep-functionp carrier)
   (tamep-functionp function)
   (q1144897-universal-p
    (q1144897-function-values-function carrier function)
    '(x))))

(defun q1144897-continuity-nearby-function
    (scalar-less carrier vector-add vector-negate norm
     function set point epsilon delta)
  (list
   'lambda
   '(nearby)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(nearby))
      (q1144897-static-apply-term set '(nearby))
      (list
       'q1144897-distance-less-p
       (q1144897-quoted scalar-less)
       (q1144897-quoted vector-add)
       (q1144897-quoted vector-negate)
       (q1144897-quoted norm)
       (q1144897-quoted point)
       'nearby
       (q1144897-quoted delta))))
    (list
     'q1144897-distance-less-p
     (q1144897-quoted scalar-less)
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-static-apply-term
      function
      (list (q1144897-quoted point)))
     (q1144897-static-apply-term function '(nearby))
     (q1144897-quoted epsilon)))))

(defun q1144897-continuity-radius-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set point epsilon)
  (list
   'lambda
   '(delta)
   (q1144897-and-terms
    (list
     (list
      'q1144897-scalar-positive-p
      (q1144897-quoted scalar-carrier)
      (q1144897-quoted scalar-less)
      (q1144897-quoted scalar-zero)
      'delta)
     (list
      'q1144897-universal-p
      (list
       'q1144897-continuity-nearby-function
       (q1144897-quoted scalar-less)
       (q1144897-quoted carrier)
       (q1144897-quoted vector-add)
       (q1144897-quoted vector-negate)
       (q1144897-quoted norm)
       (q1144897-quoted function)
       (q1144897-quoted set)
       (q1144897-quoted point)
       (q1144897-quoted epsilon)
       'delta)
      (q1144897-quoted '(nearby)))))))

(defun q1144897-continuity-radius-exists-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set point epsilon)
  (q1144897-exists-p
   (q1144897-continuity-radius-function
    scalar-carrier scalar-zero scalar-less
    carrier vector-add vector-negate norm
    function set point epsilon)
   '(delta)))

(defun q1144897-continuity-epsilon-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set point)
  (list
   'lambda
   '(epsilon)
   (q1144897-implies-term
    (list
     'q1144897-scalar-positive-p
     (q1144897-quoted scalar-carrier)
     (q1144897-quoted scalar-less)
     (q1144897-quoted scalar-zero)
     'epsilon)
    (list
     'q1144897-continuity-radius-exists-p
     (q1144897-quoted scalar-carrier)
     (q1144897-quoted scalar-zero)
     (q1144897-quoted scalar-less)
     (q1144897-quoted carrier)
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-quoted function)
     (q1144897-quoted set)
     (q1144897-quoted point)
     'epsilon))))

(defun q1144897-continuous-within-at-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set point)
  (and
   (q1144897-member-p carrier point)
   (q1144897-member-p set point)
   (q1144897-universal-p
    (q1144897-continuity-epsilon-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set point)
    '(epsilon))))

(defun q1144897-continuous-on-function
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set)
  (list
   'lambda
   '(point)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(point))
      (q1144897-static-apply-term set '(point))))
    (list
     'q1144897-continuous-within-at-p
     (q1144897-quoted scalar-carrier)
     (q1144897-quoted scalar-zero)
     (q1144897-quoted scalar-less)
     (q1144897-quoted carrier)
     (q1144897-quoted vector-add)
     (q1144897-quoted vector-negate)
     (q1144897-quoted norm)
     (q1144897-quoted function)
     (q1144897-quoted set)
     'point))))

(defun q1144897-continuous-on-p
    (scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set)
  (and
   (q1144897-valid-set-p carrier set)
   (q1144897-endomap-p carrier function)
   (q1144897-universal-p
    (q1144897-continuous-on-function
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm
     function set)
    '(point))))

;; Convexity and the self-map condition.

(defun q1144897-convex-set-function
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
  (list
   'lambda
   '(a b x y)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term scalar-carrier '(a))
      (q1144897-static-apply-term scalar-carrier '(b))
      (q1144897-not-term
       (q1144897-static-apply-term
        scalar-less
        (list 'a (q1144897-quoted scalar-zero))))
      (q1144897-not-term
       (q1144897-static-apply-term
        scalar-less
        (list 'b (q1144897-quoted scalar-zero))))
      (list
       'equal
       (q1144897-static-apply-term scalar-add '(a b))
       (q1144897-quoted scalar-one))
      (q1144897-static-apply-term carrier '(x))
      (q1144897-static-apply-term carrier '(y))
      (q1144897-static-apply-term set '(x))
      (q1144897-static-apply-term set '(y))))
    (q1144897-static-apply-term
     set
     (list
      (q1144897-static-apply-term
       vector-add
       (list
        (q1144897-static-apply-term smul '(a x))
        (q1144897-static-apply-term smul '(b y)))))))))

(defun q1144897-convex-set-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
  (and
   (q1144897-valid-set-p carrier set)
   (q1144897-universal-p
    (q1144897-convex-set-function
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
    '(a b x y))))

(defun q1144897-self-map-function
    (carrier function set)
  (list
   'lambda
   '(x)
   (q1144897-implies-term
    (q1144897-and-terms
     (list
      (q1144897-static-apply-term carrier '(x))
      (q1144897-static-apply-term set '(x))))
    (q1144897-static-apply-term
     set
     (list (q1144897-static-apply-term function '(x)))))))

(defun q1144897-self-map-p
    (carrier function set)
  (and
   (q1144897-valid-set-p carrier set)
   (q1144897-endomap-p carrier function)
   (q1144897-universal-p
    (q1144897-self-map-function carrier function set)
    '(x))))

;; The fixed point is an internal existential witness.

(defun q1144897-fixed-point-function
    (carrier function set)
  (list
   'lambda
   '(x)
   (q1144897-and-terms
    (list
     (q1144897-static-apply-term carrier '(x))
     (q1144897-static-apply-term set '(x))
     (list
      'equal
      (q1144897-static-apply-term function '(x))
      'x)))))

(defun q1144897-fixed-point-exists-p
    (carrier function set)
  (q1144897-exists-p
   (q1144897-fixed-point-function carrier function set)
   '(x)))

(defun thousand-theorems-q1144897-brouwer-fixed-point-theorem-statement
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     scalar-negate scalar-inverse scalar-less scalar-supremum
     carrier vector-zero vector-add vector-negate smul norm
     basis coordinates set function)
  (implies
   (and
    (q1144897-real-field-p
     scalar-carrier scalar-zero scalar-one
     scalar-add scalar-multiply scalar-negate scalar-inverse
     scalar-less scalar-supremum)
    (q1144897-normed-vector-space-p
     scalar-carrier scalar-zero scalar-one
     scalar-add scalar-multiply scalar-negate scalar-less
     carrier vector-zero vector-add vector-negate smul norm)
    (q1144897-finite-basis-p
     basis coordinates scalar-carrier scalar-zero
     carrier vector-zero vector-add smul)
    (q1144897-compact-set-p
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm set)
    (q1144897-convex-set-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-less
     carrier vector-add smul set)
    (q1144897-set-nonempty-p carrier set)
    (q1144897-continuous-on-p
     scalar-carrier scalar-zero scalar-less
     carrier vector-add vector-negate norm function set)
    (q1144897-self-map-p carrier function set))
   (q1144897-fixed-point-exists-p carrier function set)))

(value-triple :itpeval-statement-checked)
:q
