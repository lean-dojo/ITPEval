;; Statement-only formalization of hundred-theorems corpus artifact 064,
;; "L'Hôpital's Rule": the two-sided real 0/0 rule at a finite point, with
;; supplied derivatives on a punctured neighborhood and convergence of the
;; derivative quotient. This file contains no proof.
;; Manual semantic audit (2026-09-06): retained as a historical candidate,
;; but not counted as a faithful standard-ACL2 translation. See
;; corpus-extension/semantic_canonical_resolutions.json for the blocker.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary sets and functions are tame APPLY$ function objects. FN-EQUAL
;; supplies unbounded universal quantification, and inequality with a
;; constant-false function supplies internal existential quantification.
;; The scalar context is a Dedekind-complete ordered field, hence a
;; presentation of the real field. Derivatives and limits are expanded below
;; by their epsilon-delta definitions; no analytic predicate is left
;; uninterpreted.

(defun ht064-quoted (object)
  (list 'quote object))

(defun ht064-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (ht064-term-list (cdr terms)))
    (ht064-quoted nil)))

(defun ht064-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (ht064-term-list arguments)))

(defun ht064-static-apply-term (function arguments)
  (ht064-apply-term
   (ht064-quoted function)
   arguments))

(defun ht064-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht064-and-terms (cdr terms))
            (ht064-quoted nil))
    (ht064-quoted t)))

(defun ht064-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht064-quoted t)
            (ht064-or-terms (cdr terms)))
    (ht064-quoted nil)))

(defun ht064-not-term (term)
  (list 'if term
        (ht064-quoted nil)
        (ht064-quoted t)))

(defun ht064-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (ht064-quoted t)))

(defun ht064-true-function (formals)
  (list 'lambda formals (ht064-quoted t)))

(defun ht064-false-function (formals)
  (list 'lambda formals (ht064-quoted nil)))

(defun ht064-universal-p (function formals)
  (let ((always-true (ht064-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun ht064-exists-p (function formals)
  (let ((always-false (ht064-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun ht064-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht064-unary-value (function object)
  (apply$ function (list object)))

(defun ht064-binary-value (function left right)
  (apply$ function (list left right)))

;; Arbitrary real-valued functions and arbitrary subsets of the real carrier.

(defun ht064-function-values-function (carrier function)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-static-apply-term carrier '(x))
    (ht064-static-apply-term
     carrier
     (list (ht064-static-apply-term function '(x)))))))

(defun ht064-real-function-p (carrier function)
  (and
   (tamep-functionp function)
   (ht064-universal-p
    (ht064-function-values-function carrier function)
    '(x))))

(defun ht064-set-subset-carrier-function (carrier set)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-static-apply-term set '(x))
    (ht064-static-apply-term carrier '(x)))))

(defun ht064-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (ht064-universal-p
    (ht064-set-subset-carrier-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun ht064-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (ht064-static-apply-term add '(x y)))
         (yz-add (ht064-static-apply-term add '(y z)))
         (xy-mul (ht064-static-apply-term multiply '(x y)))
         (yz-mul (ht064-static-apply-term multiply '(y z)))
         (neg-x (ht064-static-apply-term negate '(x)))
         (inv-x (ht064-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (ht064-implies-term
      (ht064-and-terms
       (list
        (ht064-static-apply-term carrier '(x))
        (ht064-static-apply-term carrier '(y))
        (ht064-static-apply-term carrier '(z))))
      (ht064-and-terms
       (list
        (ht064-static-apply-term carrier (list xy-add))
        (ht064-static-apply-term carrier (list xy-mul))
        (ht064-static-apply-term carrier (list neg-x))
        (ht064-static-apply-term carrier (list inv-x))
        (list 'equal
              (ht064-static-apply-term add (list xy-add 'z))
              (ht064-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (ht064-static-apply-term add '(y x)))
        (list 'equal
              (ht064-static-apply-term
               add (list 'x (ht064-quoted zero)))
              'x)
        (list 'equal
              (ht064-static-apply-term add (list 'x neg-x))
              (ht064-quoted zero))
        (list 'equal
              (ht064-static-apply-term multiply (list xy-mul 'z))
              (ht064-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (ht064-static-apply-term multiply '(y x)))
        (list 'equal
              (ht064-static-apply-term
               multiply (list 'x (ht064-quoted one)))
              'x)
        (ht064-implies-term
         (list 'equal 'x (ht064-quoted zero))
         (list 'equal inv-x (ht064-quoted zero)))
        (ht064-implies-term
         (ht064-not-term
          (list 'equal 'x (ht064-quoted zero)))
         (list 'equal
               (ht064-static-apply-term
                multiply (list 'x inv-x))
               (ht064-quoted one)))
        (list 'equal
              (ht064-static-apply-term multiply (list 'x yz-add))
              (ht064-static-apply-term
               add
               (list
                (ht064-static-apply-term multiply '(x y))
                (ht064-static-apply-term multiply '(x z)))))))))))

(defun ht064-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (ht064-static-apply-term less '(x y)))
        (yx (ht064-static-apply-term less '(y x)))
        (yz (ht064-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (ht064-implies-term
      (ht064-and-terms
       (list
        (ht064-static-apply-term carrier '(x))
        (ht064-static-apply-term carrier '(y))
        (ht064-static-apply-term carrier '(z))))
      (ht064-and-terms
       (list
        (ht064-not-term
         (ht064-static-apply-term less '(x x)))
        (ht064-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (ht064-implies-term
         (ht064-and-terms (list xy yz))
         (ht064-static-apply-term less '(x z)))
        (ht064-implies-term
         xy
         (ht064-static-apply-term
          less
          (list
           (ht064-static-apply-term add '(x z))
           (ht064-static-apply-term add '(y z)))))
        (ht064-implies-term
         (ht064-and-terms
          (list
           (ht064-static-apply-term
            less (list (ht064-quoted zero) 'x))
           (ht064-static-apply-term
            less (list (ht064-quoted zero) 'y))))
         (ht064-static-apply-term
          less
          (list
           (ht064-quoted zero)
           (ht064-static-apply-term multiply '(x y)))))))))))

(defun ht064-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-and-terms
     (list
      (ht064-static-apply-term carrier '(x))
      (ht064-static-apply-term set '(x))))
    (ht064-not-term
     (ht064-static-apply-term
      less (list (ht064-quoted upper) 'x))))))

(defun ht064-upper-bound-p
    (carrier less set upper)
  (and
   (ht064-member-p carrier upper)
   (ht064-valid-set-p carrier set)
   (ht064-universal-p
    (ht064-upper-bound-function carrier less set upper)
    '(x))))

(defun ht064-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (ht064-and-terms
    (list
     (ht064-static-apply-term carrier '(x))
     (ht064-static-apply-term set '(x))))))

(defun ht064-set-nonempty-p (carrier set)
  (and
   (ht064-valid-set-p carrier set)
   (ht064-exists-p
    (ht064-set-nonempty-function carrier set)
    '(x))))

(defun ht064-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'ht064-upper-bound-p
         (ht064-quoted carrier)
         (ht064-quoted less)
         (ht064-quoted set)
         'upper)))

(defun ht064-bounded-above-p (carrier less set)
  (ht064-exists-p
   (ht064-bounded-above-function carrier less set)
   '(upper)))

(defun ht064-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (ht064-implies-term
    (list 'ht064-upper-bound-p
          (ht064-quoted carrier)
          (ht064-quoted less)
          (ht064-quoted set)
          'upper)
    (ht064-not-term
     (ht064-static-apply-term
      less (list 'upper (ht064-quoted supremum)))))))

(defun ht064-least-upper-bound-p
    (carrier less set supremum)
  (and
   (ht064-upper-bound-p carrier less set supremum)
   (ht064-universal-p
    (ht064-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun ht064-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (ht064-implies-term
    (ht064-and-terms
     (list
      (list 'ht064-valid-set-p
            (ht064-quoted carrier) 'set)
      (list 'ht064-set-nonempty-p
            (ht064-quoted carrier) 'set)
      (list 'ht064-bounded-above-p
            (ht064-quoted carrier)
            (ht064-quoted less)
            'set)))
    (list 'ht064-least-upper-bound-p
          (ht064-quoted carrier)
          (ht064-quoted less)
          'set
          (ht064-static-apply-term
           supremum-operation '(set))))))

(defun ht064-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (ht064-member-p carrier zero)
   (ht064-member-p carrier one)
   (not (equal zero one))
   (ht064-universal-p
    (ht064-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (ht064-universal-p
    (ht064-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (ht064-universal-p
    (ht064-completeness-function
     carrier less supremum)
    '(set))
   (ht064-binary-value less zero one)))

;; Real-field context and arithmetic.

(defun ht064-r-carrier (ctx) (nth 0 ctx))
(defun ht064-r-zero (ctx) (nth 1 ctx))
(defun ht064-r-one (ctx) (nth 2 ctx))
(defun ht064-r-add (ctx) (nth 3 ctx))
(defun ht064-r-mul (ctx) (nth 4 ctx))
(defun ht064-r-neg (ctx) (nth 5 ctx))
(defun ht064-r-inv (ctx) (nth 6 ctx))
(defun ht064-r-lt (ctx) (nth 7 ctx))
(defun ht064-r-sup (ctx) (nth 8 ctx))

(defun ht064-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (ht064-real-field-p
    (ht064-r-carrier ctx)
    (ht064-r-zero ctx)
    (ht064-r-one ctx)
    (ht064-r-add ctx)
    (ht064-r-mul ctx)
    (ht064-r-neg ctx)
    (ht064-r-inv ctx)
    (ht064-r-lt ctx)
    (ht064-r-sup ctx))))

(defun ht064-r-add-value (ctx left right)
  (ht064-binary-value (ht064-r-add ctx) left right))

(defun ht064-r-neg-value (ctx value)
  (ht064-unary-value (ht064-r-neg ctx) value))

(defun ht064-r-sub-value (ctx left right)
  (ht064-r-add-value
   ctx left (ht064-r-neg-value ctx right)))

(defun ht064-r-mul-value (ctx left right)
  (ht064-binary-value (ht064-r-mul ctx) left right))

(defun ht064-r-inv-value (ctx value)
  (ht064-unary-value (ht064-r-inv ctx) value))

(defun ht064-r-div-value (ctx numerator denominator)
  (ht064-r-mul-value
   ctx numerator (ht064-r-inv-value ctx denominator)))

(defun ht064-r-lt-p (ctx left right)
  (if (ht064-binary-value
       (ht064-r-lt ctx) left right)
      t nil))

(defun ht064-r-le-p (ctx left right)
  (not (ht064-r-lt-p ctx right left)))

(defun ht064-r-abs-value (ctx value)
  (if (ht064-r-lt-p ctx value (ht064-r-zero ctx))
      (ht064-r-neg-value ctx value)
    value))

(defun ht064-positive-real-p (ctx value)
  (and
   (ht064-member-p (ht064-r-carrier ctx) value)
   (ht064-r-lt-p ctx (ht064-r-zero ctx) value)))

;; Closed and open intervals.

(defun ht064-ioo-set (ctx a b)
  (list
   'lambda '(x)
   (ht064-and-terms
    (list
     (ht064-static-apply-term
      (ht064-r-carrier ctx) '(x))
     (ht064-static-apply-term
      (ht064-r-lt ctx)
      (list (ht064-quoted a) 'x))
     (ht064-static-apply-term
      (ht064-r-lt ctx)
      (list 'x (ht064-quoted b)))))))

(defun ht064-icc-set (ctx a b)
  (list
   'lambda '(x)
   (ht064-and-terms
    (list
     (ht064-static-apply-term
      (ht064-r-carrier ctx) '(x))
     (ht064-not-term
      (ht064-static-apply-term
       (ht064-r-lt ctx)
       (list 'x (ht064-quoted a))))
     (ht064-not-term
      (ht064-static-apply-term
       (ht064-r-lt ctx)
       (list (ht064-quoted b) 'x)))))))

;; Continuity within the closed interval [a,b].

(defun ht064-continuity-point-function
    (ctx function a b x epsilon radius)
  (list
   'lambda '(y)
   (ht064-implies-term
    (ht064-and-terms
     (list
      (ht064-static-apply-term
       (ht064-icc-set ctx a b) '(y))
      (list 'ht064-r-lt-p
            (ht064-quoted ctx)
            (list 'ht064-r-abs-value
                  (ht064-quoted ctx)
                  (list 'ht064-r-sub-value
                        (ht064-quoted ctx)
                        'y
                        (ht064-quoted x)))
            (ht064-quoted radius))))
    (list 'ht064-r-lt-p
          (ht064-quoted ctx)
          (list 'ht064-r-abs-value
                (ht064-quoted ctx)
                (list 'ht064-r-sub-value
                      (ht064-quoted ctx)
                      (ht064-static-apply-term function '(y))
                      (ht064-static-apply-term
                       function
                       (list (ht064-quoted x)))))
          (ht064-quoted epsilon)))))

(defun ht064-continuity-radius-function
    (ctx function a b x epsilon)
  (list
   'lambda '(radius)
   (ht064-and-terms
    (list
     (list 'ht064-positive-real-p
           (ht064-quoted ctx) 'radius)
     (list 'ht064-universal-p
           (list 'ht064-continuity-point-function
                 (ht064-quoted ctx)
                 (ht064-quoted function)
                 (ht064-quoted a)
                 (ht064-quoted b)
                 (ht064-quoted x)
                 (ht064-quoted epsilon)
                 'radius)
           (ht064-quoted '(y)))))))

(defun ht064-continuity-epsilon-function
    (ctx function a b x)
  (list
   'lambda '(epsilon)
   (ht064-implies-term
    (list 'ht064-positive-real-p
          (ht064-quoted ctx) 'epsilon)
    (list 'ht064-exists-p
          (list 'ht064-continuity-radius-function
                (ht064-quoted ctx)
                (ht064-quoted function)
                (ht064-quoted a)
                (ht064-quoted b)
                (ht064-quoted x)
                'epsilon)
          (ht064-quoted '(radius))))))

(defun ht064-continuous-on-row-function
    (ctx function a b)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-static-apply-term
     (ht064-icc-set ctx a b) '(x))
    (list 'ht064-universal-p
          (list 'ht064-continuity-epsilon-function
                (ht064-quoted ctx)
                (ht064-quoted function)
                (ht064-quoted a)
                (ht064-quoted b)
                'x)
          (ht064-quoted '(epsilon))))))

(defun ht064-continuous-on-icc-p
    (ctx function a b)
  (ht064-universal-p
   (ht064-continuous-on-row-function
    ctx function a b)
   '(x)))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun ht064-derivative-point-function
    (ctx function derivative x epsilon radius)
  (list
   'lambda '(y)
   (ht064-implies-term
    (ht064-and-terms
     (list
      (ht064-static-apply-term
       (ht064-r-carrier ctx) '(y))
      (list 'ht064-r-lt-p
            (ht064-quoted ctx)
            (list 'ht064-r-abs-value
                  (ht064-quoted ctx)
                  (list 'ht064-r-sub-value
                        (ht064-quoted ctx)
                        'y
                        (ht064-quoted x)))
            (ht064-quoted radius))))
    (list 'ht064-r-le-p
          (ht064-quoted ctx)
          (list 'ht064-r-abs-value
                (ht064-quoted ctx)
                (list 'ht064-r-sub-value
                      (ht064-quoted ctx)
                      (list 'ht064-r-sub-value
                            (ht064-quoted ctx)
                            (ht064-static-apply-term function '(y))
                            (ht064-static-apply-term
                             function
                             (list (ht064-quoted x))))
                      (list 'ht064-r-mul-value
                            (ht064-quoted ctx)
                            (ht064-quoted derivative)
                            (list 'ht064-r-sub-value
                                  (ht064-quoted ctx)
                                  'y
                                  (ht064-quoted x)))))
          (list 'ht064-r-mul-value
                (ht064-quoted ctx)
                (ht064-quoted epsilon)
                (list 'ht064-r-abs-value
                      (ht064-quoted ctx)
                      (list 'ht064-r-sub-value
                            (ht064-quoted ctx)
                            'y
                            (ht064-quoted x))))))))

(defun ht064-derivative-radius-function
    (ctx function derivative x epsilon)
  (list
   'lambda '(radius)
   (ht064-and-terms
    (list
     (list 'ht064-positive-real-p
           (ht064-quoted ctx) 'radius)
     (list 'ht064-universal-p
           (list 'ht064-derivative-point-function
                 (ht064-quoted ctx)
                 (ht064-quoted function)
                 (ht064-quoted derivative)
                 (ht064-quoted x)
                 (ht064-quoted epsilon)
                 'radius)
           (ht064-quoted '(y)))))))

(defun ht064-derivative-epsilon-function
    (ctx function derivative x)
  (list
   'lambda '(epsilon)
   (ht064-implies-term
    (list 'ht064-positive-real-p
          (ht064-quoted ctx) 'epsilon)
    (list 'ht064-exists-p
          (list 'ht064-derivative-radius-function
                (ht064-quoted ctx)
                (ht064-quoted function)
                (ht064-quoted derivative)
                (ht064-quoted x)
                'epsilon)
          (ht064-quoted '(radius))))))

(defun ht064-has-derivative-at-p
    (ctx function derivative x)
  (and
   (ht064-member-p (ht064-r-carrier ctx) derivative)
   (ht064-member-p (ht064-r-carrier ctx) x)
   (ht064-universal-p
    (ht064-derivative-epsilon-function
     ctx function derivative x)
    '(epsilon))))

(defun ht064-derivative-witness-function
    (ctx function x)
  (list
   'lambda '(derivative)
   (list 'ht064-has-derivative-at-p
         (ht064-quoted ctx)
         (ht064-quoted function)
         'derivative
         (ht064-quoted x))))

(defun ht064-differentiable-at-p
    (ctx function x)
  (ht064-exists-p
   (ht064-derivative-witness-function
    ctx function x)
   '(derivative)))

(defun ht064-differentiable-on-row-function
    (ctx function a b)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-static-apply-term
     (ht064-ioo-set ctx a b) '(x))
    (list 'ht064-differentiable-at-p
          (ht064-quoted ctx)
          (ht064-quoted function)
          'x))))

(defun ht064-differentiable-on-ioo-p
    (ctx function a b)
  (ht064-universal-p
   (ht064-differentiable-on-row-function
    ctx function a b)
   '(x)))

;; Two-sided punctured limits at a finite point.

(defun ht064-limit-point-function
    (ctx function c limit epsilon radius)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-and-terms
     (list
      (ht064-static-apply-term
       (ht064-r-carrier ctx) '(x))
      (list 'ht064-r-lt-p
            (ht064-quoted ctx)
            (ht064-quoted (ht064-r-zero ctx))
            (list 'ht064-r-abs-value
                  (ht064-quoted ctx)
                  (list 'ht064-r-sub-value
                        (ht064-quoted ctx)
                        'x
                        (ht064-quoted c))))
      (list 'ht064-r-lt-p
            (ht064-quoted ctx)
            (list 'ht064-r-abs-value
                  (ht064-quoted ctx)
                  (list 'ht064-r-sub-value
                        (ht064-quoted ctx)
                        'x
                        (ht064-quoted c)))
            (ht064-quoted radius))))
    (list 'ht064-r-lt-p
          (ht064-quoted ctx)
          (list 'ht064-r-abs-value
                (ht064-quoted ctx)
                (list 'ht064-r-sub-value
                      (ht064-quoted ctx)
                      (ht064-static-apply-term function '(x))
                      (ht064-quoted limit)))
          (ht064-quoted epsilon)))))

(defun ht064-limit-radius-function
    (ctx function c limit epsilon)
  (list
   'lambda '(radius)
   (ht064-and-terms
    (list
     (list 'ht064-positive-real-p
           (ht064-quoted ctx) 'radius)
     (list 'ht064-universal-p
           (list 'ht064-limit-point-function
                 (ht064-quoted ctx)
                 (ht064-quoted function)
                 (ht064-quoted c)
                 (ht064-quoted limit)
                 (ht064-quoted epsilon)
                 'radius)
           (ht064-quoted '(x)))))))

(defun ht064-limit-epsilon-function
    (ctx function c limit)
  (list
   'lambda '(epsilon)
   (ht064-implies-term
    (list 'ht064-positive-real-p
          (ht064-quoted ctx) 'epsilon)
    (list 'ht064-exists-p
          (list 'ht064-limit-radius-function
                (ht064-quoted ctx)
                (ht064-quoted function)
                (ht064-quoted c)
                (ht064-quoted limit)
                'epsilon)
          (ht064-quoted '(radius))))))

(defun ht064-tends-to-at-p
    (ctx function c limit)
  (and
   (tamep-functionp function)
   (ht064-member-p (ht064-r-carrier ctx) c)
   (ht064-member-p (ht064-r-carrier ctx) limit)
   (ht064-universal-p
    (ht064-limit-epsilon-function
     ctx function c limit)
    '(epsilon))))

;; The supplied derivative functions agree with the derivatives of f and g
;; throughout a fixed punctured neighborhood, and g' is nonzero there.

(defun ht064-derivative-neighborhood-row-function
    (ctx f g f-prime g-prime c d)
  (list
   'lambda '(x)
   (ht064-implies-term
    (ht064-and-terms
     (list
      (ht064-static-apply-term
       (ht064-r-carrier ctx) '(x))
      (list 'ht064-r-lt-p
            (ht064-quoted ctx)
            (ht064-quoted (ht064-r-zero ctx))
            (list 'ht064-r-abs-value
                  (ht064-quoted ctx)
                  (list 'ht064-r-sub-value
                        (ht064-quoted ctx)
                        'x
                        (ht064-quoted c))))
      (list 'ht064-r-lt-p
            (ht064-quoted ctx)
            (list 'ht064-r-abs-value
                  (ht064-quoted ctx)
                  (list 'ht064-r-sub-value
                        (ht064-quoted ctx)
                        'x
                        (ht064-quoted c)))
            (ht064-quoted d))))
    (ht064-and-terms
     (list
      (list 'ht064-has-derivative-at-p
            (ht064-quoted ctx)
            (ht064-quoted f)
            (ht064-static-apply-term f-prime '(x))
            'x)
      (list 'ht064-has-derivative-at-p
            (ht064-quoted ctx)
            (ht064-quoted g)
            (ht064-static-apply-term g-prime '(x))
            'x)
      (ht064-not-term
       (list 'equal
             (ht064-static-apply-term g-prime '(x))
             (ht064-quoted (ht064-r-zero ctx)))))))))

(defun ht064-derivative-neighborhood-p
    (ctx f g f-prime g-prime c d)
  (ht064-universal-p
   (ht064-derivative-neighborhood-row-function
    ctx f g f-prime g-prime c d)
   '(x)))

(defun ht064-quotient-function
    (ctx numerator denominator)
  (list
   'lambda '(x)
   (list 'ht064-r-div-value
         (ht064-quoted ctx)
         (ht064-static-apply-term numerator '(x))
         (ht064-static-apply-term denominator '(x)))))

;; HOL Light's LHOPITAL theorem: the full two-sided 0/0 form.
(defun hundred-theorems-064-lhopitals-rule-statement
    (ctx f g f-prime g-prime c limit d)
  (implies
   (and
    (ht064-context-p ctx)
    (ht064-member-p (ht064-r-carrier ctx) c)
    (ht064-member-p (ht064-r-carrier ctx) limit)
    (ht064-positive-real-p ctx d)
    (ht064-real-function-p (ht064-r-carrier ctx) f)
    (ht064-real-function-p (ht064-r-carrier ctx) g)
    (ht064-real-function-p (ht064-r-carrier ctx) f-prime)
    (ht064-real-function-p (ht064-r-carrier ctx) g-prime)
    (ht064-derivative-neighborhood-p
     ctx f g f-prime g-prime c d)
    (ht064-tends-to-at-p
     ctx f c (ht064-r-zero ctx))
    (ht064-tends-to-at-p
     ctx g c (ht064-r-zero ctx))
    (ht064-tends-to-at-p
     ctx
     (ht064-quotient-function ctx f-prime g-prime)
     c
     limit))
   (ht064-tends-to-at-p
    ctx
    (ht064-quotient-function ctx f g)
    c
    limit)))

(value-triple :itpeval-statement-checked)
:q
