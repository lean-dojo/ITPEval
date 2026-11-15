;; Statement-only formalization of the PutnamBench corpus artifact
;; putnam_1963_a3: the integral formula for the zero-initial-value solution of
;; the Euler differential equation delta(delta-1)...(delta-n+1)y=f on [1,+oo).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary sets and functions are tame APPLY$ function objects. FN-EQUAL
;; supplies unbounded universal quantification, and inequality with a
;; constant-false function supplies internal existential quantification.
;; The scalar context is a Dedekind-complete ordered field, hence a
;; presentation of the real field. Continuity, derivatives, and the Riemann
;; integral of the continuous kernel are expanded below. The derivative family
;; remains internally quantified, and APPLY$ functions are not finite tables.

(defun p63a3-quoted (object)
  (list 'quote object))

(defun p63a3-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (p63a3-term-list (cdr terms)))
    (p63a3-quoted nil)))

(defun p63a3-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (p63a3-term-list arguments)))

(defun p63a3-static-apply-term (function arguments)
  (p63a3-apply-term
   (p63a3-quoted function)
   arguments))

(defun p63a3-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p63a3-and-terms (cdr terms))
            (p63a3-quoted nil))
    (p63a3-quoted t)))

(defun p63a3-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p63a3-quoted t)
            (p63a3-or-terms (cdr terms)))
    (p63a3-quoted nil)))

(defun p63a3-not-term (term)
  (list 'if term
        (p63a3-quoted nil)
        (p63a3-quoted t)))

(defun p63a3-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (p63a3-quoted t)))

(defun p63a3-true-function (formals)
  (list 'lambda formals (p63a3-quoted t)))

(defun p63a3-false-function (formals)
  (list 'lambda formals (p63a3-quoted nil)))

(defun p63a3-universal-p (function formals)
  (let ((always-true (p63a3-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun p63a3-exists-p (function formals)
  (let ((always-false (p63a3-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun p63a3-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun p63a3-unary-value (function object)
  (apply$ function (list object)))

(defun p63a3-binary-value (function left right)
  (apply$ function (list left right)))

;; Arbitrary real-valued functions and arbitrary subsets of the real carrier.

(defun p63a3-function-values-function (carrier function)
  (list
   'lambda '(x)
   (p63a3-implies-term
    (p63a3-static-apply-term carrier '(x))
    (p63a3-static-apply-term
     carrier
     (list (p63a3-static-apply-term function '(x)))))))

(defun p63a3-real-function-p (carrier function)
  (and
   (tamep-functionp function)
   (p63a3-universal-p
    (p63a3-function-values-function carrier function)
    '(x))))

(defun p63a3-set-subset-carrier-function (carrier set)
  (list
   'lambda '(x)
   (p63a3-implies-term
    (p63a3-static-apply-term set '(x))
    (p63a3-static-apply-term carrier '(x)))))

(defun p63a3-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (p63a3-universal-p
    (p63a3-set-subset-carrier-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun p63a3-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (p63a3-static-apply-term add '(x y)))
         (yz-add (p63a3-static-apply-term add '(y z)))
         (xy-mul (p63a3-static-apply-term multiply '(x y)))
         (yz-mul (p63a3-static-apply-term multiply '(y z)))
         (neg-x (p63a3-static-apply-term negate '(x)))
         (inv-x (p63a3-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (p63a3-implies-term
      (p63a3-and-terms
       (list
        (p63a3-static-apply-term carrier '(x))
        (p63a3-static-apply-term carrier '(y))
        (p63a3-static-apply-term carrier '(z))))
      (p63a3-and-terms
       (list
        (p63a3-static-apply-term carrier (list xy-add))
        (p63a3-static-apply-term carrier (list xy-mul))
        (p63a3-static-apply-term carrier (list neg-x))
        (p63a3-static-apply-term carrier (list inv-x))
        (list 'equal
              (p63a3-static-apply-term add (list xy-add 'z))
              (p63a3-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (p63a3-static-apply-term add '(y x)))
        (list 'equal
              (p63a3-static-apply-term
               add (list 'x (p63a3-quoted zero)))
              'x)
        (list 'equal
              (p63a3-static-apply-term add (list 'x neg-x))
              (p63a3-quoted zero))
        (list 'equal
              (p63a3-static-apply-term multiply (list xy-mul 'z))
              (p63a3-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (p63a3-static-apply-term multiply '(y x)))
        (list 'equal
              (p63a3-static-apply-term
               multiply (list 'x (p63a3-quoted one)))
              'x)
        (p63a3-implies-term
         (list 'equal 'x (p63a3-quoted zero))
         (list 'equal inv-x (p63a3-quoted zero)))
        (p63a3-implies-term
         (p63a3-not-term
          (list 'equal 'x (p63a3-quoted zero)))
         (list 'equal
               (p63a3-static-apply-term
                multiply (list 'x inv-x))
               (p63a3-quoted one)))
        (list 'equal
              (p63a3-static-apply-term multiply (list 'x yz-add))
              (p63a3-static-apply-term
               add
               (list
                (p63a3-static-apply-term multiply '(x y))
                (p63a3-static-apply-term multiply '(x z)))))))))))

(defun p63a3-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (p63a3-static-apply-term less '(x y)))
        (yx (p63a3-static-apply-term less '(y x)))
        (yz (p63a3-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (p63a3-implies-term
      (p63a3-and-terms
       (list
        (p63a3-static-apply-term carrier '(x))
        (p63a3-static-apply-term carrier '(y))
        (p63a3-static-apply-term carrier '(z))))
      (p63a3-and-terms
       (list
        (p63a3-not-term
         (p63a3-static-apply-term less '(x x)))
        (p63a3-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (p63a3-implies-term
         (p63a3-and-terms (list xy yz))
         (p63a3-static-apply-term less '(x z)))
        (p63a3-implies-term
         xy
         (p63a3-static-apply-term
          less
          (list
           (p63a3-static-apply-term add '(x z))
           (p63a3-static-apply-term add '(y z)))))
        (p63a3-implies-term
         (p63a3-and-terms
          (list
           (p63a3-static-apply-term
            less (list (p63a3-quoted zero) 'x))
           (p63a3-static-apply-term
            less (list (p63a3-quoted zero) 'y))))
         (p63a3-static-apply-term
          less
          (list
           (p63a3-quoted zero)
           (p63a3-static-apply-term multiply '(x y)))))))))))

(defun p63a3-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (p63a3-static-apply-term carrier '(x))
      (p63a3-static-apply-term set '(x))))
    (p63a3-not-term
     (p63a3-static-apply-term
      less (list (p63a3-quoted upper) 'x))))))

(defun p63a3-upper-bound-p
    (carrier less set upper)
  (and
   (p63a3-member-p carrier upper)
   (p63a3-valid-set-p carrier set)
   (p63a3-universal-p
    (p63a3-upper-bound-function carrier less set upper)
    '(x))))

(defun p63a3-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (p63a3-and-terms
    (list
     (p63a3-static-apply-term carrier '(x))
     (p63a3-static-apply-term set '(x))))))

(defun p63a3-set-nonempty-p (carrier set)
  (and
   (p63a3-valid-set-p carrier set)
   (p63a3-exists-p
    (p63a3-set-nonempty-function carrier set)
    '(x))))

(defun p63a3-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'p63a3-upper-bound-p
         (p63a3-quoted carrier)
         (p63a3-quoted less)
         (p63a3-quoted set)
         'upper)))

(defun p63a3-bounded-above-p (carrier less set)
  (p63a3-exists-p
   (p63a3-bounded-above-function carrier less set)
   '(upper)))

(defun p63a3-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (p63a3-implies-term
    (list 'p63a3-upper-bound-p
          (p63a3-quoted carrier)
          (p63a3-quoted less)
          (p63a3-quoted set)
          'upper)
    (p63a3-not-term
     (p63a3-static-apply-term
      less (list 'upper (p63a3-quoted supremum)))))))

(defun p63a3-least-upper-bound-p
    (carrier less set supremum)
  (and
   (p63a3-upper-bound-p carrier less set supremum)
   (p63a3-universal-p
    (p63a3-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun p63a3-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (list 'p63a3-valid-set-p
            (p63a3-quoted carrier) 'set)
      (list 'p63a3-set-nonempty-p
            (p63a3-quoted carrier) 'set)
      (list 'p63a3-bounded-above-p
            (p63a3-quoted carrier)
            (p63a3-quoted less)
            'set)))
    (list 'p63a3-least-upper-bound-p
          (p63a3-quoted carrier)
          (p63a3-quoted less)
          'set
          (p63a3-static-apply-term
           supremum-operation '(set))))))

(defun p63a3-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (p63a3-member-p carrier zero)
   (p63a3-member-p carrier one)
   (not (equal zero one))
   (p63a3-universal-p
    (p63a3-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (p63a3-universal-p
    (p63a3-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (p63a3-universal-p
    (p63a3-completeness-function
     carrier less supremum)
    '(set))
   (p63a3-binary-value less zero one)))

;; Real-field context and arithmetic.

(defun p63a3-r-carrier (ctx) (nth 0 ctx))
(defun p63a3-r-zero (ctx) (nth 1 ctx))
(defun p63a3-r-one (ctx) (nth 2 ctx))
(defun p63a3-r-add (ctx) (nth 3 ctx))
(defun p63a3-r-mul (ctx) (nth 4 ctx))
(defun p63a3-r-neg (ctx) (nth 5 ctx))
(defun p63a3-r-inv (ctx) (nth 6 ctx))
(defun p63a3-r-lt (ctx) (nth 7 ctx))
(defun p63a3-r-sup (ctx) (nth 8 ctx))

(defun p63a3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (p63a3-real-field-p
    (p63a3-r-carrier ctx)
    (p63a3-r-zero ctx)
    (p63a3-r-one ctx)
    (p63a3-r-add ctx)
    (p63a3-r-mul ctx)
    (p63a3-r-neg ctx)
    (p63a3-r-inv ctx)
    (p63a3-r-lt ctx)
    (p63a3-r-sup ctx))))

(defun p63a3-r-add-value (ctx left right)
  (p63a3-binary-value (p63a3-r-add ctx) left right))

(defun p63a3-r-neg-value (ctx value)
  (p63a3-unary-value (p63a3-r-neg ctx) value))

(defun p63a3-r-sub-value (ctx left right)
  (p63a3-r-add-value
   ctx left (p63a3-r-neg-value ctx right)))

(defun p63a3-r-mul-value (ctx left right)
  (p63a3-binary-value (p63a3-r-mul ctx) left right))

(defun p63a3-r-inv-value (ctx value)
  (p63a3-unary-value (p63a3-r-inv ctx) value))

(defun p63a3-r-div-value (ctx numerator denominator)
  (p63a3-r-mul-value
   ctx numerator (p63a3-r-inv-value ctx denominator)))

(defun p63a3-r-lt-p (ctx left right)
  (if (p63a3-binary-value
       (p63a3-r-lt ctx) left right)
      t nil))

(defun p63a3-r-le-p (ctx left right)
  (not (p63a3-r-lt-p ctx right left)))

(defun p63a3-r-abs-value (ctx value)
  (if (p63a3-r-lt-p ctx value (p63a3-r-zero ctx))
      (p63a3-r-neg-value ctx value)
    value))

(defun p63a3-positive-real-p (ctx value)
  (and
   (p63a3-member-p (p63a3-r-carrier ctx) value)
   (p63a3-r-lt-p ctx (p63a3-r-zero ctx) value)))

;; Natural-number arithmetic interpreted in the abstract real field.

(defun p63a3-r-nat-value (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p63a3-r-zero ctx)
    (p63a3-r-add-value
     ctx
     (p63a3-r-one ctx)
     (p63a3-r-nat-value ctx (- n 1)))))

(defun p63a3-r-power-value (ctx base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p63a3-r-one ctx)
    (p63a3-r-mul-value
     ctx
     base
     (p63a3-r-power-value ctx base (- exponent 1)))))

(defun p63a3-r-factorial-value (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p63a3-r-one ctx)
    (p63a3-r-mul-value
     ctx
     (p63a3-r-nat-value ctx n)
     (p63a3-r-factorial-value ctx (- n 1)))))

;; Unordered closed and open intervals with endpoints x0 and x.

(defun p63a3-lower-endpoint (ctx x0 x)
  (if (p63a3-r-lt-p ctx x0 x) x0 x))

(defun p63a3-upper-endpoint (ctx x0 x)
  (if (p63a3-r-lt-p ctx x0 x) x x0))

(defun p63a3-uioo-set (ctx x0 x)
  (let ((lower (p63a3-lower-endpoint ctx x0 x))
        (upper (p63a3-upper-endpoint ctx x0 x)))
    (list
     'lambda '(point)
     (p63a3-and-terms
      (list
       (p63a3-static-apply-term
        (p63a3-r-carrier ctx) '(point))
       (p63a3-static-apply-term
        (p63a3-r-lt ctx)
        (list (p63a3-quoted lower) 'point))
       (p63a3-static-apply-term
        (p63a3-r-lt ctx)
        (list 'point (p63a3-quoted upper))))))))

(defun p63a3-uicc-set (ctx x0 x)
  (let ((lower (p63a3-lower-endpoint ctx x0 x))
        (upper (p63a3-upper-endpoint ctx x0 x)))
    (list
     'lambda '(point)
     (p63a3-and-terms
      (list
       (p63a3-static-apply-term
        (p63a3-r-carrier ctx) '(point))
       (p63a3-not-term
        (p63a3-static-apply-term
         (p63a3-r-lt ctx)
         (list 'point (p63a3-quoted lower))))
       (p63a3-not-term
        (p63a3-static-apply-term
         (p63a3-r-lt ctx)
         (list (p63a3-quoted upper) 'point))))))))

;; A derivative family maps each natural order to a real-valued function.

(defun p63a3-derivative-function (derivatives order)
  (p63a3-unary-value derivatives order))

(defun p63a3-derivative-value (derivatives order point)
  (p63a3-unary-value
   (p63a3-derivative-function derivatives order)
   point))

(defun p63a3-derivative-family-row-function
    (ctx derivatives maximum-order)
  (list
   'lambda '(order)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (list 'natp 'order)
      (list '<= 'order (p63a3-quoted maximum-order))))
    (list 'p63a3-real-function-p
          (p63a3-quoted (p63a3-r-carrier ctx))
          (p63a3-static-apply-term derivatives '(order))))))

(defun p63a3-derivative-family-p
    (ctx derivatives maximum-order)
  (and
   (tamep-functionp derivatives)
   (p63a3-universal-p
    (p63a3-derivative-family-row-function
     ctx derivatives maximum-order)
    '(order))))

;; Continuity within the unordered closed interval.

(defun p63a3-continuity-point-function
    (ctx function interval point epsilon radius)
  (list
   'lambda '(nearby)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (p63a3-static-apply-term interval '(nearby))
      (list 'p63a3-r-lt-p
            (p63a3-quoted ctx)
            (list 'p63a3-r-abs-value
                  (p63a3-quoted ctx)
                  (list 'p63a3-r-sub-value
                        (p63a3-quoted ctx)
                        'nearby
                        (p63a3-quoted point)))
            (p63a3-quoted radius))))
    (list 'p63a3-r-lt-p
          (p63a3-quoted ctx)
          (list 'p63a3-r-abs-value
                (p63a3-quoted ctx)
                (list 'p63a3-r-sub-value
                      (p63a3-quoted ctx)
                      (p63a3-static-apply-term function '(nearby))
                      (p63a3-static-apply-term
                       function
                       (list (p63a3-quoted point)))))
          (p63a3-quoted epsilon)))))

(defun p63a3-continuity-radius-function
    (ctx function interval point epsilon)
  (list
   'lambda '(radius)
   (p63a3-and-terms
    (list
     (list 'p63a3-positive-real-p
           (p63a3-quoted ctx) 'radius)
     (list 'p63a3-universal-p
           (list 'p63a3-continuity-point-function
                 (p63a3-quoted ctx)
                 (p63a3-quoted function)
                 (p63a3-quoted interval)
                 (p63a3-quoted point)
                 (p63a3-quoted epsilon)
                 'radius)
           (p63a3-quoted '(nearby)))))))

(defun p63a3-continuity-epsilon-function
    (ctx function interval point)
  (list
   'lambda '(epsilon)
   (p63a3-implies-term
    (list 'p63a3-positive-real-p
          (p63a3-quoted ctx) 'epsilon)
    (list 'p63a3-exists-p
          (list 'p63a3-continuity-radius-function
                (p63a3-quoted ctx)
                (p63a3-quoted function)
                (p63a3-quoted interval)
                (p63a3-quoted point)
                'epsilon)
          (p63a3-quoted '(radius))))))

(defun p63a3-continuous-within-at-p
    (ctx function interval point)
  (and
   (p63a3-member-p interval point)
   (p63a3-universal-p
    (p63a3-continuity-epsilon-function
     ctx function interval point)
    '(epsilon))))

(defun p63a3-continuous-on-row-function
    (ctx function interval)
  (list
   'lambda '(point)
   (p63a3-implies-term
    (p63a3-static-apply-term interval '(point))
    (list 'p63a3-continuous-within-at-p
          (p63a3-quoted ctx)
          (p63a3-quoted function)
          (p63a3-quoted interval)
          'point))))

(defun p63a3-continuous-on-p
    (ctx function interval)
  (p63a3-universal-p
   (p63a3-continuous-on-row-function
    ctx function interval)
   '(point)))

;; HasDerivWithinAt in epsilon-delta form, with nearby points restricted to
;; INTERVAL. Taking INTERVAL to be the whole carrier gives HasDerivAt.

(defun p63a3-derivative-point-function
    (ctx function derivative interval point epsilon radius)
  (list
   'lambda '(nearby)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (p63a3-static-apply-term interval '(nearby))
      (list 'p63a3-r-lt-p
            (p63a3-quoted ctx)
            (list 'p63a3-r-abs-value
                  (p63a3-quoted ctx)
                  (list 'p63a3-r-sub-value
                        (p63a3-quoted ctx)
                        'nearby
                        (p63a3-quoted point)))
            (p63a3-quoted radius))))
    (list 'p63a3-r-le-p
          (p63a3-quoted ctx)
          (list 'p63a3-r-abs-value
                (p63a3-quoted ctx)
                (list 'p63a3-r-sub-value
                      (p63a3-quoted ctx)
                      (list 'p63a3-r-sub-value
                            (p63a3-quoted ctx)
                            (p63a3-static-apply-term function '(nearby))
                            (p63a3-static-apply-term
                             function
                             (list (p63a3-quoted point))))
                      (list 'p63a3-r-mul-value
                            (p63a3-quoted ctx)
                            (p63a3-quoted derivative)
                            (list 'p63a3-r-sub-value
                                  (p63a3-quoted ctx)
                                  'nearby
                                  (p63a3-quoted point)))))
          (list 'p63a3-r-mul-value
                (p63a3-quoted ctx)
                (p63a3-quoted epsilon)
                (list 'p63a3-r-abs-value
                      (p63a3-quoted ctx)
                      (list 'p63a3-r-sub-value
                            (p63a3-quoted ctx)
                            'nearby
                            (p63a3-quoted point))))))))

(defun p63a3-derivative-radius-function
    (ctx function derivative interval point epsilon)
  (list
   'lambda '(radius)
   (p63a3-and-terms
    (list
     (list 'p63a3-positive-real-p
           (p63a3-quoted ctx) 'radius)
     (list 'p63a3-universal-p
           (list 'p63a3-derivative-point-function
                 (p63a3-quoted ctx)
                 (p63a3-quoted function)
                 (p63a3-quoted derivative)
                 (p63a3-quoted interval)
                 (p63a3-quoted point)
                 (p63a3-quoted epsilon)
                 'radius)
           (p63a3-quoted '(nearby)))))))

(defun p63a3-derivative-epsilon-function
    (ctx function derivative interval point)
  (list
   'lambda '(epsilon)
   (p63a3-implies-term
    (list 'p63a3-positive-real-p
          (p63a3-quoted ctx) 'epsilon)
    (list 'p63a3-exists-p
          (list 'p63a3-derivative-radius-function
                (p63a3-quoted ctx)
                (p63a3-quoted function)
                (p63a3-quoted derivative)
                (p63a3-quoted interval)
                (p63a3-quoted point)
                'epsilon)
          (p63a3-quoted '(radius))))))

(defun p63a3-has-derivative-within-at-p
    (ctx function derivative interval point)
  (and
   (p63a3-member-p (p63a3-r-carrier ctx) derivative)
   (p63a3-member-p interval point)
   (p63a3-universal-p
    (p63a3-derivative-epsilon-function
     ctx function derivative interval point)
    '(epsilon))))

;; The explicit derivative family is definitionally tied to f: order zero is
;; f, orders below n differentiate within the closed interval, all orders
;; through n are continuous there, and order n+1 differentiates order n on
;; the open interval.

(defun p63a3-contdiff-order-row-function
    (ctx derivatives order interval)
  (list
   'lambda '(index)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (list 'natp 'index)
      (list '<= 'index (p63a3-quoted order))))
    (list 'p63a3-continuous-on-p
          (p63a3-quoted ctx)
          (p63a3-static-apply-term derivatives '(index))
          (p63a3-quoted interval)))))

(defun p63a3-derivative-chain-point-function
    (ctx derivatives interval index)
  (let ((function-term
         (p63a3-derivative-function derivatives index))
        (next-function-term
         (p63a3-derivative-function derivatives (+ 1 index))))
    (list
     'lambda '(point)
     (p63a3-implies-term
      (p63a3-static-apply-term interval '(point))
      (list 'p63a3-has-derivative-within-at-p
            (p63a3-quoted ctx)
            (p63a3-quoted function-term)
            (p63a3-static-apply-term next-function-term '(point))
            (p63a3-quoted interval)
            'point)))))

(defun p63a3-derivative-chain-row-function
    (ctx derivatives order interval)
  (list
   'lambda '(index)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (list 'natp 'index)
      (list '< 'index (p63a3-quoted order))))
    (list 'p63a3-universal-p
          (list 'p63a3-derivative-chain-point-function
                (p63a3-quoted ctx)
                (p63a3-quoted derivatives)
                (p63a3-quoted interval)
                'index)
          (p63a3-quoted '(point))))))

(defun p63a3-contdiff-through-p
    (ctx f derivatives order interval)
  (and
   (fn-equal
    (p63a3-derivative-function derivatives 0)
    f)
   (p63a3-universal-p
    (p63a3-contdiff-order-row-function
     ctx derivatives order interval)
    '(index))
   (p63a3-universal-p
    (p63a3-derivative-chain-row-function
     ctx derivatives order interval)
    '(index))))

(defun p63a3-next-derivative-row-function
    (ctx derivatives order closed-interval open-interval)
  (let ((nth-function
         (p63a3-derivative-function derivatives order))
        (next-function
         (p63a3-derivative-function derivatives (+ 1 order))))
    (list
     'lambda '(point)
     (p63a3-implies-term
      (p63a3-static-apply-term open-interval '(point))
      (list 'p63a3-has-derivative-within-at-p
            (p63a3-quoted ctx)
            (p63a3-quoted nth-function)
            (p63a3-static-apply-term next-function '(point))
            (p63a3-quoted closed-interval)
            'point)))))

(defun p63a3-next-derivative-on-interior-p
    (ctx derivatives order closed-interval open-interval)
  (p63a3-universal-p
   (p63a3-next-derivative-row-function
    ctx derivatives order closed-interval open-interval)
   '(point)))

;; The closed half-line [1,+oo), the whole real carrier, and open balls.

(defun p63a3-ici-set (ctx lower)
  (list
   'lambda '(point)
   (p63a3-and-terms
    (list
     (p63a3-static-apply-term
      (p63a3-r-carrier ctx) '(point))
     (p63a3-not-term
      (p63a3-static-apply-term
       (p63a3-r-lt ctx)
       (list 'point (p63a3-quoted lower))))))))

(defun p63a3-univ-set (ctx)
  (list
   'lambda '(point)
   (p63a3-static-apply-term
    (p63a3-r-carrier ctx) '(point))))

(defun p63a3-open-ball-set (ctx center radius)
  (list
   'lambda '(point)
   (p63a3-and-terms
    (list
     (p63a3-static-apply-term
      (p63a3-r-carrier ctx) '(point))
     (list 'p63a3-r-lt-p
           (p63a3-quoted ctx)
           (list 'p63a3-r-abs-value
                 (p63a3-quoted ctx)
                 (list 'p63a3-r-sub-value
                       (p63a3-quoted ctx)
                       'point
                       (p63a3-quoted center)))
           (p63a3-quoted radius))))))

;; ContDiffOn of order N on [1,+oo), together with ContDiffAt of order N at
;; 1. The latter is represented by an internally existential open radius.

(defun p63a3-halfline-regularity-p (ctx y derivatives n)
  (let ((halfline (p63a3-ici-set ctx (p63a3-r-one ctx))))
    (and
     (p63a3-derivative-family-p ctx derivatives n)
     (fn-equal (p63a3-derivative-function derivatives 0) y)
     (p63a3-contdiff-through-p
      ctx y derivatives n halfline))))

(defun p63a3-local-contdiff-radius-witness-p
    (ctx y derivatives n radius)
  (and
   (p63a3-positive-real-p ctx radius)
   (p63a3-contdiff-through-p
    ctx
    y
    derivatives
    n
    (p63a3-open-ball-set
     ctx (p63a3-r-one ctx) radius))))

(defun p63a3-local-contdiff-radius-function
    (ctx y derivatives n)
  (list
   'lambda '(radius)
   (list 'p63a3-local-contdiff-radius-witness-p
         (p63a3-quoted ctx)
         (p63a3-quoted y)
         (p63a3-quoted derivatives)
         (p63a3-quoted n)
         'radius)))

(defun p63a3-regularity-p (ctx y derivatives n)
  (and
   (p63a3-halfline-regularity-p ctx y derivatives n)
   (p63a3-exists-p
    (p63a3-local-contdiff-radius-function
     ctx y derivatives n)
    '(radius))))

(defun p63a3-regularity-family-function (ctx y n)
  (list
   'lambda '(derivatives)
   (list 'p63a3-regularity-p
         (p63a3-quoted ctx)
         (p63a3-quoted y)
         'derivatives
         (p63a3-quoted n))))

;; The recursive operator from the formal sources satisfies
;; P_n(y)(x) = x^n y^(n)(x). This falling-Euler identity removes only the
;; definitional higher-order parameter P and leaves the same equation.

(defun p63a3-initial-conditions-row-function
    (ctx derivatives n)
  (list
   'lambda '(index)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (list 'natp 'index)
      (list '< 'index (p63a3-quoted n))))
    (list 'equal
          (p63a3-static-apply-term
           (p63a3-derivative-function derivatives 'index)
           (list (p63a3-quoted (p63a3-r-one ctx))))
          (p63a3-quoted (p63a3-r-zero ctx))))))

(defun p63a3-initial-conditions-p
    (ctx derivatives n)
  (p63a3-universal-p
   (p63a3-initial-conditions-row-function
    ctx derivatives n)
   '(index)))

(defun p63a3-equation-row-function
    (ctx f derivatives n)
  (let ((halfline
         (p63a3-ici-set ctx (p63a3-r-one ctx)))
        (nth-derivative
         (p63a3-derivative-function derivatives n)))
    (list
     'lambda '(x)
     (p63a3-implies-term
      (p63a3-static-apply-term halfline '(x))
      (list
       'equal
       (list 'p63a3-r-mul-value
             (p63a3-quoted ctx)
             (list 'p63a3-r-power-value
                   (p63a3-quoted ctx)
                   'x
                   (p63a3-quoted n))
             (p63a3-static-apply-term nth-derivative '(x)))
       (p63a3-static-apply-term f '(x)))))))

(defun p63a3-differential-equation-p
    (ctx f derivatives n)
  (p63a3-universal-p
   (p63a3-equation-row-function
    ctx f derivatives n)
   '(x)))

;; The kernel (x-t)^(n-1) f(t) / ((n-1)! t^n).

(defun p63a3-kernel-value (ctx f n x time)
  (let* ((degree (- n 1))
         (numerator
          (p63a3-r-mul-value
           ctx
           (p63a3-r-power-value
            ctx
            (p63a3-r-sub-value ctx x time)
            degree)
           (p63a3-unary-value f time)))
         (denominator
          (p63a3-r-mul-value
           ctx
           (p63a3-r-factorial-value ctx degree)
           (p63a3-r-power-value ctx time n))))
    (p63a3-r-div-value ctx numerator denominator)))

(defun p63a3-kernel-function (ctx f n x)
  (list
   'lambda '(time)
   (list 'p63a3-kernel-value
         (p63a3-quoted ctx)
         (p63a3-quoted f)
         (p63a3-quoted n)
         (p63a3-quoted x)
         'time)))

;; Tagged partitions and the epsilon definition of the Riemann integral. The
;; source kernel is continuous on every [1,x], so this equals the interval
;; integral used by Lean and Isabelle.

(defun p63a3-last-value (xs)
  (if (atom (cdr xs))
      (car xs)
    (p63a3-last-value (cdr xs))))

(defun p63a3-partition-elements-p (ctx xs)
  (if (atom xs)
      t
    (and
     (p63a3-member-p (p63a3-r-carrier ctx) (car xs))
     (p63a3-partition-elements-p ctx (cdr xs)))))

(defun p63a3-partition-increasing-p (ctx xs)
  (if (or (atom xs) (atom (cdr xs)))
      t
    (and
     (p63a3-r-lt-p ctx (car xs) (cadr xs))
     (p63a3-partition-increasing-p ctx (cdr xs)))))

(defun p63a3-partition-p (ctx lower upper partition)
  (and
   (true-listp partition)
   (consp partition)
   (consp (cdr partition))
   (equal (car partition) lower)
   (equal (p63a3-last-value partition) upper)
   (p63a3-partition-elements-p ctx partition)
   (p63a3-partition-increasing-p ctx partition)))

(defun p63a3-tags-p (ctx partition tags)
  (if (atom (cdr partition))
      (equal tags nil)
    (and
     (consp tags)
     (p63a3-member-p (p63a3-r-carrier ctx) (car tags))
     (p63a3-r-le-p ctx (car partition) (car tags))
     (p63a3-r-le-p ctx (car tags) (cadr partition))
     (p63a3-tags-p ctx (cdr partition) (cdr tags)))))

(defun p63a3-tagged-partition-p
    (ctx lower upper partition tags)
  (and
   (p63a3-partition-p ctx lower upper partition)
   (p63a3-tags-p ctx partition tags)))

(defun p63a3-r-max-value (ctx left right)
  (if (p63a3-r-lt-p ctx left right) right left))

(defun p63a3-partition-mesh (ctx partition)
  (if (or (atom partition) (atom (cdr partition)))
      (p63a3-r-zero ctx)
    (p63a3-r-max-value
     ctx
     (p63a3-r-sub-value ctx (cadr partition) (car partition))
     (p63a3-partition-mesh ctx (cdr partition)))))

(defun p63a3-riemann-sum (ctx integrand partition tags)
  (if (or (atom (cdr partition)) (atom tags))
      (p63a3-r-zero ctx)
    (p63a3-r-add-value
     ctx
     (p63a3-r-mul-value
      ctx
      (p63a3-unary-value integrand (car tags))
      (p63a3-r-sub-value
       ctx (cadr partition) (car partition)))
     (p63a3-riemann-sum
      ctx integrand (cdr partition) (cdr tags)))))

(defun p63a3-integral-partition-row-function
    (ctx integrand lower upper value epsilon delta)
  (list
   'lambda '(partition tags)
   (p63a3-implies-term
    (p63a3-and-terms
     (list
      (list 'p63a3-tagged-partition-p
            (p63a3-quoted ctx)
            (p63a3-quoted lower)
            (p63a3-quoted upper)
            'partition
            'tags)
      (list 'p63a3-r-lt-p
            (p63a3-quoted ctx)
            (list 'p63a3-partition-mesh
                  (p63a3-quoted ctx)
                  'partition)
            (p63a3-quoted delta))))
    (list 'p63a3-r-lt-p
          (p63a3-quoted ctx)
          (list 'p63a3-r-abs-value
                (p63a3-quoted ctx)
                (list 'p63a3-r-sub-value
                      (p63a3-quoted ctx)
                      (list 'p63a3-riemann-sum
                            (p63a3-quoted ctx)
                            (p63a3-quoted integrand)
                            'partition
                            'tags)
                      (p63a3-quoted value)))
          (p63a3-quoted epsilon)))))

(defun p63a3-integral-delta-witness-p
    (ctx integrand lower upper value epsilon delta)
  (and
   (p63a3-positive-real-p ctx delta)
   (p63a3-universal-p
    (p63a3-integral-partition-row-function
     ctx integrand lower upper value epsilon delta)
    '(partition tags))))

(defun p63a3-integral-delta-function
    (ctx integrand lower upper value epsilon)
  (list
   'lambda '(delta)
   (list 'p63a3-integral-delta-witness-p
         (p63a3-quoted ctx)
         (p63a3-quoted integrand)
         (p63a3-quoted lower)
         (p63a3-quoted upper)
         (p63a3-quoted value)
         (p63a3-quoted epsilon)
         'delta)))

(defun p63a3-integral-epsilon-row-function
    (ctx integrand lower upper value)
  (list
   'lambda '(epsilon)
   (p63a3-implies-term
    (list 'p63a3-positive-real-p
          (p63a3-quoted ctx) 'epsilon)
    (list 'p63a3-exists-p
          (list 'p63a3-integral-delta-function
                (p63a3-quoted ctx)
                (p63a3-quoted integrand)
                (p63a3-quoted lower)
                (p63a3-quoted upper)
                (p63a3-quoted value)
                'epsilon)
          (p63a3-quoted '(delta))))))

(defun p63a3-integral-value-p
    (ctx integrand lower upper value)
  (and
   (tamep-functionp integrand)
   (p63a3-member-p (p63a3-r-carrier ctx) lower)
   (p63a3-member-p (p63a3-r-carrier ctx) upper)
   (p63a3-member-p (p63a3-r-carrier ctx) value)
   (p63a3-r-le-p ctx lower upper)
   (if (equal lower upper)
       (equal value (p63a3-r-zero ctx))
     (p63a3-universal-p
      (p63a3-integral-epsilon-row-function
       ctx integrand lower upper value)
      '(epsilon)))))

(defun p63a3-integral-formula-row-function (ctx f y n)
  (let ((halfline
         (p63a3-ici-set ctx (p63a3-r-one ctx))))
    (list
     'lambda '(x)
     (p63a3-implies-term
      (p63a3-static-apply-term halfline '(x))
      (list 'p63a3-integral-value-p
            (p63a3-quoted ctx)
            (list 'p63a3-kernel-function
                  (p63a3-quoted ctx)
                  (p63a3-quoted f)
                  (p63a3-quoted n)
                  'x)
            (p63a3-quoted (p63a3-r-one ctx))
            'x
            (p63a3-static-apply-term y '(x)))))))

(defun p63a3-integral-formula-p (ctx f y n)
  (p63a3-universal-p
   (p63a3-integral-formula-row-function ctx f y n)
   '(x)))

(defun p63a3-equivalence-p (ctx f y derivatives n)
  (iff
   (and
    (p63a3-initial-conditions-p ctx derivatives n)
    (p63a3-differential-equation-p
     ctx f derivatives n))
   (p63a3-integral-formula-p ctx f y n)))

(defun p63a3-equivalence-family-row-function
    (ctx f y n)
  (list
   'lambda '(derivatives)
   (p63a3-implies-term
    (list 'p63a3-regularity-p
          (p63a3-quoted ctx)
          (p63a3-quoted y)
          'derivatives
          (p63a3-quoted n))
    (list 'p63a3-equivalence-p
          (p63a3-quoted ctx)
          (p63a3-quoted f)
          (p63a3-quoted y)
          'derivatives
          (p63a3-quoted n)))))

(defun putnam-1963-a3-statement (ctx n f y)
  (implies
   (and
    (p63a3-context-p ctx)
    (natp n)
    (< 0 n)
    (p63a3-real-function-p (p63a3-r-carrier ctx) f)
    (p63a3-real-function-p (p63a3-r-carrier ctx) y)
    (p63a3-continuous-on-p
     ctx f (p63a3-ici-set ctx (p63a3-r-one ctx)))
    (p63a3-exists-p
     (p63a3-regularity-family-function ctx y n)
     '(derivatives)))
   (p63a3-universal-p
    (p63a3-equivalence-family-row-function
     ctx f y n)
    '(derivatives))))

(value-triple :itpeval-statement-checked)
:q
