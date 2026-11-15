;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_a2:
;; for f(x) = exp(x^2), there is an open interval and a nonzero differentiable
;; real function g on which (f*g)' = f'*g'. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary sets and functions are tame APPLY$ function objects. FN-EQUAL
;; supplies unbounded universal quantification, and inequality with a
;; constant-false function supplies internal existential quantification.
;; The scalar context is a Dedekind-complete ordered field, hence a
;; presentation of the real field. The exponential is fixed by its exact
;; power series, and derivatives are expanded by their epsilon-delta
;; definition. The interval endpoints and function g remain internal
;; existential witnesses.

(defun p1988a2-quoted (object)
  (list 'quote object))

(defun p1988a2-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (p1988a2-term-list (cdr terms)))
    (p1988a2-quoted nil)))

(defun p1988a2-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (p1988a2-term-list arguments)))

(defun p1988a2-static-apply-term (function arguments)
  (p1988a2-apply-term
   (p1988a2-quoted function)
   arguments))

(defun p1988a2-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p1988a2-and-terms (cdr terms))
            (p1988a2-quoted nil))
    (p1988a2-quoted t)))

(defun p1988a2-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p1988a2-quoted t)
            (p1988a2-or-terms (cdr terms)))
    (p1988a2-quoted nil)))

(defun p1988a2-not-term (term)
  (list 'if term
        (p1988a2-quoted nil)
        (p1988a2-quoted t)))

(defun p1988a2-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (p1988a2-quoted t)))

(defun p1988a2-true-function (formals)
  (list 'lambda formals (p1988a2-quoted t)))

(defun p1988a2-false-function (formals)
  (list 'lambda formals (p1988a2-quoted nil)))

(defun p1988a2-universal-p (function formals)
  (let ((always-true (p1988a2-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun p1988a2-exists-p (function formals)
  (let ((always-false (p1988a2-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun p1988a2-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun p1988a2-unary-value (function object)
  (apply$ function (list object)))

(defun p1988a2-binary-value (function left right)
  (apply$ function (list left right)))

;; Arbitrary real-valued functions and arbitrary subsets of the real carrier.

(defun p1988a2-function-values-function (carrier function)
  (list
   'lambda '(x)
   (p1988a2-implies-term
    (p1988a2-static-apply-term carrier '(x))
    (p1988a2-static-apply-term
     carrier
     (list (p1988a2-static-apply-term function '(x)))))))

(defun p1988a2-real-function-p (carrier function)
  (and
   (tamep-functionp function)
   (p1988a2-universal-p
    (p1988a2-function-values-function carrier function)
    '(x))))

(defun p1988a2-set-subset-carrier-function (carrier set)
  (list
   'lambda '(x)
   (p1988a2-implies-term
    (p1988a2-static-apply-term set '(x))
    (p1988a2-static-apply-term carrier '(x)))))

(defun p1988a2-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (p1988a2-universal-p
    (p1988a2-set-subset-carrier-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun p1988a2-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (p1988a2-static-apply-term add '(x y)))
         (yz-add (p1988a2-static-apply-term add '(y z)))
         (xy-mul (p1988a2-static-apply-term multiply '(x y)))
         (yz-mul (p1988a2-static-apply-term multiply '(y z)))
         (neg-x (p1988a2-static-apply-term negate '(x)))
         (inv-x (p1988a2-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (p1988a2-implies-term
      (p1988a2-and-terms
       (list
        (p1988a2-static-apply-term carrier '(x))
        (p1988a2-static-apply-term carrier '(y))
        (p1988a2-static-apply-term carrier '(z))))
      (p1988a2-and-terms
       (list
        (p1988a2-static-apply-term carrier (list xy-add))
        (p1988a2-static-apply-term carrier (list xy-mul))
        (p1988a2-static-apply-term carrier (list neg-x))
        (p1988a2-static-apply-term carrier (list inv-x))
        (list 'equal
              (p1988a2-static-apply-term add (list xy-add 'z))
              (p1988a2-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (p1988a2-static-apply-term add '(y x)))
        (list 'equal
              (p1988a2-static-apply-term
               add (list 'x (p1988a2-quoted zero)))
              'x)
        (list 'equal
              (p1988a2-static-apply-term add (list 'x neg-x))
              (p1988a2-quoted zero))
        (list 'equal
              (p1988a2-static-apply-term multiply (list xy-mul 'z))
              (p1988a2-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (p1988a2-static-apply-term multiply '(y x)))
        (list 'equal
              (p1988a2-static-apply-term
               multiply (list 'x (p1988a2-quoted one)))
              'x)
        (p1988a2-implies-term
         (list 'equal 'x (p1988a2-quoted zero))
         (list 'equal inv-x (p1988a2-quoted zero)))
        (p1988a2-implies-term
         (p1988a2-not-term
          (list 'equal 'x (p1988a2-quoted zero)))
         (list 'equal
               (p1988a2-static-apply-term
                multiply (list 'x inv-x))
               (p1988a2-quoted one)))
        (list 'equal
              (p1988a2-static-apply-term multiply (list 'x yz-add))
              (p1988a2-static-apply-term
               add
               (list
                (p1988a2-static-apply-term multiply '(x y))
                (p1988a2-static-apply-term multiply '(x z)))))))))))

(defun p1988a2-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (p1988a2-static-apply-term less '(x y)))
        (yx (p1988a2-static-apply-term less '(y x)))
        (yz (p1988a2-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (p1988a2-implies-term
      (p1988a2-and-terms
       (list
        (p1988a2-static-apply-term carrier '(x))
        (p1988a2-static-apply-term carrier '(y))
        (p1988a2-static-apply-term carrier '(z))))
      (p1988a2-and-terms
       (list
        (p1988a2-not-term
         (p1988a2-static-apply-term less '(x x)))
        (p1988a2-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (p1988a2-implies-term
         (p1988a2-and-terms (list xy yz))
         (p1988a2-static-apply-term less '(x z)))
        (p1988a2-implies-term
         xy
         (p1988a2-static-apply-term
          less
          (list
           (p1988a2-static-apply-term add '(x z))
           (p1988a2-static-apply-term add '(y z)))))
        (p1988a2-implies-term
         (p1988a2-and-terms
          (list
           (p1988a2-static-apply-term
            less (list (p1988a2-quoted zero) 'x))
           (p1988a2-static-apply-term
            less (list (p1988a2-quoted zero) 'y))))
         (p1988a2-static-apply-term
          less
          (list
           (p1988a2-quoted zero)
           (p1988a2-static-apply-term multiply '(x y)))))))))))

(defun p1988a2-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (p1988a2-implies-term
    (p1988a2-and-terms
     (list
      (p1988a2-static-apply-term carrier '(x))
      (p1988a2-static-apply-term set '(x))))
    (p1988a2-not-term
     (p1988a2-static-apply-term
      less (list (p1988a2-quoted upper) 'x))))))

(defun p1988a2-upper-bound-p
    (carrier less set upper)
  (and
   (p1988a2-member-p carrier upper)
   (p1988a2-valid-set-p carrier set)
   (p1988a2-universal-p
    (p1988a2-upper-bound-function carrier less set upper)
    '(x))))

(defun p1988a2-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (p1988a2-and-terms
    (list
     (p1988a2-static-apply-term carrier '(x))
     (p1988a2-static-apply-term set '(x))))))

(defun p1988a2-set-nonempty-p (carrier set)
  (and
   (p1988a2-valid-set-p carrier set)
   (p1988a2-exists-p
    (p1988a2-set-nonempty-function carrier set)
    '(x))))

(defun p1988a2-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'p1988a2-upper-bound-p
         (p1988a2-quoted carrier)
         (p1988a2-quoted less)
         (p1988a2-quoted set)
         'upper)))

(defun p1988a2-bounded-above-p (carrier less set)
  (p1988a2-exists-p
   (p1988a2-bounded-above-function carrier less set)
   '(upper)))

(defun p1988a2-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (p1988a2-implies-term
    (list 'p1988a2-upper-bound-p
          (p1988a2-quoted carrier)
          (p1988a2-quoted less)
          (p1988a2-quoted set)
          'upper)
    (p1988a2-not-term
     (p1988a2-static-apply-term
      less (list 'upper (p1988a2-quoted supremum)))))))

(defun p1988a2-least-upper-bound-p
    (carrier less set supremum)
  (and
   (p1988a2-upper-bound-p carrier less set supremum)
   (p1988a2-universal-p
    (p1988a2-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun p1988a2-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (p1988a2-implies-term
    (p1988a2-and-terms
     (list
      (list 'p1988a2-valid-set-p
            (p1988a2-quoted carrier) 'set)
      (list 'p1988a2-set-nonempty-p
            (p1988a2-quoted carrier) 'set)
      (list 'p1988a2-bounded-above-p
            (p1988a2-quoted carrier)
            (p1988a2-quoted less)
            'set)))
    (list 'p1988a2-least-upper-bound-p
          (p1988a2-quoted carrier)
          (p1988a2-quoted less)
          'set
          (p1988a2-static-apply-term
           supremum-operation '(set))))))

(defun p1988a2-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (p1988a2-member-p carrier zero)
   (p1988a2-member-p carrier one)
   (not (equal zero one))
   (p1988a2-universal-p
    (p1988a2-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (p1988a2-universal-p
    (p1988a2-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (p1988a2-universal-p
    (p1988a2-completeness-function
     carrier less supremum)
    '(set))
   (p1988a2-binary-value less zero one)))

;; Real-field context and arithmetic.

(defun p1988a2-r-carrier (ctx) (nth 0 ctx))
(defun p1988a2-r-zero (ctx) (nth 1 ctx))
(defun p1988a2-r-one (ctx) (nth 2 ctx))
(defun p1988a2-r-add (ctx) (nth 3 ctx))
(defun p1988a2-r-mul (ctx) (nth 4 ctx))
(defun p1988a2-r-neg (ctx) (nth 5 ctx))
(defun p1988a2-r-inv (ctx) (nth 6 ctx))
(defun p1988a2-r-lt (ctx) (nth 7 ctx))
(defun p1988a2-r-sup (ctx) (nth 8 ctx))

(defun p1988a2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (p1988a2-real-field-p
    (p1988a2-r-carrier ctx)
    (p1988a2-r-zero ctx)
    (p1988a2-r-one ctx)
    (p1988a2-r-add ctx)
    (p1988a2-r-mul ctx)
    (p1988a2-r-neg ctx)
    (p1988a2-r-inv ctx)
    (p1988a2-r-lt ctx)
    (p1988a2-r-sup ctx))))

(defun p1988a2-r-add-value (ctx left right)
  (p1988a2-binary-value (p1988a2-r-add ctx) left right))

(defun p1988a2-r-neg-value (ctx value)
  (p1988a2-unary-value (p1988a2-r-neg ctx) value))

(defun p1988a2-r-sub-value (ctx left right)
  (p1988a2-r-add-value
   ctx left (p1988a2-r-neg-value ctx right)))

(defun p1988a2-r-mul-value (ctx left right)
  (p1988a2-binary-value (p1988a2-r-mul ctx) left right))

(defun p1988a2-r-inv-value (ctx value)
  (p1988a2-unary-value (p1988a2-r-inv ctx) value))

(defun p1988a2-r-div-value (ctx numerator denominator)
  (p1988a2-r-mul-value
   ctx numerator (p1988a2-r-inv-value ctx denominator)))

(defun p1988a2-r-lt-p (ctx left right)
  (if (p1988a2-binary-value
       (p1988a2-r-lt ctx) left right)
      t nil))

(defun p1988a2-r-le-p (ctx left right)
  (not (p1988a2-r-lt-p ctx right left)))

(defun p1988a2-r-abs-value (ctx value)
  (if (p1988a2-r-lt-p ctx value (p1988a2-r-zero ctx))
      (p1988a2-r-neg-value ctx value)
    value))

(defun p1988a2-positive-real-p (ctx value)
  (and
   (p1988a2-member-p (p1988a2-r-carrier ctx) value)
   (p1988a2-r-lt-p ctx (p1988a2-r-zero ctx) value)))

;; The real exponential, defined by sum_{k=0}^\infty x^k/k!.

(defun p1988a2-r-nat-value (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p1988a2-r-zero ctx)
    (p1988a2-r-add-value
     ctx
     (p1988a2-r-nat-value ctx (- n 1))
     (p1988a2-r-one ctx))))

(defun p1988a2-r-power (ctx value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p1988a2-r-one ctx)
    (p1988a2-r-mul-value
     ctx
     value
     (p1988a2-r-power ctx value (- exponent 1)))))

(defun p1988a2-r-factorial (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p1988a2-r-one ctx)
    (p1988a2-r-mul-value
     ctx
     (p1988a2-r-nat-value ctx n)
     (p1988a2-r-factorial ctx (- n 1)))))

(defun p1988a2-sequence-values-function (ctx sequence)
  (list
   'lambda '(n)
   (p1988a2-implies-term
    (list 'natp 'n)
    (p1988a2-static-apply-term
     (p1988a2-r-carrier ctx)
     (list (p1988a2-static-apply-term sequence '(n)))))))

(defun p1988a2-real-sequence-p (ctx sequence)
  (and
   (tamep-functionp sequence)
   (p1988a2-universal-p
    (p1988a2-sequence-values-function ctx sequence)
    '(n))))

(defun p1988a2-convergence-tail-function
    (ctx sequence limit epsilon start)
  (list
   'lambda '(n)
   (p1988a2-implies-term
    (p1988a2-and-terms
     (list
      (list 'natp 'n)
      (list '<= (p1988a2-quoted start) 'n)))
    (list 'p1988a2-r-lt-p
          (p1988a2-quoted ctx)
          (list 'p1988a2-r-abs-value
                (p1988a2-quoted ctx)
                (list 'p1988a2-r-sub-value
                      (p1988a2-quoted ctx)
                      (p1988a2-static-apply-term sequence '(n))
                      (p1988a2-quoted limit)))
          (p1988a2-quoted epsilon)))))

(defun p1988a2-convergence-tail-p
    (ctx sequence limit epsilon start)
  (and
   (natp start)
   (p1988a2-universal-p
    (p1988a2-convergence-tail-function
     ctx sequence limit epsilon start)
    '(n))))

(defun p1988a2-convergence-start-function
    (ctx sequence limit epsilon)
  (list
   'lambda '(start)
   (list 'p1988a2-convergence-tail-p
         (p1988a2-quoted ctx)
         (p1988a2-quoted sequence)
         (p1988a2-quoted limit)
         (p1988a2-quoted epsilon)
         'start)))

(defun p1988a2-convergence-epsilon-function
    (ctx sequence limit)
  (list
   'lambda '(epsilon)
   (p1988a2-implies-term
    (list 'p1988a2-positive-real-p
          (p1988a2-quoted ctx) 'epsilon)
    (list 'p1988a2-exists-p
          (list 'p1988a2-convergence-start-function
                (p1988a2-quoted ctx)
                (p1988a2-quoted sequence)
                (p1988a2-quoted limit)
                'epsilon)
          (p1988a2-quoted '(start))))))

(defun p1988a2-converges-p (ctx sequence limit)
  (and
   (p1988a2-real-sequence-p ctx sequence)
   (p1988a2-member-p (p1988a2-r-carrier ctx) limit)
   (p1988a2-universal-p
    (p1988a2-convergence-epsilon-function
     ctx sequence limit)
    '(epsilon))))

(defun p1988a2-exp-partial-sum (ctx count x)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p1988a2-r-zero ctx)
    (let* ((index (- count 1))
           (term
            (p1988a2-r-div-value
             ctx
             (p1988a2-r-power ctx x index)
             (p1988a2-r-factorial ctx index))))
      (p1988a2-r-add-value
       ctx
       (p1988a2-exp-partial-sum ctx index x)
       term))))

(defun p1988a2-exp-partial-sum-sequence (ctx x)
  (list
   'lambda '(n)
   (list 'if
         (list 'natp 'n)
         (list 'p1988a2-exp-partial-sum
               (p1988a2-quoted ctx)
               'n
               (p1988a2-quoted x))
         (p1988a2-quoted (p1988a2-r-zero ctx)))))

(defun p1988a2-exp-values-function (ctx exponential)
  (list
   'lambda '(x)
   (p1988a2-implies-term
    (p1988a2-static-apply-term
     (p1988a2-r-carrier ctx) '(x))
    (list 'p1988a2-converges-p
          (p1988a2-quoted ctx)
          (list 'p1988a2-exp-partial-sum-sequence
                (p1988a2-quoted ctx)
                'x)
          (p1988a2-static-apply-term exponential '(x))))))

(defun p1988a2-exponential-operation-p (ctx exponential)
  (and
   (p1988a2-real-function-p
    (p1988a2-r-carrier ctx) exponential)
   (p1988a2-universal-p
    (p1988a2-exp-values-function ctx exponential)
    '(x))))

;; Closed and open intervals.

(defun p1988a2-ioo-set (ctx a b)
  (list
   'lambda '(x)
   (p1988a2-and-terms
    (list
     (p1988a2-static-apply-term
      (p1988a2-r-carrier ctx) '(x))
     (p1988a2-static-apply-term
      (p1988a2-r-lt ctx)
      (list (p1988a2-quoted a) 'x))
     (p1988a2-static-apply-term
      (p1988a2-r-lt ctx)
      (list 'x (p1988a2-quoted b)))))))

(defun p1988a2-icc-set (ctx a b)
  (list
   'lambda '(x)
   (p1988a2-and-terms
    (list
     (p1988a2-static-apply-term
      (p1988a2-r-carrier ctx) '(x))
     (p1988a2-not-term
      (p1988a2-static-apply-term
       (p1988a2-r-lt ctx)
       (list 'x (p1988a2-quoted a))))
     (p1988a2-not-term
      (p1988a2-static-apply-term
       (p1988a2-r-lt ctx)
       (list (p1988a2-quoted b) 'x)))))))

;; Continuity within the closed interval [a,b].

(defun p1988a2-continuity-point-function
    (ctx function a b x epsilon radius)
  (list
   'lambda '(y)
   (p1988a2-implies-term
    (p1988a2-and-terms
     (list
      (p1988a2-static-apply-term
       (p1988a2-icc-set ctx a b) '(y))
      (list 'p1988a2-r-lt-p
            (p1988a2-quoted ctx)
            (list 'p1988a2-r-abs-value
                  (p1988a2-quoted ctx)
                  (list 'p1988a2-r-sub-value
                        (p1988a2-quoted ctx)
                        'y
                        (p1988a2-quoted x)))
            (p1988a2-quoted radius))))
    (list 'p1988a2-r-lt-p
          (p1988a2-quoted ctx)
          (list 'p1988a2-r-abs-value
                (p1988a2-quoted ctx)
                (list 'p1988a2-r-sub-value
                      (p1988a2-quoted ctx)
                      (p1988a2-static-apply-term function '(y))
                      (p1988a2-static-apply-term
                       function
                       (list (p1988a2-quoted x)))))
          (p1988a2-quoted epsilon)))))

(defun p1988a2-continuity-radius-function
    (ctx function a b x epsilon)
  (list
   'lambda '(radius)
   (p1988a2-and-terms
    (list
     (list 'p1988a2-positive-real-p
           (p1988a2-quoted ctx) 'radius)
     (list 'p1988a2-universal-p
           (list 'p1988a2-continuity-point-function
                 (p1988a2-quoted ctx)
                 (p1988a2-quoted function)
                 (p1988a2-quoted a)
                 (p1988a2-quoted b)
                 (p1988a2-quoted x)
                 (p1988a2-quoted epsilon)
                 'radius)
           (p1988a2-quoted '(y)))))))

(defun p1988a2-continuity-epsilon-function
    (ctx function a b x)
  (list
   'lambda '(epsilon)
   (p1988a2-implies-term
    (list 'p1988a2-positive-real-p
          (p1988a2-quoted ctx) 'epsilon)
    (list 'p1988a2-exists-p
          (list 'p1988a2-continuity-radius-function
                (p1988a2-quoted ctx)
                (p1988a2-quoted function)
                (p1988a2-quoted a)
                (p1988a2-quoted b)
                (p1988a2-quoted x)
                'epsilon)
          (p1988a2-quoted '(radius))))))

(defun p1988a2-continuous-on-row-function
    (ctx function a b)
  (list
   'lambda '(x)
   (p1988a2-implies-term
    (p1988a2-static-apply-term
     (p1988a2-icc-set ctx a b) '(x))
    (list 'p1988a2-universal-p
          (list 'p1988a2-continuity-epsilon-function
                (p1988a2-quoted ctx)
                (p1988a2-quoted function)
                (p1988a2-quoted a)
                (p1988a2-quoted b)
                'x)
          (p1988a2-quoted '(epsilon))))))

(defun p1988a2-continuous-on-icc-p
    (ctx function a b)
  (p1988a2-universal-p
   (p1988a2-continuous-on-row-function
    ctx function a b)
   '(x)))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun p1988a2-derivative-point-function
    (ctx function derivative x epsilon radius)
  (list
   'lambda '(y)
   (p1988a2-implies-term
    (p1988a2-and-terms
     (list
      (p1988a2-static-apply-term
       (p1988a2-r-carrier ctx) '(y))
      (list 'p1988a2-r-lt-p
            (p1988a2-quoted ctx)
            (list 'p1988a2-r-abs-value
                  (p1988a2-quoted ctx)
                  (list 'p1988a2-r-sub-value
                        (p1988a2-quoted ctx)
                        'y
                        (p1988a2-quoted x)))
            (p1988a2-quoted radius))))
    (list 'p1988a2-r-le-p
          (p1988a2-quoted ctx)
          (list 'p1988a2-r-abs-value
                (p1988a2-quoted ctx)
                (list 'p1988a2-r-sub-value
                      (p1988a2-quoted ctx)
                      (list 'p1988a2-r-sub-value
                            (p1988a2-quoted ctx)
                            (p1988a2-static-apply-term function '(y))
                            (p1988a2-static-apply-term
                             function
                             (list (p1988a2-quoted x))))
                      (list 'p1988a2-r-mul-value
                            (p1988a2-quoted ctx)
                            (p1988a2-quoted derivative)
                            (list 'p1988a2-r-sub-value
                                  (p1988a2-quoted ctx)
                                  'y
                                  (p1988a2-quoted x)))))
          (list 'p1988a2-r-mul-value
                (p1988a2-quoted ctx)
                (p1988a2-quoted epsilon)
                (list 'p1988a2-r-abs-value
                      (p1988a2-quoted ctx)
                      (list 'p1988a2-r-sub-value
                            (p1988a2-quoted ctx)
                            'y
                            (p1988a2-quoted x))))))))

(defun p1988a2-derivative-radius-function
    (ctx function derivative x epsilon)
  (list
   'lambda '(radius)
   (p1988a2-and-terms
    (list
     (list 'p1988a2-positive-real-p
           (p1988a2-quoted ctx) 'radius)
     (list 'p1988a2-universal-p
           (list 'p1988a2-derivative-point-function
                 (p1988a2-quoted ctx)
                 (p1988a2-quoted function)
                 (p1988a2-quoted derivative)
                 (p1988a2-quoted x)
                 (p1988a2-quoted epsilon)
                 'radius)
           (p1988a2-quoted '(y)))))))

(defun p1988a2-derivative-epsilon-function
    (ctx function derivative x)
  (list
   'lambda '(epsilon)
   (p1988a2-implies-term
    (list 'p1988a2-positive-real-p
          (p1988a2-quoted ctx) 'epsilon)
    (list 'p1988a2-exists-p
          (list 'p1988a2-derivative-radius-function
                (p1988a2-quoted ctx)
                (p1988a2-quoted function)
                (p1988a2-quoted derivative)
                (p1988a2-quoted x)
                'epsilon)
          (p1988a2-quoted '(radius))))))

(defun p1988a2-has-derivative-at-p
    (ctx function derivative x)
  (and
   (p1988a2-member-p (p1988a2-r-carrier ctx) derivative)
   (p1988a2-member-p (p1988a2-r-carrier ctx) x)
   (p1988a2-universal-p
    (p1988a2-derivative-epsilon-function
     ctx function derivative x)
    '(epsilon))))

(defun p1988a2-derivative-witness-function
    (ctx function x)
  (list
   'lambda '(derivative)
   (list 'p1988a2-has-derivative-at-p
         (p1988a2-quoted ctx)
         (p1988a2-quoted function)
         'derivative
         (p1988a2-quoted x))))

(defun p1988a2-differentiable-at-p
    (ctx function x)
  (p1988a2-exists-p
   (p1988a2-derivative-witness-function
    ctx function x)
   '(derivative)))

(defun p1988a2-f-function (ctx exponential)
  (list
   'lambda '(x)
   (p1988a2-static-apply-term
    exponential
    (list
     (list 'p1988a2-r-mul-value
           (p1988a2-quoted ctx)
           'x
           'x)))))

(defun p1988a2-product-function (ctx left right)
  (list
   'lambda '(x)
   (list 'p1988a2-r-mul-value
         (p1988a2-quoted ctx)
         (p1988a2-static-apply-term left '(x))
         (p1988a2-static-apply-term right '(x)))))

(defun p1988a2-nonzero-witness-function (ctx g a b)
  (list
   'lambda '(x)
   (p1988a2-and-terms
    (list
     (p1988a2-static-apply-term
      (p1988a2-ioo-set ctx a b) '(x))
     (p1988a2-not-term
      (list 'equal
            (p1988a2-static-apply-term g '(x))
            (p1988a2-quoted (p1988a2-r-zero ctx))))))))

(defun p1988a2-point-derivative-witness-function
    (ctx f g product x)
  (list
   'lambda '(g-derivative f-derivative product-derivative)
   (p1988a2-and-terms
    (list
     (list 'p1988a2-has-derivative-at-p
           (p1988a2-quoted ctx)
           (p1988a2-quoted g)
           'g-derivative
           (p1988a2-quoted x))
     (list 'p1988a2-has-derivative-at-p
           (p1988a2-quoted ctx)
           (p1988a2-quoted f)
           'f-derivative
           (p1988a2-quoted x))
     (list 'p1988a2-has-derivative-at-p
           (p1988a2-quoted ctx)
           (p1988a2-quoted product)
           'product-derivative
           (p1988a2-quoted x))
     (list 'equal
           'product-derivative
           (list 'p1988a2-r-mul-value
                 (p1988a2-quoted ctx)
                 'f-derivative
                 'g-derivative))))))

(defun p1988a2-point-condition-function
    (ctx f g product a b)
  (list
   'lambda '(x)
   (p1988a2-implies-term
    (p1988a2-static-apply-term
     (p1988a2-ioo-set ctx a b) '(x))
    (list 'p1988a2-exists-p
          (list 'p1988a2-point-derivative-witness-function
                (p1988a2-quoted ctx)
                (p1988a2-quoted f)
                (p1988a2-quoted g)
                (p1988a2-quoted product)
                'x)
          (p1988a2-quoted
           '(g-derivative f-derivative product-derivative))))))

(defun p1988a2-interval-witness-function (ctx exponential)
  (let ((f (p1988a2-f-function ctx exponential)))
    (list
     'lambda '(a b g)
     (p1988a2-and-terms
      (list
       (p1988a2-static-apply-term
        (p1988a2-r-carrier ctx) '(a))
       (p1988a2-static-apply-term
        (p1988a2-r-carrier ctx) '(b))
       (p1988a2-static-apply-term
        (p1988a2-r-lt ctx) '(a b))
       (list 'p1988a2-real-function-p
             (p1988a2-quoted (p1988a2-r-carrier ctx))
             'g)
       (list 'p1988a2-exists-p
             (list 'p1988a2-nonzero-witness-function
                   (p1988a2-quoted ctx)
                   'g
                   'a
                   'b)
             (p1988a2-quoted '(x)))
       (list 'p1988a2-universal-p
             (list 'p1988a2-point-condition-function
                   (p1988a2-quoted ctx)
                   (p1988a2-quoted f)
                   'g
                   (list 'p1988a2-product-function
                         (p1988a2-quoted ctx)
                         (p1988a2-quoted f)
                         'g)
                   'a
                   'b)
             (p1988a2-quoted '(x))))))))

(defun putnambench-putnam-1988-a2-solution ()
  t)

(defun putnambench-putnam-1988-a2-statement (ctx exponential)
  (implies
   (and
    (p1988a2-context-p ctx)
    (p1988a2-exponential-operation-p ctx exponential))
   (equal
    (if (putnambench-putnam-1988-a2-solution) t nil)
    (if
        (p1988a2-exists-p
         (p1988a2-interval-witness-function ctx exponential)
         '(a b g))
        t
      nil))))

(value-triple :itpeval-statement-checked)
:q
