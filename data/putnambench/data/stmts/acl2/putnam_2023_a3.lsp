;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_a3:
;; pi/2 is the smallest positive zero time attainable by globally
;; differentiable real functions satisfying the coupled derivative bounds.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ objects represent arbitrary carriers and functions. FN-EQUAL
;; supplies unbounded universal quantification, and inequality with a
;; constant-false function supplies internal existential quantification.
;; A Dedekind-complete ordered field presents the reals. Differentiability is
;; expanded by its epsilon remainder condition. Sine and cosine are fixed by
;; their initial values and differential system, and pi-value is their least
;; positive sine zero. All functions and derivative values in the Putnam
;; condition remain internally quantified.

(defun p23a3-quoted (object)
  (list 'quote object))

(defun p23a3-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (p23a3-term-list (cdr terms)))
    (p23a3-quoted nil)))

(defun p23a3-apply-term (function-term arguments)
  (list 'apply$
        function-term
        (p23a3-term-list arguments)))

(defun p23a3-static-apply-term (function arguments)
  (p23a3-apply-term
   (p23a3-quoted function)
   arguments))

(defun p23a3-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p23a3-and-terms (cdr terms))
            (p23a3-quoted nil))
    (p23a3-quoted t)))

(defun p23a3-or-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (p23a3-quoted t)
            (p23a3-or-terms (cdr terms)))
    (p23a3-quoted nil)))

(defun p23a3-not-term (term)
  (list 'if term
        (p23a3-quoted nil)
        (p23a3-quoted t)))

(defun p23a3-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (p23a3-quoted t)))

(defun p23a3-iff-term (left right)
  (list 'if left
        (list 'if right
              (p23a3-quoted t)
              (p23a3-quoted nil))
        (list 'if right
              (p23a3-quoted nil)
              (p23a3-quoted t))))

(defun p23a3-true-function (formals)
  (list 'lambda formals (p23a3-quoted t)))

(defun p23a3-false-function (formals)
  (list 'lambda formals (p23a3-quoted nil)))

(defun p23a3-universal-p (function formals)
  (let ((always-true (p23a3-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun p23a3-exists-p (function formals)
  (let ((always-false (p23a3-false-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-false)
         (not (fn-equal function always-false)))))

(defun p23a3-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun p23a3-unary-value (function object)
  (apply$ function (list object)))

(defun p23a3-binary-value (function left right)
  (apply$ function (list left right)))

;; Arbitrary real-valued functions and arbitrary subsets of the real carrier.

(defun p23a3-function-values-function (carrier function)
  (list
   'lambda '(x)
   (p23a3-implies-term
    (p23a3-static-apply-term carrier '(x))
    (p23a3-static-apply-term
     carrier
     (list (p23a3-static-apply-term function '(x)))))))

(defun p23a3-real-function-p (carrier function)
  (and
   (tamep-functionp function)
   (p23a3-universal-p
    (p23a3-function-values-function carrier function)
    '(x))))

(defun p23a3-set-subset-carrier-function (carrier set)
  (list
   'lambda '(x)
   (p23a3-implies-term
    (p23a3-static-apply-term set '(x))
    (p23a3-static-apply-term carrier '(x)))))

(defun p23a3-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (p23a3-universal-p
    (p23a3-set-subset-carrier-function carrier set)
    '(x))))

;; A Dedekind-complete ordered field, used as an abstract presentation of R.

(defun p23a3-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (p23a3-static-apply-term add '(x y)))
         (yz-add (p23a3-static-apply-term add '(y z)))
         (xy-mul (p23a3-static-apply-term multiply '(x y)))
         (yz-mul (p23a3-static-apply-term multiply '(y z)))
         (neg-x (p23a3-static-apply-term negate '(x)))
         (inv-x (p23a3-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (p23a3-implies-term
      (p23a3-and-terms
       (list
        (p23a3-static-apply-term carrier '(x))
        (p23a3-static-apply-term carrier '(y))
        (p23a3-static-apply-term carrier '(z))))
      (p23a3-and-terms
       (list
        (p23a3-static-apply-term carrier (list xy-add))
        (p23a3-static-apply-term carrier (list xy-mul))
        (p23a3-static-apply-term carrier (list neg-x))
        (p23a3-static-apply-term carrier (list inv-x))
        (list 'equal
              (p23a3-static-apply-term add (list xy-add 'z))
              (p23a3-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (p23a3-static-apply-term add '(y x)))
        (list 'equal
              (p23a3-static-apply-term
               add (list 'x (p23a3-quoted zero)))
              'x)
        (list 'equal
              (p23a3-static-apply-term add (list 'x neg-x))
              (p23a3-quoted zero))
        (list 'equal
              (p23a3-static-apply-term multiply (list xy-mul 'z))
              (p23a3-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (p23a3-static-apply-term multiply '(y x)))
        (list 'equal
              (p23a3-static-apply-term
               multiply (list 'x (p23a3-quoted one)))
              'x)
        (p23a3-implies-term
         (list 'equal 'x (p23a3-quoted zero))
         (list 'equal inv-x (p23a3-quoted zero)))
        (p23a3-implies-term
         (p23a3-not-term
          (list 'equal 'x (p23a3-quoted zero)))
         (list 'equal
               (p23a3-static-apply-term
                multiply (list 'x inv-x))
               (p23a3-quoted one)))
        (list 'equal
              (p23a3-static-apply-term multiply (list 'x yz-add))
              (p23a3-static-apply-term
               add
               (list
                (p23a3-static-apply-term multiply '(x y))
                (p23a3-static-apply-term multiply '(x z)))))))))))

(defun p23a3-order-laws-function
    (carrier zero add multiply less)
  (let ((xy (p23a3-static-apply-term less '(x y)))
        (yx (p23a3-static-apply-term less '(y x)))
        (yz (p23a3-static-apply-term less '(y z))))
    (list
     'lambda '(x y z)
     (p23a3-implies-term
      (p23a3-and-terms
       (list
        (p23a3-static-apply-term carrier '(x))
        (p23a3-static-apply-term carrier '(y))
        (p23a3-static-apply-term carrier '(z))))
      (p23a3-and-terms
       (list
        (p23a3-not-term
         (p23a3-static-apply-term less '(x x)))
        (p23a3-or-terms
         (list xy yx (list 'equal 'x 'y)))
        (p23a3-implies-term
         (p23a3-and-terms (list xy yz))
         (p23a3-static-apply-term less '(x z)))
        (p23a3-implies-term
         xy
         (p23a3-static-apply-term
          less
          (list
           (p23a3-static-apply-term add '(x z))
           (p23a3-static-apply-term add '(y z)))))
        (p23a3-implies-term
         (p23a3-and-terms
          (list
           (p23a3-static-apply-term
            less (list (p23a3-quoted zero) 'x))
           (p23a3-static-apply-term
            less (list (p23a3-quoted zero) 'y))))
         (p23a3-static-apply-term
          less
          (list
           (p23a3-quoted zero)
           (p23a3-static-apply-term multiply '(x y)))))))))))

(defun p23a3-upper-bound-function
    (carrier less set upper)
  (list
   'lambda '(x)
   (p23a3-implies-term
    (p23a3-and-terms
     (list
      (p23a3-static-apply-term carrier '(x))
      (p23a3-static-apply-term set '(x))))
    (p23a3-not-term
     (p23a3-static-apply-term
      less (list (p23a3-quoted upper) 'x))))))

(defun p23a3-upper-bound-p
    (carrier less set upper)
  (and
   (p23a3-member-p carrier upper)
   (p23a3-valid-set-p carrier set)
   (p23a3-universal-p
    (p23a3-upper-bound-function carrier less set upper)
    '(x))))

(defun p23a3-set-nonempty-function (carrier set)
  (list
   'lambda '(x)
   (p23a3-and-terms
    (list
     (p23a3-static-apply-term carrier '(x))
     (p23a3-static-apply-term set '(x))))))

(defun p23a3-set-nonempty-p (carrier set)
  (and
   (p23a3-valid-set-p carrier set)
   (p23a3-exists-p
    (p23a3-set-nonempty-function carrier set)
    '(x))))

(defun p23a3-bounded-above-function
    (carrier less set)
  (list
   'lambda '(upper)
   (list 'p23a3-upper-bound-p
         (p23a3-quoted carrier)
         (p23a3-quoted less)
         (p23a3-quoted set)
         'upper)))

(defun p23a3-bounded-above-p (carrier less set)
  (p23a3-exists-p
   (p23a3-bounded-above-function carrier less set)
   '(upper)))

(defun p23a3-least-upper-bound-function
    (carrier less set supremum)
  (list
   'lambda '(upper)
   (p23a3-implies-term
    (list 'p23a3-upper-bound-p
          (p23a3-quoted carrier)
          (p23a3-quoted less)
          (p23a3-quoted set)
          'upper)
    (p23a3-not-term
     (p23a3-static-apply-term
      less (list 'upper (p23a3-quoted supremum)))))))

(defun p23a3-least-upper-bound-p
    (carrier less set supremum)
  (and
   (p23a3-upper-bound-p carrier less set supremum)
   (p23a3-universal-p
    (p23a3-least-upper-bound-function
     carrier less set supremum)
    '(upper))))

(defun p23a3-completeness-function
    (carrier less supremum-operation)
  (list
   'lambda '(set)
   (p23a3-implies-term
    (p23a3-and-terms
     (list
      (list 'p23a3-valid-set-p
            (p23a3-quoted carrier) 'set)
      (list 'p23a3-set-nonempty-p
            (p23a3-quoted carrier) 'set)
      (list 'p23a3-bounded-above-p
            (p23a3-quoted carrier)
            (p23a3-quoted less)
            'set)))
    (list 'p23a3-least-upper-bound-p
          (p23a3-quoted carrier)
          (p23a3-quoted less)
          'set
          (p23a3-static-apply-term
           supremum-operation '(set))))))

(defun p23a3-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (p23a3-member-p carrier zero)
   (p23a3-member-p carrier one)
   (not (equal zero one))
   (p23a3-universal-p
    (p23a3-field-laws-function
     carrier zero one add multiply negate inverse)
    '(x y z))
   (p23a3-universal-p
    (p23a3-order-laws-function
     carrier zero add multiply less)
    '(x y z))
   (p23a3-universal-p
    (p23a3-completeness-function
     carrier less supremum)
    '(set))
   (p23a3-binary-value less zero one)))

;; Real-field context and arithmetic.

(defun p23a3-r-carrier (ctx) (nth 0 ctx))
(defun p23a3-r-zero (ctx) (nth 1 ctx))
(defun p23a3-r-one (ctx) (nth 2 ctx))
(defun p23a3-r-add (ctx) (nth 3 ctx))
(defun p23a3-r-mul (ctx) (nth 4 ctx))
(defun p23a3-r-neg (ctx) (nth 5 ctx))
(defun p23a3-r-inv (ctx) (nth 6 ctx))
(defun p23a3-r-lt (ctx) (nth 7 ctx))
(defun p23a3-r-sup (ctx) (nth 8 ctx))

(defun p23a3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (p23a3-real-field-p
    (p23a3-r-carrier ctx)
    (p23a3-r-zero ctx)
    (p23a3-r-one ctx)
    (p23a3-r-add ctx)
    (p23a3-r-mul ctx)
    (p23a3-r-neg ctx)
    (p23a3-r-inv ctx)
    (p23a3-r-lt ctx)
    (p23a3-r-sup ctx))))

(defun p23a3-r-add-value (ctx left right)
  (p23a3-binary-value (p23a3-r-add ctx) left right))

(defun p23a3-r-neg-value (ctx value)
  (p23a3-unary-value (p23a3-r-neg ctx) value))

(defun p23a3-r-sub-value (ctx left right)
  (p23a3-r-add-value
   ctx left (p23a3-r-neg-value ctx right)))

(defun p23a3-r-mul-value (ctx left right)
  (p23a3-binary-value (p23a3-r-mul ctx) left right))

(defun p23a3-r-inv-value (ctx value)
  (p23a3-unary-value (p23a3-r-inv ctx) value))

(defun p23a3-r-div-value (ctx numerator denominator)
  (p23a3-r-mul-value
   ctx numerator (p23a3-r-inv-value ctx denominator)))

(defun p23a3-r-lt-p (ctx left right)
  (if (p23a3-binary-value
       (p23a3-r-lt ctx) left right)
      t nil))

(defun p23a3-r-le-p (ctx left right)
  (not (p23a3-r-lt-p ctx right left)))

(defun p23a3-r-abs-value (ctx value)
  (if (p23a3-r-lt-p ctx value (p23a3-r-zero ctx))
      (p23a3-r-neg-value ctx value)
    value))

(defun p23a3-positive-real-p (ctx value)
  (and
   (p23a3-member-p (p23a3-r-carrier ctx) value)
   (p23a3-r-lt-p ctx (p23a3-r-zero ctx) value)))

(defun p23a3-nonnegative-real-p (ctx value)
  (and
   (p23a3-member-p (p23a3-r-carrier ctx) value)
   (p23a3-r-le-p ctx (p23a3-r-zero ctx) value)))
;; Real differentiability, expanded rather than left as an uninterpreted
;; analytic predicate.

(defun p23a3-real-derivative-nearby-function
    (ctx function point derivative epsilon radius)
  (let* ((fy (p23a3-static-apply-term function '(y)))
         (fx (p23a3-static-apply-term
              function (list (p23a3-quoted point))))
         (delta
          (list 'p23a3-r-sub-value
                (p23a3-quoted ctx)
                'y
                (p23a3-quoted point)))
         (error
          (list
           'p23a3-r-sub-value
           (p23a3-quoted ctx)
           (list
            'p23a3-r-sub-value
            (p23a3-quoted ctx)
            fy
            fx)
           (list
            'p23a3-r-mul-value
            (p23a3-quoted ctx)
            (p23a3-quoted derivative)
            delta))))
    (list
     'lambda '(y)
     (p23a3-implies-term
      (p23a3-and-terms
       (list
        (p23a3-static-apply-term
         (p23a3-r-carrier ctx) '(y))
        (list
         'p23a3-r-lt-p
         (p23a3-quoted ctx)
         (list
          'p23a3-r-abs-value
          (p23a3-quoted ctx)
          delta)
         (p23a3-quoted radius))))
      (list
       'p23a3-r-le-p
       (p23a3-quoted ctx)
       (list
        'p23a3-r-abs-value
        (p23a3-quoted ctx)
        error)
       (list
        'p23a3-r-mul-value
        (p23a3-quoted ctx)
        (p23a3-quoted epsilon)
        (list
         'p23a3-r-abs-value
         (p23a3-quoted ctx)
         delta)))))))

(defun p23a3-real-derivative-radius-function
    (ctx function point derivative epsilon)
  (list
   'lambda '(radius)
   (p23a3-and-terms
    (list
     (list 'p23a3-positive-real-p
           (p23a3-quoted ctx) 'radius)
     (list
      'p23a3-universal-p
      (list
       'p23a3-real-derivative-nearby-function
       (p23a3-quoted ctx)
       (p23a3-quoted function)
       (p23a3-quoted point)
       (p23a3-quoted derivative)
       (p23a3-quoted epsilon)
       'radius)
      (p23a3-quoted '(y)))))))

(defun p23a3-real-derivative-epsilon-function
    (ctx function point derivative)
  (list
   'lambda '(epsilon)
   (p23a3-implies-term
    (list 'p23a3-positive-real-p
          (p23a3-quoted ctx) 'epsilon)
    (list
     'p23a3-exists-p
     (list
      'p23a3-real-derivative-radius-function
      (p23a3-quoted ctx)
      (p23a3-quoted function)
      (p23a3-quoted point)
      (p23a3-quoted derivative)
      'epsilon)
     (p23a3-quoted '(radius))))))

(defun p23a3-real-has-derivative-at-p
    (ctx function point derivative)
  (and
   (p23a3-member-p (p23a3-r-carrier ctx) point)
   (p23a3-member-p (p23a3-r-carrier ctx) derivative)
   (p23a3-universal-p
    (p23a3-real-derivative-epsilon-function
     ctx function point derivative)
    '(epsilon))))

;; Sine and cosine are fixed by their initial values and differential system.

(defun p23a3-trigonometric-laws-function (ctx sine cosine)
  (list
   'lambda '(x)
   (p23a3-implies-term
    (p23a3-static-apply-term
     (p23a3-r-carrier ctx) '(x))
    (p23a3-and-terms
     (list
      (list
       'p23a3-real-has-derivative-at-p
       (p23a3-quoted ctx)
       (p23a3-quoted sine)
       'x
       (p23a3-static-apply-term cosine '(x)))
      (list
       'p23a3-real-has-derivative-at-p
       (p23a3-quoted ctx)
       (p23a3-quoted cosine)
       'x
       (list
        'p23a3-r-neg-value
        (p23a3-quoted ctx)
        (p23a3-static-apply-term sine '(x)))))))))

(defun p23a3-trigonometric-operations-p (ctx sine cosine)
  (and
   (p23a3-real-function-p
    (p23a3-r-carrier ctx) sine)
   (p23a3-real-function-p
    (p23a3-r-carrier ctx) cosine)
   (equal
    (p23a3-unary-value sine (p23a3-r-zero ctx))
    (p23a3-r-zero ctx))
   (equal
    (p23a3-unary-value cosine (p23a3-r-zero ctx))
    (p23a3-r-one ctx))
   (p23a3-universal-p
    (p23a3-trigonometric-laws-function ctx sine cosine)
    '(x))))

(defun p23a3-no-positive-sine-zero-below-function
    (ctx sine pi-value)
  (list
   'lambda '(x)
   (p23a3-implies-term
    (p23a3-and-terms
     (list
      (p23a3-static-apply-term
       (p23a3-r-carrier ctx) '(x))
      (list
       'p23a3-r-lt-p
       (p23a3-quoted ctx)
       (p23a3-quoted (p23a3-r-zero ctx))
       'x)
      (list
       'p23a3-r-lt-p
       (p23a3-quoted ctx)
       'x
       (p23a3-quoted pi-value))))
    (p23a3-not-term
     (list
      'equal
      (p23a3-static-apply-term sine '(x))
      (p23a3-quoted (p23a3-r-zero ctx)))))))

(defun p23a3-pi-value-p (ctx sine cosine pi-value)
  (and
   (p23a3-trigonometric-operations-p ctx sine cosine)
   (p23a3-positive-real-p ctx pi-value)
   (equal
    (p23a3-unary-value sine pi-value)
    (p23a3-r-zero ctx))
   (p23a3-universal-p
    (p23a3-no-positive-sine-zero-below-function
     ctx sine pi-value)
    '(x))))

;; At each real input, the derivative values are internal witnesses. This is
;; equivalent to using DERIV because a derivative, when it exists, is unique.

(defun p23a3-derivative-pair-witness-function
    (ctx f g point)
  (let ((f-point (p23a3-unary-value f point))
        (g-point (p23a3-unary-value g point)))
    (list
     'lambda '(f-prime g-prime)
     (p23a3-and-terms
      (list
       (p23a3-static-apply-term
        (p23a3-r-carrier ctx) '(f-prime))
       (p23a3-static-apply-term
        (p23a3-r-carrier ctx) '(g-prime))
       (list
        'p23a3-real-has-derivative-at-p
        (p23a3-quoted ctx)
        (p23a3-quoted f)
        (p23a3-quoted point)
        'f-prime)
       (list
        'p23a3-real-has-derivative-at-p
        (p23a3-quoted ctx)
        (p23a3-quoted g)
        (p23a3-quoted point)
        'g-prime)
       (list
        'p23a3-r-le-p
        (p23a3-quoted ctx)
        (list
         'p23a3-r-abs-value
         (p23a3-quoted ctx)
         'f-prime)
        (p23a3-quoted
         (p23a3-r-abs-value ctx g-point)))
       (list
        'p23a3-r-le-p
        (p23a3-quoted ctx)
        (list
         'p23a3-r-abs-value
         (p23a3-quoted ctx)
         'g-prime)
        (p23a3-quoted
         (p23a3-r-abs-value ctx f-point))))))))

(defun p23a3-derivative-bounds-at-p (ctx f g point)
  (p23a3-exists-p
   (p23a3-derivative-pair-witness-function
    ctx f g point)
   '(f-prime g-prime)))

(defun p23a3-all-points-function (ctx f g)
  (list
   'lambda '(x)
   (p23a3-implies-term
    (p23a3-static-apply-term
     (p23a3-r-carrier ctx) '(x))
    (list
     'p23a3-derivative-bounds-at-p
     (p23a3-quoted ctx)
     (p23a3-quoted f)
     (p23a3-quoted g)
     'x))))

(defun p23a3-admissible-functions-p (ctx f g r)
  (and
   (p23a3-real-function-p
    (p23a3-r-carrier ctx) f)
   (p23a3-real-function-p
    (p23a3-r-carrier ctx) g)
   (p23a3-positive-real-p
    ctx
    (p23a3-unary-value f (p23a3-r-zero ctx)))
   (equal
    (p23a3-unary-value g (p23a3-r-zero ctx))
    (p23a3-r-zero ctx))
   (equal
    (p23a3-unary-value f r)
    (p23a3-r-zero ctx))
   (p23a3-universal-p
    (p23a3-all-points-function ctx f g)
    '(x))))

(defun p23a3-admissible-witness-function (ctx r)
  (list
   'lambda '(f g)
   (list
    'p23a3-admissible-functions-p
    (p23a3-quoted ctx)
    'f
    'g
    (p23a3-quoted r))))

(defun p23a3-admissible-p (ctx r)
  (and
   (p23a3-member-p (p23a3-r-carrier ctx) r)
   (p23a3-exists-p
    (p23a3-admissible-witness-function ctx r)
    '(f g))))

(defun p23a3-no-smaller-admissible-function
    (ctx solution)
  (list
   'lambda '(t-value)
   (p23a3-implies-term
    (p23a3-and-terms
     (list
      (p23a3-static-apply-term
       (p23a3-r-carrier ctx) '(t-value))
      (list
       'p23a3-r-lt-p
       (p23a3-quoted ctx)
       (p23a3-quoted (p23a3-r-zero ctx))
       't-value)
      (list
       'p23a3-r-lt-p
       (p23a3-quoted ctx)
       't-value
       (p23a3-quoted solution))))
    (p23a3-not-term
     (list
      'p23a3-admissible-p
      (p23a3-quoted ctx)
      't-value)))))

(defun putnambench-putnam-2023-a3-statement
    (ctx sine cosine pi-value)
  (implies
   (and
    (p23a3-context-p ctx)
    (p23a3-pi-value-p ctx sine cosine pi-value))
   (let* ((two
           (p23a3-r-add-value
            ctx
            (p23a3-r-one ctx)
            (p23a3-r-one ctx)))
          (solution
           (p23a3-r-div-value ctx pi-value two)))
     (and
      (p23a3-positive-real-p ctx solution)
      (p23a3-admissible-p ctx solution)
      (p23a3-universal-p
       (p23a3-no-smaller-admissible-function
        ctx solution)
       '(t-value))))))

(value-triple :itpeval-statement-checked)
:q
