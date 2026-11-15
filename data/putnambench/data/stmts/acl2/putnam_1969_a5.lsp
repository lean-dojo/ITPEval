;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_a5:
;; a controlled two-dimensional real differential system reaches the origin
;; at a positive time exactly when its two initial coordinates agree. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers up to the
;; unique ordered-field isomorphism. APPLY$ function objects represent the
;; arbitrary real-valued functions in the source, and DEFUN-SK keeps the
;; existential witnesses x, y, and u internal to the statement. Continuity
;; and differentiability are expanded by their global epsilon-delta
;; definitions.

(defun p69a5-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p69a5-unary-value (function value)
  (apply$ function (list value)))

(defun p69a5-binary-value (function left right)
  (apply$ function (list left right)))

(defun-sk p69a5-real-function-values-p (carrier function)
  (forall (x)
    (implies
     (p69a5-member-p carrier x)
     (p69a5-member-p
      carrier
      (p69a5-unary-value function x)))))

(defun p69a5-real-function-p (carrier function)
  (and
   (tamep-functionp function)
   (p69a5-real-function-values-p carrier function)))

;; Complete ordered-field presentation of the real scalar domain.

(defun-sk p69a5-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p69a5-member-p carrier x)
      (p69a5-member-p carrier y)
      (p69a5-member-p carrier z))
     (let* ((xy-add (p69a5-binary-value add x y))
            (yz-add (p69a5-binary-value add y z))
            (xy-mul (p69a5-binary-value multiply x y))
            (yz-mul (p69a5-binary-value multiply y z))
            (neg-x (p69a5-unary-value negate x))
            (inv-x (p69a5-unary-value inverse x)))
       (and
        (p69a5-member-p carrier xy-add)
        (p69a5-member-p carrier xy-mul)
        (p69a5-member-p carrier neg-x)
        (p69a5-member-p carrier inv-x)
        (equal
         (p69a5-binary-value add xy-add z)
         (p69a5-binary-value add x yz-add))
        (equal xy-add (p69a5-binary-value add y x))
        (equal (p69a5-binary-value add x zero) x)
        (equal (p69a5-binary-value add x neg-x) zero)
        (equal
         (p69a5-binary-value multiply xy-mul z)
         (p69a5-binary-value multiply x yz-mul))
        (equal xy-mul (p69a5-binary-value multiply y x))
        (equal (p69a5-binary-value multiply x one) x)
        (equal
         (p69a5-binary-value multiply x yz-add)
         (p69a5-binary-value
          add
          (p69a5-binary-value multiply x y)
          (p69a5-binary-value multiply x z)))
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p69a5-binary-value multiply x inv-x)
          one)))))))

(defun-sk p69a5-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p69a5-member-p carrier x)
      (p69a5-member-p carrier y)
      (p69a5-member-p carrier z))
     (let ((xy (p69a5-binary-value less x y))
           (yx (p69a5-binary-value less y x))
           (yz (p69a5-binary-value less y z)))
       (and
        (not (p69a5-binary-value less x x))
        (or xy yx (equal x y))
        (implies
         (and xy yz)
         (p69a5-binary-value less x z))
        (implies
         xy
         (p69a5-binary-value
          less
          (p69a5-binary-value add x z)
          (p69a5-binary-value add y z)))
        (implies
         (and
          (p69a5-binary-value less zero x)
          (p69a5-binary-value less zero y))
         (p69a5-binary-value
          less
          zero
          (p69a5-binary-value multiply x y))))))))

(defun-sk p69a5-set-subset-carrier-p (carrier set)
  (forall (x)
    (implies
     (p69a5-member-p set x)
     (p69a5-member-p carrier x))))

(defun p69a5-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (p69a5-set-subset-carrier-p carrier set)))

(defun-sk p69a5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p69a5-member-p carrier x)
     (p69a5-member-p set x))))

(defun-sk p69a5-upper-bound-p (carrier less set upper)
  (forall (x)
    (implies
     (and
      (p69a5-member-p carrier x)
      (p69a5-member-p set x))
     (not (p69a5-binary-value less upper x)))))

(defun-sk p69a5-bounded-above-p (carrier less set)
  (exists (upper)
    (and
     (p69a5-member-p carrier upper)
     (p69a5-upper-bound-p
      carrier less set upper))))

(defun-sk p69a5-least-upper-bound-p
    (carrier less set supremum)
  (forall (upper)
    (implies
     (and
      (p69a5-member-p carrier upper)
      (p69a5-upper-bound-p
       carrier less set upper))
     (not (p69a5-binary-value
           less upper supremum)))))

(defun p69a5-supremum-p
    (carrier less set supremum)
  (and
   (p69a5-member-p carrier supremum)
   (p69a5-upper-bound-p
    carrier less set supremum)
   (p69a5-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p69a5-dedekind-complete-p
    (carrier less supremum-operation)
  (forall (set)
    (implies
     (and
      (p69a5-valid-set-p carrier set)
      (p69a5-set-nonempty-p carrier set)
      (p69a5-bounded-above-p carrier less set))
     (p69a5-supremum-p
      carrier
      less
      set
      (p69a5-unary-value supremum-operation set)))))

(defun p69a5-real-field-p
    (carrier zero one add multiply negate inverse less supremum)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (tamep-functionp supremum)
   (p69a5-member-p carrier zero)
   (p69a5-member-p carrier one)
   (not (equal zero one))
   (p69a5-field-laws-p
    carrier zero one add multiply negate inverse)
   (p69a5-order-laws-p
    carrier zero add multiply less)
   (p69a5-dedekind-complete-p
    carrier less supremum)
   (p69a5-binary-value less zero one)))

;; Real-field context and arithmetic.

(defun p69a5-r-carrier (ctx) (nth 0 ctx))
(defun p69a5-r-zero (ctx) (nth 1 ctx))
(defun p69a5-r-one (ctx) (nth 2 ctx))
(defun p69a5-r-add (ctx) (nth 3 ctx))
(defun p69a5-r-mul (ctx) (nth 4 ctx))
(defun p69a5-r-neg (ctx) (nth 5 ctx))
(defun p69a5-r-inv (ctx) (nth 6 ctx))
(defun p69a5-r-lt (ctx) (nth 7 ctx))
(defun p69a5-r-sup (ctx) (nth 8 ctx))

(defun p69a5-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (p69a5-real-field-p
    (p69a5-r-carrier ctx)
    (p69a5-r-zero ctx)
    (p69a5-r-one ctx)
    (p69a5-r-add ctx)
    (p69a5-r-mul ctx)
    (p69a5-r-neg ctx)
    (p69a5-r-inv ctx)
    (p69a5-r-lt ctx)
    (p69a5-r-sup ctx))))

(defun p69a5-r-add-value (ctx left right)
  (p69a5-binary-value
   (p69a5-r-add ctx) left right))

(defun p69a5-r-neg-value (ctx value)
  (p69a5-unary-value
   (p69a5-r-neg ctx) value))

(defun p69a5-r-sub-value (ctx left right)
  (p69a5-r-add-value
   ctx left (p69a5-r-neg-value ctx right)))

(defun p69a5-r-mul-value (ctx left right)
  (p69a5-binary-value
   (p69a5-r-mul ctx) left right))

(defun p69a5-r-lt-p (ctx left right)
  (if (p69a5-binary-value
       (p69a5-r-lt ctx) left right)
      t nil))

(defun p69a5-r-le-p (ctx left right)
  (not (p69a5-r-lt-p ctx right left)))

(defun p69a5-r-abs-value (ctx value)
  (if (p69a5-r-lt-p
       ctx value (p69a5-r-zero ctx))
      (p69a5-r-neg-value ctx value)
    value))

(defun p69a5-positive-real-p (ctx value)
  (and
   (p69a5-member-p
    (p69a5-r-carrier ctx) value)
   (p69a5-r-lt-p
    ctx (p69a5-r-zero ctx) value)))

(defun p69a5-negative-two (ctx)
  (p69a5-r-neg-value
   ctx
   (p69a5-r-add-value
    ctx
    (p69a5-r-one ctx)
    (p69a5-r-one ctx))))

;; Global continuity on the represented real line.

(defun-sk p69a5-continuity-neighborhood-p
    (ctx function x epsilon radius)
  (forall (y)
    (implies
     (and
      (p69a5-member-p
       (p69a5-r-carrier ctx) y)
      (p69a5-r-lt-p
       ctx
       (p69a5-r-abs-value
        ctx (p69a5-r-sub-value ctx y x))
       radius))
     (p69a5-r-lt-p
      ctx
      (p69a5-r-abs-value
       ctx
       (p69a5-r-sub-value
        ctx
        (p69a5-unary-value function y)
        (p69a5-unary-value function x)))
      epsilon))))

(defun-sk p69a5-continuity-radius-exists-p
    (ctx function x epsilon)
  (exists (radius)
    (and
     (p69a5-positive-real-p ctx radius)
     (p69a5-continuity-neighborhood-p
      ctx function x epsilon radius))))

(defun-sk p69a5-continuous-at-p
    (ctx function x)
  (forall (epsilon)
    (implies
     (p69a5-positive-real-p ctx epsilon)
     (p69a5-continuity-radius-exists-p
      ctx function x epsilon))))

(defun-sk p69a5-continuous-p (ctx function)
  (forall (x)
    (implies
     (p69a5-member-p
      (p69a5-r-carrier ctx) x)
     (p69a5-continuous-at-p
      ctx function x))))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun-sk p69a5-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p69a5-member-p
       (p69a5-r-carrier ctx) y)
      (p69a5-r-lt-p
       ctx
       (p69a5-r-abs-value
        ctx (p69a5-r-sub-value ctx y x))
       radius))
     (p69a5-r-le-p
      ctx
      (p69a5-r-abs-value
       ctx
       (p69a5-r-sub-value
        ctx
        (p69a5-r-sub-value
         ctx
         (p69a5-unary-value function y)
         (p69a5-unary-value function x))
        (p69a5-r-mul-value
         ctx derivative
         (p69a5-r-sub-value ctx y x))))
      (p69a5-r-mul-value
       ctx epsilon
       (p69a5-r-abs-value
        ctx (p69a5-r-sub-value ctx y x)))))))

(defun-sk p69a5-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p69a5-positive-real-p ctx radius)
     (p69a5-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p69a5-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p69a5-positive-real-p ctx epsilon)
     (p69a5-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p69a5-differentiable-at-p
    (ctx function x)
  (exists (derivative)
    (and
     (p69a5-member-p
      (p69a5-r-carrier ctx) derivative)
     (p69a5-has-derivative-at-p
      ctx function derivative x))))

(defun-sk p69a5-differentiable-p (ctx function)
  (forall (x)
    (implies
     (p69a5-member-p
      (p69a5-r-carrier ctx) x)
     (p69a5-differentiable-at-p
      ctx function x))))

;; The coupled differential equations, pointwise on the whole real line.

(defun p69a5-x-derivative-value
    (ctx y u point)
  (p69a5-r-add-value
   ctx
   (p69a5-r-mul-value
    ctx
    (p69a5-negative-two ctx)
    (p69a5-unary-value y point))
   (p69a5-unary-value u point)))

(defun p69a5-y-derivative-value
    (ctx x u point)
  (p69a5-r-add-value
   ctx
   (p69a5-r-mul-value
    ctx
    (p69a5-negative-two ctx)
    (p69a5-unary-value x point))
   (p69a5-unary-value u point)))

(defun-sk p69a5-ode-system-p (ctx x y u)
  (forall (point)
    (implies
     (p69a5-member-p
      (p69a5-r-carrier ctx) point)
     (and
      (p69a5-has-derivative-at-p
       ctx x
       (p69a5-x-derivative-value
        ctx y u point)
       point)
      (p69a5-has-derivative-at-p
       ctx y
       (p69a5-y-derivative-value
        ctx x u point)
       point)))))

(defun p69a5-solution-p
    (ctx x0 y0 time x y u)
  (and
   (p69a5-real-function-p
    (p69a5-r-carrier ctx) x)
   (p69a5-real-function-p
    (p69a5-r-carrier ctx) y)
   (p69a5-real-function-p
    (p69a5-r-carrier ctx) u)
   (p69a5-differentiable-p ctx x)
   (p69a5-differentiable-p ctx y)
   (p69a5-continuous-p ctx u)
   (p69a5-ode-system-p ctx x y u)
   (equal
    (p69a5-unary-value x (p69a5-r-zero ctx))
    x0)
   (equal
    (p69a5-unary-value y (p69a5-r-zero ctx))
    y0)
   (equal
    (p69a5-unary-value x time)
    (p69a5-r-zero ctx))
   (equal
    (p69a5-unary-value y time)
    (p69a5-r-zero ctx))))

(defun-sk p69a5-solution-exists-p
    (ctx x0 y0 time)
  (exists (x y u)
    (p69a5-solution-p
     ctx x0 y0 time x y u)))

(defun putnambench-putnam-1969-a5-statement
    (ctx x0 y0 time)
  (implies
   (and
    (p69a5-context-p ctx)
    (p69a5-member-p
     (p69a5-r-carrier ctx) x0)
    (p69a5-member-p
     (p69a5-r-carrier ctx) y0)
    (p69a5-positive-real-p ctx time))
   (iff
    (equal x0 y0)
    (p69a5-solution-exists-p
     ctx x0 y0 time))))

(value-triple :itpeval-statement-checked)
:q
