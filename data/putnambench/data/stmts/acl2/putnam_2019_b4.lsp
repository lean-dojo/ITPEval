;; Statement-only formalization of PutnamBench corpus artifact putnam_2019_b4:
;; the infimum of a square mixed difference is 2*ln(2)-1/2 for every twice
;; continuously differentiable real function satisfying the stated two
;; partial differential equations on x,y >= 1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its standard
;; exponential and logarithm. Tame APPLY$ objects retain arbitrary carriers,
;; operations, and real-valued functions, while DEFUN-SK keeps every
;; mathematical quantifier internal to the statement.
;;
;; Partial derivatives use their epsilon-delta linear-approximation
;; definition relative to the closed quadrant. Joint continuity of f and all
;; first and second partial derivative fields is an explicit C2 presentation.
;; The derivative fields are existentially quantified inside the hypothesis,
;; so they are not additional statement parameters. The conclusion gives the
;; exact infimum by its lower-bound and arbitrarily-close-witness properties.

(defun p19b4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p19b4-unary-value (operation x)
  (apply$ operation (list x)))

(defun p19b4-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p19b4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p19b4-member-p carrier x))))

(defun-sk p19b4-unary-real-function-p (carrier function)
  (forall (x)
    (implies
     (p19b4-member-p carrier x)
     (p19b4-member-p
      carrier
      (p19b4-unary-value function x)))))

(defun-sk p19b4-binary-real-function-p (carrier function)
  (forall (x y)
    (implies
     (and
      (p19b4-member-p carrier x)
      (p19b4-member-p carrier y))
     (p19b4-member-p
      carrier
      (p19b4-binary-value function x y)))))

(defun-sk p19b4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p19b4-member-p carrier x)
      (p19b4-member-p carrier y)
      (p19b4-member-p carrier z))
     (and
      (p19b4-member-p
       carrier (p19b4-binary-value add x y))
      (p19b4-member-p
       carrier (p19b4-binary-value multiply x y))
      (p19b4-member-p
       carrier (p19b4-unary-value negate x))
      (p19b4-member-p
       carrier (p19b4-unary-value inverse x))
      (equal
       (p19b4-binary-value
        add (p19b4-binary-value add x y) z)
       (p19b4-binary-value
        add x (p19b4-binary-value add y z)))
      (equal
       (p19b4-binary-value add x y)
       (p19b4-binary-value add y x))
      (equal
       (p19b4-binary-value add x zero)
       x)
      (equal
       (p19b4-binary-value
        add x (p19b4-unary-value negate x))
       zero)
      (equal
       (p19b4-binary-value
        multiply
        (p19b4-binary-value multiply x y)
        z)
       (p19b4-binary-value
        multiply
        x
        (p19b4-binary-value multiply y z)))
      (equal
       (p19b4-binary-value multiply x y)
       (p19b4-binary-value multiply y x))
      (equal
       (p19b4-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal
        (p19b4-unary-value inverse x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (p19b4-binary-value
         multiply x (p19b4-unary-value inverse x))
        one))
      (equal
       (p19b4-binary-value
        multiply x (p19b4-binary-value add y z))
       (p19b4-binary-value
        add
        (p19b4-binary-value multiply x y)
        (p19b4-binary-value multiply x z)))))))

(defun-sk p19b4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p19b4-member-p carrier x)
      (p19b4-member-p carrier y)
      (p19b4-member-p carrier z))
     (and
      (not (p19b4-binary-value less x x))
      (or
       (equal x y)
       (p19b4-binary-value less x y)
       (p19b4-binary-value less y x))
      (implies
       (and
        (p19b4-binary-value less x y)
        (p19b4-binary-value less y z))
       (p19b4-binary-value less x z))
      (implies
       (p19b4-binary-value less x y)
       (p19b4-binary-value
        less
        (p19b4-binary-value add x z)
        (p19b4-binary-value add y z)))
      (implies
       (and
        (p19b4-binary-value less zero x)
        (p19b4-binary-value less zero y))
       (p19b4-binary-value
        less
        zero
        (p19b4-binary-value multiply x y)))))))

(defun-sk p19b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p19b4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p19b4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p19b4-member-p carrier x)
      (apply$ set (list x)))
     (not
      (p19b4-binary-value less bound x)))))

(defun-sk p19b4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p19b4-member-p carrier bound)
     (p19b4-upper-bound-p
      carrier less set bound))))

(defun-sk p19b4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p19b4-member-p carrier bound)
      (p19b4-upper-bound-p
       carrier less set bound))
     (not
      (p19b4-binary-value
       less bound supremum)))))

(defun p19b4-supremum-p
    (carrier less set supremum)
  (and
   (p19b4-member-p carrier supremum)
   (p19b4-upper-bound-p
    carrier less set supremum)
   (p19b4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p19b4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p19b4-supremum-p
     carrier less set supremum)))

(defun-sk p19b4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p19b4-valid-set-p carrier set)
      (p19b4-set-nonempty-p carrier set)
      (p19b4-bounded-above-p
       carrier less set))
     (p19b4-has-supremum-p
      carrier less set))))

(defun p19b4-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p19b4-member-p carrier zero)
   (p19b4-member-p carrier one)
   (not (equal zero one))
   (p19b4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p19b4-order-laws-p
    carrier add multiply zero less)
   (p19b4-binary-value less zero one)
   (p19b4-dedekind-complete-p
    carrier less)))

;; Context layout:
;; (carrier zero one add multiply negate inverse less exponential logarithm).

(defun p19b4-r-carrier (ctx) (nth 0 ctx))
(defun p19b4-r-zero (ctx) (nth 1 ctx))
(defun p19b4-r-one (ctx) (nth 2 ctx))
(defun p19b4-r-add (ctx) (nth 3 ctx))
(defun p19b4-r-multiply (ctx) (nth 4 ctx))
(defun p19b4-r-negate (ctx) (nth 5 ctx))
(defun p19b4-r-inverse (ctx) (nth 6 ctx))
(defun p19b4-r-less (ctx) (nth 7 ctx))
(defun p19b4-r-exp (ctx) (nth 8 ctx))
(defun p19b4-r-log (ctx) (nth 9 ctx))

(defun p19b4-r-add-value (ctx x y)
  (p19b4-binary-value
   (p19b4-r-add ctx) x y))

(defun p19b4-r-multiply-value (ctx x y)
  (p19b4-binary-value
   (p19b4-r-multiply ctx) x y))

(defun p19b4-r-negate-value (ctx x)
  (p19b4-unary-value
   (p19b4-r-negate ctx) x))

(defun p19b4-r-inverse-value (ctx x)
  (p19b4-unary-value
   (p19b4-r-inverse ctx) x))

(defun p19b4-r-subtract-value (ctx x y)
  (p19b4-r-add-value
   ctx x (p19b4-r-negate-value ctx y)))

(defun p19b4-r-divide-value (ctx x y)
  (p19b4-r-multiply-value
   ctx x (p19b4-r-inverse-value ctx y)))

(defun p19b4-r-less-p (ctx x y)
  (if (p19b4-binary-value
       (p19b4-r-less ctx) x y)
      t
    nil))

(defun p19b4-r-less-equal-p (ctx x y)
  (not (p19b4-r-less-p ctx y x)))

(defun p19b4-r-absolute-value (ctx x)
  (if (p19b4-r-less-p
       ctx x (p19b4-r-zero ctx))
      (p19b4-r-negate-value ctx x)
    x))

(defun p19b4-positive-real-p (ctx x)
  (and
   (p19b4-member-p (p19b4-r-carrier ctx) x)
   (p19b4-r-less-p
    ctx (p19b4-r-zero ctx) x)))

(defun p19b4-r-two (ctx)
  (p19b4-r-add-value
   ctx (p19b4-r-one ctx) (p19b4-r-one ctx)))

(defun p19b4-r-half (ctx)
  (p19b4-r-inverse-value
   ctx (p19b4-r-two ctx)))

(defun p19b4-r-square (ctx x)
  (p19b4-r-multiply-value ctx x x))

(defun p19b4-at-least-one-p (ctx x)
  (and
   (p19b4-member-p (p19b4-r-carrier ctx) x)
   (p19b4-r-less-equal-p
    ctx (p19b4-r-one ctx) x)))

;; Unary derivatives, used to characterize the standard exponential.

(defun-sk p19b4-unary-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p19b4-member-p (p19b4-r-carrier ctx) y)
      (p19b4-r-less-p
       ctx
       (p19b4-r-absolute-value
        ctx (p19b4-r-subtract-value ctx y x))
       radius))
     (p19b4-r-less-equal-p
      ctx
      (p19b4-r-absolute-value
       ctx
       (p19b4-r-subtract-value
        ctx
        (p19b4-r-subtract-value
         ctx
         (p19b4-unary-value function y)
         (p19b4-unary-value function x))
        (p19b4-r-multiply-value
         ctx derivative
         (p19b4-r-subtract-value ctx y x))))
      (p19b4-r-multiply-value
       ctx epsilon
       (p19b4-r-absolute-value
        ctx
        (p19b4-r-subtract-value ctx y x)))))))

(defun-sk p19b4-unary-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p19b4-positive-real-p ctx radius)
     (p19b4-unary-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p19b4-unary-derivative-epsilon-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p19b4-positive-real-p ctx epsilon)
     (p19b4-unary-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun p19b4-has-unary-derivative-at-p
    (ctx function derivative x)
  (and
   (p19b4-member-p (p19b4-r-carrier ctx) x)
   (p19b4-member-p
    (p19b4-r-carrier ctx) derivative)
   (p19b4-unary-derivative-epsilon-p
    ctx function derivative x)))

(defun-sk p19b4-exponential-laws-p (ctx)
  (forall (x)
    (implies
     (p19b4-member-p (p19b4-r-carrier ctx) x)
     (and
      (p19b4-positive-real-p
       ctx
       (p19b4-unary-value
        (p19b4-r-exp ctx) x))
      (p19b4-has-unary-derivative-at-p
       ctx
       (p19b4-r-exp ctx)
       (p19b4-unary-value
        (p19b4-r-exp ctx) x)
       x)))))

(defun p19b4-exponential-function-p (ctx)
  (and
   (tamep-functionp (p19b4-r-exp ctx))
   (p19b4-unary-real-function-p
    (p19b4-r-carrier ctx)
    (p19b4-r-exp ctx))
   (equal
    (p19b4-unary-value
     (p19b4-r-exp ctx)
     (p19b4-r-zero ctx))
    (p19b4-r-one ctx))
   (p19b4-exponential-laws-p ctx)))

(defun-sk p19b4-logarithm-laws-p (ctx)
  (forall (x)
    (implies
     (p19b4-member-p (p19b4-r-carrier ctx) x)
     (and
      (equal
       (p19b4-unary-value
        (p19b4-r-log ctx)
        (p19b4-unary-value
         (p19b4-r-exp ctx) x))
       x)
      (implies
       (p19b4-positive-real-p ctx x)
       (equal
        (p19b4-unary-value
         (p19b4-r-exp ctx)
         (p19b4-unary-value
          (p19b4-r-log ctx) x))
        x))))))

(defun p19b4-logarithm-function-p (ctx)
  (and
   (tamep-functionp (p19b4-r-log ctx))
   (p19b4-unary-real-function-p
    (p19b4-r-carrier ctx)
    (p19b4-r-log ctx))
   (p19b4-logarithm-laws-p ctx)))

(defun p19b4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 10)
   (p19b4-real-field-p
    (p19b4-r-carrier ctx)
    (p19b4-r-zero ctx)
    (p19b4-r-one ctx)
    (p19b4-r-add ctx)
    (p19b4-r-multiply ctx)
    (p19b4-r-negate ctx)
    (p19b4-r-inverse ctx)
    (p19b4-r-less ctx))
   (p19b4-exponential-function-p ctx)
   (p19b4-logarithm-function-p ctx)))

;; Joint continuity on the closed quadrant [1,infinity)^2.

(defun-sk p19b4-continuity-neighborhood-p
    (ctx function x y epsilon radius)
  (forall (u v)
    (implies
     (and
      (p19b4-at-least-one-p ctx u)
      (p19b4-at-least-one-p ctx v)
      (p19b4-r-less-p
       ctx
       (p19b4-r-absolute-value
        ctx (p19b4-r-subtract-value ctx u x))
       radius)
      (p19b4-r-less-p
       ctx
       (p19b4-r-absolute-value
        ctx (p19b4-r-subtract-value ctx v y))
       radius))
     (p19b4-r-less-p
      ctx
      (p19b4-r-absolute-value
       ctx
       (p19b4-r-subtract-value
        ctx
        (p19b4-binary-value function u v)
        (p19b4-binary-value function x y)))
      epsilon))))

(defun-sk p19b4-continuity-radius-exists-p
    (ctx function x y epsilon)
  (exists (radius)
    (and
     (p19b4-positive-real-p ctx radius)
     (p19b4-continuity-neighborhood-p
      ctx function x y epsilon radius))))

(defun-sk p19b4-continuous-at-p
    (ctx function x y)
  (forall (epsilon)
    (implies
     (p19b4-positive-real-p ctx epsilon)
     (p19b4-continuity-radius-exists-p
      ctx function x y epsilon))))

(defun-sk p19b4-continuous-on-quadrant-p
    (ctx function)
  (forall (x y)
    (implies
     (and
      (p19b4-at-least-one-p ctx x)
      (p19b4-at-least-one-p ctx y))
     (p19b4-continuous-at-p
      ctx function x y))))

;; First-coordinate partial derivative relative to the quadrant.

(defun-sk p19b4-partial-x-neighborhood-p
    (ctx function derivative x y epsilon radius)
  (forall (u)
    (implies
     (and
      (p19b4-at-least-one-p ctx u)
      (p19b4-r-less-p
       ctx
       (p19b4-r-absolute-value
        ctx (p19b4-r-subtract-value ctx u x))
       radius))
     (p19b4-r-less-equal-p
      ctx
      (p19b4-r-absolute-value
       ctx
       (p19b4-r-subtract-value
        ctx
        (p19b4-r-subtract-value
         ctx
         (p19b4-binary-value function u y)
         (p19b4-binary-value function x y))
        (p19b4-r-multiply-value
         ctx
         (p19b4-binary-value derivative x y)
         (p19b4-r-subtract-value ctx u x))))
      (p19b4-r-multiply-value
       ctx epsilon
       (p19b4-r-absolute-value
        ctx
        (p19b4-r-subtract-value ctx u x)))))))

(defun-sk p19b4-partial-x-radius-exists-p
    (ctx function derivative x y epsilon)
  (exists (radius)
    (and
     (p19b4-positive-real-p ctx radius)
     (p19b4-partial-x-neighborhood-p
      ctx function derivative x y epsilon radius))))

(defun-sk p19b4-partial-x-epsilon-p
    (ctx function derivative x y)
  (forall (epsilon)
    (implies
     (p19b4-positive-real-p ctx epsilon)
     (p19b4-partial-x-radius-exists-p
      ctx function derivative x y epsilon))))

(defun-sk p19b4-partial-x-relation-p
    (ctx function derivative)
  (forall (x y)
    (implies
     (and
      (p19b4-at-least-one-p ctx x)
      (p19b4-at-least-one-p ctx y))
     (p19b4-partial-x-epsilon-p
      ctx function derivative x y))))

;; Second-coordinate partial derivative relative to the quadrant.

(defun-sk p19b4-partial-y-neighborhood-p
    (ctx function derivative x y epsilon radius)
  (forall (v)
    (implies
     (and
      (p19b4-at-least-one-p ctx v)
      (p19b4-r-less-p
       ctx
       (p19b4-r-absolute-value
        ctx (p19b4-r-subtract-value ctx v y))
       radius))
     (p19b4-r-less-equal-p
      ctx
      (p19b4-r-absolute-value
       ctx
       (p19b4-r-subtract-value
        ctx
        (p19b4-r-subtract-value
         ctx
         (p19b4-binary-value function x v)
         (p19b4-binary-value function x y))
        (p19b4-r-multiply-value
         ctx
         (p19b4-binary-value derivative x y)
         (p19b4-r-subtract-value ctx v y))))
      (p19b4-r-multiply-value
       ctx epsilon
       (p19b4-r-absolute-value
        ctx
        (p19b4-r-subtract-value ctx v y)))))))

(defun-sk p19b4-partial-y-radius-exists-p
    (ctx function derivative x y epsilon)
  (exists (radius)
    (and
     (p19b4-positive-real-p ctx radius)
     (p19b4-partial-y-neighborhood-p
      ctx function derivative x y epsilon radius))))

(defun-sk p19b4-partial-y-epsilon-p
    (ctx function derivative x y)
  (forall (epsilon)
    (implies
     (p19b4-positive-real-p ctx epsilon)
     (p19b4-partial-y-radius-exists-p
      ctx function derivative x y epsilon))))

(defun-sk p19b4-partial-y-relation-p
    (ctx function derivative)
  (forall (x y)
    (implies
     (and
      (p19b4-at-least-one-p ctx x)
      (p19b4-at-least-one-p ctx y))
     (p19b4-partial-y-epsilon-p
      ctx function derivative x y))))

(defun-sk p19b4-pde-p
    (ctx f-x f-y f-xx f-yy)
  (forall (x y)
    (implies
     (and
      (p19b4-at-least-one-p ctx x)
      (p19b4-at-least-one-p ctx y))
     (let* ((xy
             (p19b4-r-multiply-value ctx x y))
            (first-left
             (p19b4-r-add-value
              ctx
              (p19b4-r-multiply-value
               ctx x (p19b4-binary-value f-x x y))
              (p19b4-r-multiply-value
               ctx y (p19b4-binary-value f-y x y))))
            (first-right
             (p19b4-r-multiply-value
              ctx
              xy
              (p19b4-unary-value
               (p19b4-r-log ctx) xy)))
            (second-left
             (p19b4-r-add-value
              ctx
              (p19b4-r-multiply-value
               ctx
               (p19b4-r-square ctx x)
               (p19b4-binary-value f-xx x y))
              (p19b4-r-multiply-value
               ctx
               (p19b4-r-square ctx y)
               (p19b4-binary-value f-yy x y)))))
       (and
        (equal first-left first-right)
        (equal second-left xy))))))

(defun p19b4-c2-presentation-p
    (ctx f f-x f-y f-xx f-xy f-yx f-yy)
  (and
   (tamep-functionp f-x)
   (tamep-functionp f-y)
   (tamep-functionp f-xx)
   (tamep-functionp f-xy)
   (tamep-functionp f-yx)
   (tamep-functionp f-yy)
   (p19b4-binary-real-function-p
    (p19b4-r-carrier ctx) f-x)
   (p19b4-binary-real-function-p
    (p19b4-r-carrier ctx) f-y)
   (p19b4-binary-real-function-p
    (p19b4-r-carrier ctx) f-xx)
   (p19b4-binary-real-function-p
    (p19b4-r-carrier ctx) f-xy)
   (p19b4-binary-real-function-p
    (p19b4-r-carrier ctx) f-yx)
   (p19b4-binary-real-function-p
    (p19b4-r-carrier ctx) f-yy)
   (p19b4-continuous-on-quadrant-p ctx f)
   (p19b4-continuous-on-quadrant-p ctx f-x)
   (p19b4-continuous-on-quadrant-p ctx f-y)
   (p19b4-continuous-on-quadrant-p ctx f-xx)
   (p19b4-continuous-on-quadrant-p ctx f-xy)
   (p19b4-continuous-on-quadrant-p ctx f-yx)
   (p19b4-continuous-on-quadrant-p ctx f-yy)
   (p19b4-partial-x-relation-p ctx f f-x)
   (p19b4-partial-y-relation-p ctx f f-y)
   (p19b4-partial-x-relation-p ctx f-x f-xx)
   (p19b4-partial-y-relation-p ctx f-x f-xy)
   (p19b4-partial-x-relation-p ctx f-y f-yx)
   (p19b4-partial-y-relation-p ctx f-y f-yy)
   (p19b4-pde-p ctx f-x f-y f-xx f-yy)))

(defun-sk p19b4-hypothesis-p (ctx f)
  (exists (f-x f-y f-xx f-xy f-yx f-yy)
    (p19b4-c2-presentation-p
     ctx f f-x f-y f-xx f-xy f-yx f-yy)))

(defun p19b4-cross-difference (ctx f s)
  (let ((s-plus-one
         (p19b4-r-add-value
          ctx s (p19b4-r-one ctx))))
    (p19b4-r-add-value
     ctx
     (p19b4-r-subtract-value
      ctx
      (p19b4-binary-value
       f s-plus-one s-plus-one)
      (p19b4-binary-value
       f s-plus-one s))
     (p19b4-r-subtract-value
      ctx
      (p19b4-binary-value f s s)
      (p19b4-binary-value
       f s s-plus-one)))))

(defun p19b4-solution (ctx)
  (p19b4-r-subtract-value
   ctx
   (p19b4-r-multiply-value
    ctx
    (p19b4-r-two ctx)
    (p19b4-unary-value
     (p19b4-r-log ctx)
     (p19b4-r-two ctx)))
   (p19b4-r-half ctx)))

(defun-sk p19b4-lower-bound-p (ctx f)
  (forall (s)
    (implies
     (p19b4-at-least-one-p ctx s)
     (p19b4-r-less-equal-p
      ctx
      (p19b4-solution ctx)
      (p19b4-cross-difference ctx f s)))))

(defun-sk p19b4-close-value-exists-p
    (ctx f epsilon)
  (exists (s)
    (and
     (p19b4-at-least-one-p ctx s)
     (p19b4-r-less-p
      ctx
      (p19b4-cross-difference ctx f s)
      (p19b4-r-add-value
       ctx
       (p19b4-solution ctx)
       epsilon)))))

(defun-sk p19b4-arbitrarily-close-p (ctx f)
  (forall (epsilon)
    (implies
     (p19b4-positive-real-p ctx epsilon)
     (p19b4-close-value-exists-p
      ctx f epsilon))))

(defun p19b4-infimum-value-p (ctx f)
  (and
   (p19b4-lower-bound-p ctx f)
   (p19b4-arbitrarily-close-p ctx f)))

(defun putnambench-putnam-2019-b4-statement
    (ctx f)
  (implies
   (and
    (p19b4-context-p ctx)
    (tamep-functionp f)
    (p19b4-binary-real-function-p
     (p19b4-r-carrier ctx) f)
    (p19b4-hypothesis-p ctx f))
   (p19b4-infimum-value-p ctx f)))

(value-triple :itpeval-statement-checked)
:q
