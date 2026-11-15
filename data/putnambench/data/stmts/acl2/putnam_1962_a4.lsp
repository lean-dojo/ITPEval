;; Statement-only formalization of PutnamBench corpus artifact putnam_1962_a4:
;; a twice-differentiable real function bounded in absolute value by 1,
;; whose second derivative is likewise bounded by 1 on an interval of length
;; at least 2, has first derivative bounded by 2 there. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context below explicitly presents a Dedekind-complete ordered field,
;; hence the real field up to ordered-field isomorphism. Conservative DEFSTUB
;; interfaces represent arbitrary carrier predicates, subsets, operations,
;; and functions. DEFUN-SK keeps all unbounded mathematical quantifiers,
;; including the first- and second-derivative functions, internal to the
;; statement. Differentiation is expanded by its epsilon-delta definition.

(defstub p62a4-member-p (carrier value) t)

(defstub p62a4-set-member-p (set value) t)

(defstub p62a4-unary-value (function value) t)

(defstub p62a4-binary-value (function left right) t)

(defun-sk p62a4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (p62a4-set-member-p set x)
     (p62a4-member-p carrier x))))

(defun-sk p62a4-real-function-p (carrier function)
  (forall (x)
    (implies
     (p62a4-member-p carrier x)
     (p62a4-member-p
      carrier
      (p62a4-unary-value function x)))))

(defun-sk p62a4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p62a4-member-p carrier x)
      (p62a4-member-p carrier y)
      (p62a4-member-p carrier z))
     (and
      (p62a4-member-p
       carrier (p62a4-binary-value add x y))
      (p62a4-member-p
       carrier (p62a4-binary-value multiply x y))
      (p62a4-member-p
       carrier (p62a4-unary-value negate x))
      (p62a4-member-p
       carrier (p62a4-unary-value inverse x))
      (equal
       (p62a4-binary-value
        add (p62a4-binary-value add x y) z)
       (p62a4-binary-value
        add x (p62a4-binary-value add y z)))
      (equal
       (p62a4-binary-value add x y)
       (p62a4-binary-value add y x))
      (equal
       (p62a4-binary-value add x zero)
       x)
      (equal
       (p62a4-binary-value
        add x (p62a4-unary-value negate x))
       zero)
      (equal
       (p62a4-binary-value
        multiply (p62a4-binary-value multiply x y) z)
       (p62a4-binary-value
        multiply x (p62a4-binary-value multiply y z)))
      (equal
       (p62a4-binary-value multiply x y)
       (p62a4-binary-value multiply y x))
      (equal
       (p62a4-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal (p62a4-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p62a4-binary-value
         multiply x (p62a4-unary-value inverse x))
        one))
      (equal
       (p62a4-binary-value
        multiply x (p62a4-binary-value add y z))
       (p62a4-binary-value
        add
        (p62a4-binary-value multiply x y)
        (p62a4-binary-value multiply x z)))))))

(defun-sk p62a4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p62a4-member-p carrier x)
      (p62a4-member-p carrier y)
      (p62a4-member-p carrier z))
     (and
      (not (p62a4-binary-value less x x))
      (or
       (equal x y)
       (p62a4-binary-value less x y)
       (p62a4-binary-value less y x))
      (implies
       (and
        (p62a4-binary-value less x y)
        (p62a4-binary-value less y z))
       (p62a4-binary-value less x z))
      (implies
       (p62a4-binary-value less x y)
       (p62a4-binary-value
        less
        (p62a4-binary-value add x z)
        (p62a4-binary-value add y z)))
      (implies
       (and
        (p62a4-binary-value less zero x)
        (p62a4-binary-value less zero y))
       (p62a4-binary-value
        less
        zero
        (p62a4-binary-value multiply x y)))))))

(defun-sk p62a4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p62a4-member-p carrier x)
     (p62a4-set-member-p set x))))

(defun-sk p62a4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p62a4-member-p carrier x)
      (p62a4-set-member-p set x))
     (not (p62a4-binary-value less bound x)))))

(defun-sk p62a4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p62a4-member-p carrier bound)
     (p62a4-upper-bound-p
      carrier less set bound))))

(defun-sk p62a4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p62a4-member-p carrier bound)
      (p62a4-upper-bound-p carrier less set bound))
     (not (p62a4-binary-value less bound supremum)))))

(defun p62a4-supremum-p
    (carrier less set supremum)
  (and
   (p62a4-member-p carrier supremum)
   (p62a4-upper-bound-p carrier less set supremum)
   (p62a4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p62a4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p62a4-supremum-p
     carrier less set supremum)))

(defun-sk p62a4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (p62a4-valid-set-p carrier set)
      (p62a4-set-nonempty-p carrier set)
      (p62a4-bounded-above-p carrier less set))
     (p62a4-has-supremum-p carrier less set))))

(defun p62a4-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (p62a4-member-p carrier zero)
   (p62a4-member-p carrier one)
   (not (equal zero one))
   (p62a4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p62a4-order-laws-p
    carrier add multiply zero less)
   (p62a4-binary-value less zero one)
   (p62a4-dedekind-complete-p carrier less)))

;; An eight-entry context contains the real carrier, 0, 1, addition,
;; multiplication, additive negation, inversion, and strict order.

(defun p62a4-r-carrier (ctx)
  (nth 0 ctx))

(defun p62a4-r-zero (ctx)
  (nth 1 ctx))

(defun p62a4-r-one (ctx)
  (nth 2 ctx))

(defun p62a4-r-add (ctx)
  (nth 3 ctx))

(defun p62a4-r-multiply (ctx)
  (nth 4 ctx))

(defun p62a4-r-negate (ctx)
  (nth 5 ctx))

(defun p62a4-r-inverse (ctx)
  (nth 6 ctx))

(defun p62a4-r-less (ctx)
  (nth 7 ctx))

(defun p62a4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p62a4-real-field-p
    (p62a4-r-carrier ctx)
    (p62a4-r-zero ctx)
    (p62a4-r-one ctx)
    (p62a4-r-add ctx)
    (p62a4-r-multiply ctx)
    (p62a4-r-negate ctx)
    (p62a4-r-inverse ctx)
    (p62a4-r-less ctx))))

(defun p62a4-r-add-value (ctx left right)
  (p62a4-binary-value
   (p62a4-r-add ctx) left right))

(defun p62a4-r-multiply-value (ctx left right)
  (p62a4-binary-value
   (p62a4-r-multiply ctx) left right))

(defun p62a4-r-negate-value (ctx value)
  (p62a4-unary-value
   (p62a4-r-negate ctx) value))

(defun p62a4-r-subtract-value (ctx left right)
  (p62a4-r-add-value
   ctx left (p62a4-r-negate-value ctx right)))

(defun p62a4-r-less-p (ctx left right)
  (if (p62a4-binary-value
       (p62a4-r-less ctx) left right)
      t
    nil))

(defun p62a4-r-less-equal-p (ctx left right)
  (not (p62a4-r-less-p ctx right left)))

(defun p62a4-r-absolute-value (ctx value)
  (if (p62a4-r-less-p
       ctx value (p62a4-r-zero ctx))
      (p62a4-r-negate-value ctx value)
    value))

(defun p62a4-positive-real-p (ctx value)
  (and
   (p62a4-member-p (p62a4-r-carrier ctx) value)
   (p62a4-r-less-p
    ctx (p62a4-r-zero ctx) value)))

(defun p62a4-r-two (ctx)
  (p62a4-r-add-value
   ctx (p62a4-r-one ctx) (p62a4-r-one ctx)))

(defun p62a4-icc-member-p (ctx left right x)
  (and
   (p62a4-member-p (p62a4-r-carrier ctx) x)
   (p62a4-r-less-equal-p ctx left x)
   (p62a4-r-less-equal-p ctx x right)))

;; HasDerivAt in epsilon-delta form:
;; |g(z) - g(x) - d (z - x)| <= epsilon |z - x| near x.

(defun-sk p62a4-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (z)
    (implies
     (and
      (p62a4-member-p (p62a4-r-carrier ctx) z)
      (p62a4-r-less-p
       ctx
       (p62a4-r-absolute-value
        ctx (p62a4-r-subtract-value ctx z x))
       radius))
     (p62a4-r-less-equal-p
      ctx
      (p62a4-r-absolute-value
       ctx
       (p62a4-r-subtract-value
        ctx
        (p62a4-r-subtract-value
         ctx
         (p62a4-unary-value function z)
         (p62a4-unary-value function x))
        (p62a4-r-multiply-value
         ctx
         derivative
         (p62a4-r-subtract-value ctx z x))))
      (p62a4-r-multiply-value
       ctx
       epsilon
       (p62a4-r-absolute-value
        ctx (p62a4-r-subtract-value ctx z x)))))))

(defun-sk p62a4-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p62a4-positive-real-p ctx radius)
     (p62a4-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p62a4-has-derivative-at-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p62a4-positive-real-p ctx epsilon)
     (p62a4-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun-sk p62a4-derivative-function-p
    (ctx function derivative-function)
  (forall (x)
    (implies
     (p62a4-member-p (p62a4-r-carrier ctx) x)
     (p62a4-has-derivative-at-p
      ctx
      function
      (p62a4-unary-value derivative-function x)
      x))))

(defun-sk p62a4-absolute-bound-on-icc-p
    (ctx function left right bound)
  (forall (x)
    (implies
     (p62a4-icc-member-p ctx left right x)
     (p62a4-r-less-equal-p
      ctx
      (p62a4-r-absolute-value
       ctx (p62a4-unary-value function x))
      bound))))

(defun p62a4-interval-length-at-least-two-p
    (ctx left right)
  (p62a4-r-less-equal-p
   ctx
   (p62a4-r-two ctx)
   (p62a4-r-subtract-value ctx right left)))

;; The quantified derivative functions are internal witnesses for deriv f and
;; deriv (deriv f). Derivatives are unique in an ordered field, so universally
;; quantifying these witnesses in the implication is equivalent to using the
;; source provers' canonical derivative operators.

(defun-sk putnambench-putnam-1962-a4-statement
    (ctx function left right)
  (forall (first-derivative second-derivative)
    (implies
     (and
      (p62a4-context-p ctx)
      (p62a4-member-p (p62a4-r-carrier ctx) left)
      (p62a4-member-p (p62a4-r-carrier ctx) right)
      (p62a4-real-function-p
       (p62a4-r-carrier ctx) function)
      (p62a4-real-function-p
       (p62a4-r-carrier ctx) first-derivative)
      (p62a4-real-function-p
       (p62a4-r-carrier ctx) second-derivative)
      (p62a4-derivative-function-p
       ctx function first-derivative)
      (p62a4-derivative-function-p
       ctx first-derivative second-derivative)
      (p62a4-absolute-bound-on-icc-p
       ctx function left right (p62a4-r-one ctx))
      (p62a4-absolute-bound-on-icc-p
       ctx second-derivative left right (p62a4-r-one ctx))
      (p62a4-interval-length-at-least-two-p
       ctx left right))
     (p62a4-absolute-bound-on-icc-p
      ctx
      first-derivative
      left
      right
      (p62a4-r-two ctx)))))

(value-triple :itpeval-statement-checked)
:q
