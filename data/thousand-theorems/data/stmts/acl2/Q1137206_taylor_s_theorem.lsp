;; Statement-only formalization of thousand-theorems corpus artifact Q1137206,
;; "Taylor's theorem": the Lagrange and Cauchy remainder formulas for a
;; real-valued function continuously differentiable through order n on a
;; closed interval and differentiable once more on its interior.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ objects represent the real carrier, its operations, every
;; subset used by completeness, the arbitrary source function, and its
;; derivative family. All quantifiers remain direct DEFUN-SK quantifiers, so
;; no finite table or opaque set/function tag replaces an extensional object.

(defun q1137206-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun q1137206-unary-value (function argument)
  (apply$ function (list argument)))

(defun q1137206-binary-value (function left right)
  (apply$ function (list left right)))

;; A scalar context consists of a carrier predicate, zero, one, addition,
;; multiplication, negation, inversion, and strict order.

(defun q1137206-r-carrier (ctx) (nth 0 ctx))
(defun q1137206-r-zero (ctx) (nth 1 ctx))
(defun q1137206-r-one (ctx) (nth 2 ctx))
(defun q1137206-r-add (ctx) (nth 3 ctx))
(defun q1137206-r-multiply (ctx) (nth 4 ctx))
(defun q1137206-r-negate (ctx) (nth 5 ctx))
(defun q1137206-r-inverse (ctx) (nth 6 ctx))
(defun q1137206-r-less (ctx) (nth 7 ctx))

(defun q1137206-real-p (ctx value)
  (q1137206-member-p (q1137206-r-carrier ctx) value))

(defun q1137206-zero (ctx)
  (q1137206-r-zero ctx))

(defun q1137206-one (ctx)
  (q1137206-r-one ctx))

(defun q1137206-add (ctx left right)
  (q1137206-binary-value
   (q1137206-r-add ctx) left right))

(defun q1137206-multiply (ctx left right)
  (q1137206-binary-value
   (q1137206-r-multiply ctx) left right))

(defun q1137206-negate (ctx value)
  (q1137206-unary-value
   (q1137206-r-negate ctx) value))

(defun q1137206-inverse (ctx value)
  (q1137206-unary-value
   (q1137206-r-inverse ctx) value))

(defun q1137206-less (ctx left right)
  (if
      (q1137206-binary-value
       (q1137206-r-less ctx) left right)
      t nil))

(defun q1137206-set-member-p (ctx set value)
  (declare (ignore ctx))
  (q1137206-member-p set value))

(defun q1137206-function-value (function point)
  (q1137206-unary-value function point))

(defun q1137206-derivative-value
    (derivatives derivative-order point)
  (q1137206-binary-value
   derivatives derivative-order point))

(defun q1137206-subtract (ctx left right)
  (q1137206-add ctx left (q1137206-negate ctx right)))

(defun q1137206-divide (ctx numerator denominator)
  (q1137206-multiply
   ctx numerator (q1137206-inverse ctx denominator)))

(defun q1137206-less-equal-p (ctx left right)
  (not (q1137206-less ctx right left)))

(defun q1137206-absolute-value (ctx value)
  (if (q1137206-less ctx value (q1137206-zero ctx))
      (q1137206-negate ctx value)
    value))

(defun q1137206-positive-real-p (ctx value)
  (and
   (q1137206-real-p ctx value)
   (q1137206-less ctx (q1137206-zero ctx) value)))

;; A Dedekind-complete ordered field, hence a presentation of the real field.

(defun-sk q1137206-field-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (q1137206-real-p ctx a)
      (q1137206-real-p ctx b)
      (q1137206-real-p ctx c))
     (let* ((ab-add (q1137206-add ctx a b))
            (bc-add (q1137206-add ctx b c))
            (ab-mul (q1137206-multiply ctx a b))
            (bc-mul (q1137206-multiply ctx b c))
            (neg-a (q1137206-negate ctx a))
            (inv-a (q1137206-inverse ctx a))
            (zero (q1137206-zero ctx))
            (one (q1137206-one ctx)))
       (and
        (q1137206-real-p ctx ab-add)
        (q1137206-real-p ctx ab-mul)
        (q1137206-real-p ctx neg-a)
        (q1137206-real-p ctx inv-a)
        (equal
         (q1137206-add ctx ab-add c)
         (q1137206-add ctx a bc-add))
        (equal ab-add (q1137206-add ctx b a))
        (equal (q1137206-add ctx a zero) a)
        (equal (q1137206-add ctx a neg-a) zero)
        (equal
         (q1137206-multiply ctx ab-mul c)
         (q1137206-multiply ctx a bc-mul))
        (equal ab-mul (q1137206-multiply ctx b a))
        (equal (q1137206-multiply ctx a one) a)
        (implies
         (equal a zero)
         (equal inv-a zero))
        (implies
         (not (equal a zero))
         (equal (q1137206-multiply ctx a inv-a) one))
        (equal
         (q1137206-multiply ctx a bc-add)
         (q1137206-add
          ctx
          (q1137206-multiply ctx a b)
          (q1137206-multiply ctx a c))))))))

(defun-sk q1137206-order-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (q1137206-real-p ctx a)
      (q1137206-real-p ctx b)
      (q1137206-real-p ctx c))
     (and
      (not (q1137206-less ctx a a))
      (or
       (q1137206-less ctx a b)
       (equal a b)
       (q1137206-less ctx b a))
      (implies
       (and
        (q1137206-less ctx a b)
        (q1137206-less ctx b c))
       (q1137206-less ctx a c))
      (implies
       (q1137206-less ctx a b)
       (q1137206-less
        ctx
        (q1137206-add ctx a c)
        (q1137206-add ctx b c)))
      (implies
       (and
        (q1137206-less ctx (q1137206-zero ctx) a)
        (q1137206-less ctx (q1137206-zero ctx) b))
       (q1137206-less
        ctx
        (q1137206-zero ctx)
        (q1137206-multiply ctx a b)))))))

(defun-sk q1137206-valid-set-p (ctx set)
  (forall (value)
    (implies
     (q1137206-set-member-p ctx set value)
     (q1137206-real-p ctx value))))

(defun q1137206-extensional-set-p (ctx set)
  (and
   (tamep-functionp set)
   (q1137206-valid-set-p ctx set)))

(defun-sk q1137206-set-nonempty-p (ctx set)
  (exists (value)
    (and
     (q1137206-real-p ctx value)
     (q1137206-set-member-p ctx set value))))

(defun-sk q1137206-upper-bound-p (ctx set upper)
  (forall (value)
    (implies
     (and
      (q1137206-real-p ctx value)
      (q1137206-set-member-p ctx set value))
     (not (q1137206-less ctx upper value)))))

(defun-sk q1137206-bounded-above-p (ctx set)
  (exists (upper)
    (and
     (q1137206-real-p ctx upper)
     (q1137206-upper-bound-p ctx set upper))))

(defun-sk q1137206-least-upper-bound-p
    (ctx set supremum)
  (forall (upper)
    (implies
     (and
      (q1137206-real-p ctx upper)
      (q1137206-upper-bound-p ctx set upper))
     (not (q1137206-less ctx upper supremum)))))

(defun q1137206-is-supremum-p (ctx set supremum)
  (and
   (q1137206-real-p ctx supremum)
   (q1137206-upper-bound-p ctx set supremum)
   (q1137206-least-upper-bound-p ctx set supremum)))

(defun-sk q1137206-has-supremum-p (ctx set)
  (exists (supremum)
    (q1137206-is-supremum-p ctx set supremum)))

(defun-sk q1137206-completeness-p (ctx)
  (forall (set)
    (implies
     (and
      (q1137206-extensional-set-p ctx set)
      (q1137206-set-nonempty-p ctx set)
      (q1137206-bounded-above-p ctx set))
     (q1137206-has-supremum-p ctx set))))

(defun q1137206-real-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (q1137206-r-carrier ctx))
   (tamep-functionp (q1137206-r-add ctx))
   (tamep-functionp (q1137206-r-multiply ctx))
   (tamep-functionp (q1137206-r-negate ctx))
   (tamep-functionp (q1137206-r-inverse ctx))
   (tamep-functionp (q1137206-r-less ctx))
   (q1137206-real-p ctx (q1137206-zero ctx))
   (q1137206-real-p ctx (q1137206-one ctx))
   (not
    (equal
     (q1137206-zero ctx)
     (q1137206-one ctx)))
   (q1137206-field-laws-p ctx)
   (q1137206-order-laws-p ctx)
   (q1137206-completeness-p ctx)
   (q1137206-less
    ctx (q1137206-zero ctx) (q1137206-one ctx))))

;; Natural numbers embedded in the abstract real field.

(defun q1137206-real-natural (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1137206-zero ctx)
    (q1137206-add
     ctx
     (q1137206-one ctx)
     (q1137206-real-natural ctx (- n 1)))))

(defun q1137206-power (ctx base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q1137206-one ctx)
    (q1137206-multiply
     ctx
     base
     (q1137206-power ctx base (- exponent 1)))))

(defun q1137206-factorial (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1137206-one ctx)
    (q1137206-multiply
     ctx
     (q1137206-real-natural ctx n)
     (q1137206-factorial ctx (- n 1)))))

;; The intervals Icc x0 x and Ioo x0 x.

(defun q1137206-in-closed-interval-p
    (ctx x0 x point)
  (and
   (q1137206-real-p ctx point)
   (not (q1137206-less ctx point x0))
   (not (q1137206-less ctx x point))))

(defun q1137206-in-open-interval-p
    (ctx x0 x point)
  (and
   (q1137206-real-p ctx point)
   (q1137206-less ctx x0 point)
   (q1137206-less ctx point x)))

;; Arbitrary real-valued functions and explicitly tied iterated derivatives.

(defun-sk q1137206-real-function-p (ctx function)
  (forall (point)
    (implies
     (q1137206-real-p ctx point)
     (q1137206-real-p
      ctx (q1137206-function-value function point)))))

(defun q1137206-extensional-real-function-p
    (ctx function)
  (and
   (tamep-functionp function)
   (q1137206-real-function-p ctx function)))

(defun-sk q1137206-derivative-order-real-p
    (ctx derivatives derivative-order)
  (forall (point)
    (implies
     (q1137206-real-p ctx point)
     (q1137206-real-p
      ctx
      (q1137206-derivative-value
       derivatives derivative-order point)))))

(defun-sk q1137206-derivative-family-p
    (ctx derivatives maximum-order)
  (forall (derivative-order)
    (implies
     (and
      (natp derivative-order)
      (<= derivative-order maximum-order))
     (q1137206-derivative-order-real-p
      ctx derivatives derivative-order))))

(defun q1137206-extensional-derivative-family-p
    (ctx derivatives maximum-order)
  (and
   (tamep-functionp derivatives)
   (q1137206-derivative-family-p
    ctx derivatives maximum-order)))

(defun-sk q1137206-order-zero-is-function-p
    (ctx function derivatives)
  (forall (point)
    (implies
     (q1137206-real-p ctx point)
     (equal
      (q1137206-derivative-value derivatives 0 point)
      (q1137206-function-value function point)))))

;; Epsilon-delta continuity of a derivative row on the closed interval.

(defun-sk q1137206-continuity-radius-p
    (ctx derivatives derivative-order x0 x point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (q1137206-in-closed-interval-p
       ctx x0 x nearby)
      (q1137206-less
       ctx
       (q1137206-absolute-value
        ctx (q1137206-subtract ctx nearby point))
       radius))
     (q1137206-less
      ctx
      (q1137206-absolute-value
       ctx
       (q1137206-subtract
        ctx
        (q1137206-derivative-value
         derivatives derivative-order nearby)
        (q1137206-derivative-value
         derivatives derivative-order point)))
      epsilon))))

(defun-sk q1137206-continuity-radius-exists-p
    (ctx derivatives derivative-order x0 x point epsilon)
  (exists (radius)
    (and
     (q1137206-positive-real-p ctx radius)
     (q1137206-continuity-radius-p
      ctx derivatives derivative-order
      x0 x point epsilon radius))))

(defun-sk q1137206-continuous-within-at-p
    (ctx derivatives derivative-order x0 x point)
  (forall (epsilon)
    (implies
     (q1137206-positive-real-p ctx epsilon)
     (q1137206-continuity-radius-exists-p
      ctx derivatives derivative-order
      x0 x point epsilon))))

(defun-sk q1137206-continuous-on-closed-interval-p
    (ctx derivatives derivative-order x0 x)
  (forall (point)
    (implies
     (q1137206-in-closed-interval-p ctx x0 x point)
     (q1137206-continuous-within-at-p
      ctx derivatives derivative-order x0 x point))))

;; HasDerivWithinAt in epsilon-delta form, restricted to Icc x0 x.

(defun-sk q1137206-derivative-radius-p
    (ctx derivatives derivative-order derivative
         x0 x point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (q1137206-in-closed-interval-p
       ctx x0 x nearby)
      (q1137206-less
       ctx
       (q1137206-absolute-value
        ctx (q1137206-subtract ctx nearby point))
       radius))
     (q1137206-less-equal-p
      ctx
      (q1137206-absolute-value
       ctx
       (q1137206-subtract
        ctx
        (q1137206-subtract
         ctx
         (q1137206-derivative-value
          derivatives derivative-order nearby)
         (q1137206-derivative-value
          derivatives derivative-order point))
        (q1137206-multiply
         ctx
         derivative
         (q1137206-subtract ctx nearby point))))
      (q1137206-multiply
       ctx
       epsilon
       (q1137206-absolute-value
        ctx (q1137206-subtract ctx nearby point)))))))

(defun-sk q1137206-derivative-radius-exists-p
    (ctx derivatives derivative-order derivative
         x0 x point epsilon)
  (exists (radius)
    (and
     (q1137206-positive-real-p ctx radius)
     (q1137206-derivative-radius-p
      ctx derivatives derivative-order derivative
      x0 x point epsilon radius))))

(defun-sk q1137206-has-derivative-within-at-p
    (ctx derivatives derivative-order derivative
         x0 x point)
  (forall (epsilon)
    (implies
     (q1137206-positive-real-p ctx epsilon)
     (q1137206-derivative-radius-exists-p
      ctx derivatives derivative-order derivative
      x0 x point epsilon))))

(defun-sk q1137206-contdiff-orders-continuous-p
    (ctx derivatives order x0 x)
  (forall (derivative-order)
    (implies
     (and
      (natp derivative-order)
      (<= derivative-order order))
     (q1137206-continuous-on-closed-interval-p
      ctx derivatives derivative-order x0 x))))

(defun-sk q1137206-derivative-chain-at-index-p
    (ctx derivatives derivative-order x0 x)
  (forall (point)
    (implies
     (q1137206-in-closed-interval-p ctx x0 x point)
     (q1137206-has-derivative-within-at-p
      ctx
      derivatives
      derivative-order
      (q1137206-derivative-value
       derivatives (+ 1 derivative-order) point)
      x0 x point))))

(defun-sk q1137206-derivative-chain-p
    (ctx derivatives order x0 x)
  (forall (derivative-order)
    (implies
     (and
      (natp derivative-order)
      (< derivative-order order))
     (q1137206-derivative-chain-at-index-p
      ctx derivatives derivative-order x0 x))))

(defun q1137206-contdiff-through-p
    (ctx function derivatives order x0 x)
  (and
   (q1137206-order-zero-is-function-p
    ctx function derivatives)
   (q1137206-contdiff-orders-continuous-p
    ctx derivatives order x0 x)
   (q1137206-derivative-chain-p
    ctx derivatives order x0 x)))

(defun-sk q1137206-next-derivative-on-interior-p
    (ctx derivatives order x0 x)
  (forall (point)
    (implies
     (q1137206-in-open-interval-p ctx x0 x point)
     (q1137206-has-derivative-within-at-p
      ctx
      derivatives
      order
      (q1137206-derivative-value
       derivatives (+ 1 order) point)
      x0 x point))))

;; The finite Taylor polynomial sum from k = 0 through k = ORDER.

(defun q1137206-taylor-sum
    (ctx derivatives terms x0 x)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (q1137206-zero ctx)
    (let* ((index (- terms 1))
           (delta (q1137206-subtract ctx x x0))
           (coefficient
            (q1137206-divide
             ctx
             (q1137206-derivative-value
              derivatives index x0)
             (q1137206-factorial ctx index)))
           (term
            (q1137206-multiply
             ctx
             coefficient
             (q1137206-power ctx delta index))))
      (q1137206-add
       ctx
       (q1137206-taylor-sum
        ctx derivatives index x0 x)
       term))))

;; Independent internal existential witnesses for the two source conclusions.

(defun-sk q1137206-lagrange-remainder-p
    (ctx function derivatives order x0 x)
  (exists (witness)
    (let* ((next-order (+ 1 order))
           (delta (q1137206-subtract ctx x x0))
           (left-side
            (q1137206-subtract
             ctx
             (q1137206-function-value function x)
             (q1137206-taylor-sum
              ctx derivatives next-order x0 x)))
           (right-side
            (q1137206-divide
             ctx
             (q1137206-multiply
              ctx
              (q1137206-derivative-value
               derivatives next-order witness)
              (q1137206-power ctx delta next-order))
             (q1137206-factorial ctx next-order))))
      (and
       (q1137206-in-open-interval-p
        ctx x0 x witness)
       (equal left-side right-side)))))

(defun-sk q1137206-cauchy-remainder-p
    (ctx function derivatives order x0 x)
  (exists (witness)
    (let* ((next-order (+ 1 order))
           (delta (q1137206-subtract ctx x x0))
           (left-side
            (q1137206-subtract
             ctx
             (q1137206-function-value function x)
             (q1137206-taylor-sum
              ctx derivatives next-order x0 x)))
           (right-side
            (q1137206-multiply
             ctx
             (q1137206-divide
              ctx
              (q1137206-multiply
               ctx
               (q1137206-derivative-value
                derivatives next-order witness)
               (q1137206-power
                ctx
                (q1137206-subtract ctx x witness)
                order))
              (q1137206-factorial ctx order))
             delta)))
      (and
       (q1137206-in-open-interval-p
        ctx x0 x witness)
       (equal left-side right-side)))))

(defun-sk thousand-theorems-q1137206-taylor-s-theorem-statement ()
  (forall (ctx function derivatives order x0 x)
    (implies
     (and
      (q1137206-real-field-p ctx)
      (natp order)
      (q1137206-real-p ctx x0)
      (q1137206-real-p ctx x)
      (q1137206-less ctx x0 x)
      (q1137206-extensional-real-function-p
       ctx function)
      (q1137206-extensional-derivative-family-p
       ctx derivatives (+ 1 order))
      (q1137206-contdiff-through-p
       ctx function derivatives order x0 x)
      (q1137206-next-derivative-on-interior-p
       ctx derivatives order x0 x))
     (and
      (q1137206-lagrange-remainder-p
       ctx function derivatives order x0 x)
      (q1137206-cauchy-remainder-p
       ctx function derivatives order x0 x)))))

(value-triple :itpeval-statement-checked)
:q
