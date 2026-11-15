;; Statement-only formalization of Hundred Theorems item 035,
;; "Taylor's Theorem": the Lagrange-remainder formula for a real-valued
;; function continuously differentiable through order n on the unordered
;; closed interval between two distinct points and differentiable once more
;; on its interior.
;; This file contains no proof.
;;
;; Semantic status: the direct DEFUN-SK formulation below repairs the former
;; vacuous APPLY$ quantifiers, but standard ACL2 still ranges only over tame
;; coded functions and subsets. It therefore does not preserve the source's
;; unrestricted real-function quantification and is not counted as a faithful
;; translation.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ objects represent the real carrier, its operations, every
;; subset used by completeness, the arbitrary source function, and its
;; derivative family. All quantifiers remain direct DEFUN-SK quantifiers, so
;; no finite table or opaque set/function tag replaces an extensional object.

(defun ht035-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht035-unary-value (function argument)
  (apply$ function (list argument)))

(defun ht035-binary-value (function left right)
  (apply$ function (list left right)))

;; A scalar context consists of a carrier predicate, zero, one, addition,
;; multiplication, negation, inversion, and strict order.

(defun ht035-r-carrier (ctx) (nth 0 ctx))
(defun ht035-r-zero (ctx) (nth 1 ctx))
(defun ht035-r-one (ctx) (nth 2 ctx))
(defun ht035-r-add (ctx) (nth 3 ctx))
(defun ht035-r-multiply (ctx) (nth 4 ctx))
(defun ht035-r-negate (ctx) (nth 5 ctx))
(defun ht035-r-inverse (ctx) (nth 6 ctx))
(defun ht035-r-less (ctx) (nth 7 ctx))

(defun ht035-real-p (ctx value)
  (ht035-member-p (ht035-r-carrier ctx) value))

(defun ht035-zero (ctx)
  (ht035-r-zero ctx))

(defun ht035-one (ctx)
  (ht035-r-one ctx))

(defun ht035-add (ctx left right)
  (ht035-binary-value
   (ht035-r-add ctx) left right))

(defun ht035-multiply (ctx left right)
  (ht035-binary-value
   (ht035-r-multiply ctx) left right))

(defun ht035-negate (ctx value)
  (ht035-unary-value
   (ht035-r-negate ctx) value))

(defun ht035-inverse (ctx value)
  (ht035-unary-value
   (ht035-r-inverse ctx) value))

(defun ht035-less (ctx left right)
  (if
      (ht035-binary-value
       (ht035-r-less ctx) left right)
      t nil))

(defun ht035-set-member-p (ctx set value)
  (declare (ignore ctx))
  (ht035-member-p set value))

(defun ht035-function-value (function point)
  (ht035-unary-value function point))

(defun ht035-derivative-value
    (derivatives derivative-order point)
  (ht035-binary-value
   derivatives derivative-order point))

(defun ht035-subtract (ctx left right)
  (ht035-add ctx left (ht035-negate ctx right)))

(defun ht035-divide (ctx numerator denominator)
  (ht035-multiply
   ctx numerator (ht035-inverse ctx denominator)))

(defun ht035-less-equal-p (ctx left right)
  (not (ht035-less ctx right left)))

(defun ht035-absolute-value (ctx value)
  (if (ht035-less ctx value (ht035-zero ctx))
      (ht035-negate ctx value)
    value))

(defun ht035-positive-real-p (ctx value)
  (and
   (ht035-real-p ctx value)
   (ht035-less ctx (ht035-zero ctx) value)))

;; A Dedekind-complete ordered field, hence a presentation of the real field.

(defun-sk ht035-field-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (ht035-real-p ctx a)
      (ht035-real-p ctx b)
      (ht035-real-p ctx c))
     (let* ((ab-add (ht035-add ctx a b))
            (bc-add (ht035-add ctx b c))
            (ab-mul (ht035-multiply ctx a b))
            (bc-mul (ht035-multiply ctx b c))
            (neg-a (ht035-negate ctx a))
            (inv-a (ht035-inverse ctx a))
            (zero (ht035-zero ctx))
            (one (ht035-one ctx)))
       (and
        (ht035-real-p ctx ab-add)
        (ht035-real-p ctx ab-mul)
        (ht035-real-p ctx neg-a)
        (ht035-real-p ctx inv-a)
        (equal
         (ht035-add ctx ab-add c)
         (ht035-add ctx a bc-add))
        (equal ab-add (ht035-add ctx b a))
        (equal (ht035-add ctx a zero) a)
        (equal (ht035-add ctx a neg-a) zero)
        (equal
         (ht035-multiply ctx ab-mul c)
         (ht035-multiply ctx a bc-mul))
        (equal ab-mul (ht035-multiply ctx b a))
        (equal (ht035-multiply ctx a one) a)
        (implies
         (equal a zero)
         (equal inv-a zero))
        (implies
         (not (equal a zero))
         (equal (ht035-multiply ctx a inv-a) one))
        (equal
         (ht035-multiply ctx a bc-add)
         (ht035-add
          ctx
          (ht035-multiply ctx a b)
          (ht035-multiply ctx a c))))))))

(defun-sk ht035-order-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (ht035-real-p ctx a)
      (ht035-real-p ctx b)
      (ht035-real-p ctx c))
     (and
      (not (ht035-less ctx a a))
      (or
       (ht035-less ctx a b)
       (equal a b)
       (ht035-less ctx b a))
      (implies
       (and
        (ht035-less ctx a b)
        (ht035-less ctx b c))
       (ht035-less ctx a c))
      (implies
       (ht035-less ctx a b)
       (ht035-less
        ctx
        (ht035-add ctx a c)
        (ht035-add ctx b c)))
      (implies
       (and
        (ht035-less ctx (ht035-zero ctx) a)
        (ht035-less ctx (ht035-zero ctx) b))
       (ht035-less
        ctx
        (ht035-zero ctx)
        (ht035-multiply ctx a b)))))))

(defun-sk ht035-valid-set-p (ctx set)
  (forall (value)
    (implies
     (ht035-set-member-p ctx set value)
     (ht035-real-p ctx value))))

(defun ht035-extensional-set-p (ctx set)
  (and
   (tamep-functionp set)
   (ht035-valid-set-p ctx set)))

(defun-sk ht035-set-nonempty-p (ctx set)
  (exists (value)
    (and
     (ht035-real-p ctx value)
     (ht035-set-member-p ctx set value))))

(defun-sk ht035-upper-bound-p (ctx set upper)
  (forall (value)
    (implies
     (and
      (ht035-real-p ctx value)
      (ht035-set-member-p ctx set value))
     (not (ht035-less ctx upper value)))))

(defun-sk ht035-bounded-above-p (ctx set)
  (exists (upper)
    (and
     (ht035-real-p ctx upper)
     (ht035-upper-bound-p ctx set upper))))

(defun-sk ht035-least-upper-bound-p
    (ctx set supremum)
  (forall (upper)
    (implies
     (and
      (ht035-real-p ctx upper)
      (ht035-upper-bound-p ctx set upper))
     (not (ht035-less ctx upper supremum)))))

(defun ht035-is-supremum-p (ctx set supremum)
  (and
   (ht035-real-p ctx supremum)
   (ht035-upper-bound-p ctx set supremum)
   (ht035-least-upper-bound-p ctx set supremum)))

(defun-sk ht035-has-supremum-p (ctx set)
  (exists (supremum)
    (ht035-is-supremum-p ctx set supremum)))

(defun-sk ht035-completeness-p (ctx)
  (forall (set)
    (implies
     (and
      (ht035-extensional-set-p ctx set)
      (ht035-set-nonempty-p ctx set)
      (ht035-bounded-above-p ctx set))
     (ht035-has-supremum-p ctx set))))

(defun ht035-real-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (ht035-r-carrier ctx))
   (tamep-functionp (ht035-r-add ctx))
   (tamep-functionp (ht035-r-multiply ctx))
   (tamep-functionp (ht035-r-negate ctx))
   (tamep-functionp (ht035-r-inverse ctx))
   (tamep-functionp (ht035-r-less ctx))
   (ht035-real-p ctx (ht035-zero ctx))
   (ht035-real-p ctx (ht035-one ctx))
   (not
    (equal
     (ht035-zero ctx)
     (ht035-one ctx)))
   (ht035-field-laws-p ctx)
   (ht035-order-laws-p ctx)
   (ht035-completeness-p ctx)
   (ht035-less
    ctx (ht035-zero ctx) (ht035-one ctx))))

;; Natural numbers embedded in the abstract real field.

(defun ht035-real-natural (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht035-zero ctx)
    (ht035-add
     ctx
     (ht035-one ctx)
     (ht035-real-natural ctx (- n 1)))))

(defun ht035-power (ctx base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht035-one ctx)
    (ht035-multiply
     ctx
     base
     (ht035-power ctx base (- exponent 1)))))

(defun ht035-factorial (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht035-one ctx)
    (ht035-multiply
     ctx
     (ht035-real-natural ctx n)
     (ht035-factorial ctx (- n 1)))))

;; The unordered intervals uIcc x0 x and uIoo x0 x.

(defun ht035-in-closed-interval-p
    (ctx x0 x point)
  (and
   (ht035-real-p ctx point)
   (or
    (and
     (not (ht035-less ctx point x0))
     (not (ht035-less ctx x point)))
    (and
     (not (ht035-less ctx point x))
     (not (ht035-less ctx x0 point))))))

(defun ht035-in-open-interval-p
    (ctx x0 x point)
  (and
   (ht035-real-p ctx point)
   (or
    (and
     (ht035-less ctx x0 point)
     (ht035-less ctx point x))
    (and
     (ht035-less ctx x point)
     (ht035-less ctx point x0)))))

;; Arbitrary real-valued functions and explicitly tied iterated derivatives.

(defun-sk ht035-real-function-p (ctx function)
  (forall (point)
    (implies
     (ht035-real-p ctx point)
     (ht035-real-p
      ctx (ht035-function-value function point)))))

(defun ht035-extensional-real-function-p
    (ctx function)
  (and
   (tamep-functionp function)
   (ht035-real-function-p ctx function)))

(defun-sk ht035-derivative-order-real-p
    (ctx derivatives derivative-order)
  (forall (point)
    (implies
     (ht035-real-p ctx point)
     (ht035-real-p
      ctx
      (ht035-derivative-value
       derivatives derivative-order point)))))

(defun-sk ht035-derivative-family-p
    (ctx derivatives maximum-order)
  (forall (derivative-order)
    (implies
     (and
      (natp derivative-order)
      (<= derivative-order maximum-order))
     (ht035-derivative-order-real-p
      ctx derivatives derivative-order))))

(defun ht035-extensional-derivative-family-p
    (ctx derivatives maximum-order)
  (and
   (tamep-functionp derivatives)
   (ht035-derivative-family-p
    ctx derivatives maximum-order)))

(defun-sk ht035-order-zero-is-function-p
    (ctx function derivatives)
  (forall (point)
    (implies
     (ht035-real-p ctx point)
     (equal
      (ht035-derivative-value derivatives 0 point)
      (ht035-function-value function point)))))

;; Epsilon-delta continuity of a derivative row on the closed interval.

(defun-sk ht035-continuity-radius-p
    (ctx derivatives derivative-order x0 x point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (ht035-in-closed-interval-p
       ctx x0 x nearby)
      (ht035-less
       ctx
       (ht035-absolute-value
        ctx (ht035-subtract ctx nearby point))
       radius))
     (ht035-less
      ctx
      (ht035-absolute-value
       ctx
       (ht035-subtract
        ctx
        (ht035-derivative-value
         derivatives derivative-order nearby)
        (ht035-derivative-value
         derivatives derivative-order point)))
      epsilon))))

(defun-sk ht035-continuity-radius-exists-p
    (ctx derivatives derivative-order x0 x point epsilon)
  (exists (radius)
    (and
     (ht035-positive-real-p ctx radius)
     (ht035-continuity-radius-p
      ctx derivatives derivative-order
      x0 x point epsilon radius))))

(defun-sk ht035-continuous-within-at-p
    (ctx derivatives derivative-order x0 x point)
  (forall (epsilon)
    (implies
     (ht035-positive-real-p ctx epsilon)
     (ht035-continuity-radius-exists-p
      ctx derivatives derivative-order
      x0 x point epsilon))))

(defun-sk ht035-continuous-on-closed-interval-p
    (ctx derivatives derivative-order x0 x)
  (forall (point)
    (implies
     (ht035-in-closed-interval-p ctx x0 x point)
     (ht035-continuous-within-at-p
      ctx derivatives derivative-order x0 x point))))

;; HasDerivWithinAt in epsilon-delta form, restricted to Icc x0 x.

(defun-sk ht035-derivative-radius-p
    (ctx derivatives derivative-order derivative
         x0 x point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (ht035-in-closed-interval-p
       ctx x0 x nearby)
      (ht035-less
       ctx
       (ht035-absolute-value
        ctx (ht035-subtract ctx nearby point))
       radius))
     (ht035-less-equal-p
      ctx
      (ht035-absolute-value
       ctx
       (ht035-subtract
        ctx
        (ht035-subtract
         ctx
         (ht035-derivative-value
          derivatives derivative-order nearby)
         (ht035-derivative-value
          derivatives derivative-order point))
        (ht035-multiply
         ctx
         derivative
         (ht035-subtract ctx nearby point))))
      (ht035-multiply
       ctx
       epsilon
       (ht035-absolute-value
        ctx (ht035-subtract ctx nearby point)))))))

(defun-sk ht035-derivative-radius-exists-p
    (ctx derivatives derivative-order derivative
         x0 x point epsilon)
  (exists (radius)
    (and
     (ht035-positive-real-p ctx radius)
     (ht035-derivative-radius-p
      ctx derivatives derivative-order derivative
      x0 x point epsilon radius))))

(defun-sk ht035-has-derivative-within-at-p
    (ctx derivatives derivative-order derivative
         x0 x point)
  (forall (epsilon)
    (implies
     (ht035-positive-real-p ctx epsilon)
     (ht035-derivative-radius-exists-p
      ctx derivatives derivative-order derivative
      x0 x point epsilon))))

(defun-sk ht035-contdiff-orders-continuous-p
    (ctx derivatives order x0 x)
  (forall (derivative-order)
    (implies
     (and
      (natp derivative-order)
      (<= derivative-order order))
     (ht035-continuous-on-closed-interval-p
      ctx derivatives derivative-order x0 x))))

(defun-sk ht035-derivative-chain-at-index-p
    (ctx derivatives derivative-order x0 x)
  (forall (point)
    (implies
     (ht035-in-closed-interval-p ctx x0 x point)
     (ht035-has-derivative-within-at-p
      ctx
      derivatives
      derivative-order
      (ht035-derivative-value
       derivatives (+ 1 derivative-order) point)
      x0 x point))))

(defun-sk ht035-derivative-chain-p
    (ctx derivatives order x0 x)
  (forall (derivative-order)
    (implies
     (and
      (natp derivative-order)
      (< derivative-order order))
     (ht035-derivative-chain-at-index-p
      ctx derivatives derivative-order x0 x))))

(defun ht035-contdiff-through-p
    (ctx function derivatives order x0 x)
  (and
   (ht035-order-zero-is-function-p
    ctx function derivatives)
   (ht035-contdiff-orders-continuous-p
    ctx derivatives order x0 x)
   (ht035-derivative-chain-p
    ctx derivatives order x0 x)))

(defun-sk ht035-next-derivative-on-interior-p
    (ctx derivatives order x0 x)
  (forall (point)
    (implies
     (ht035-in-open-interval-p ctx x0 x point)
     (ht035-has-derivative-within-at-p
      ctx
      derivatives
      order
      (ht035-derivative-value
       derivatives (+ 1 order) point)
      x0 x point))))

;; The finite Taylor polynomial sum from k = 0 through k = ORDER.

(defun ht035-taylor-sum
    (ctx derivatives terms x0 x)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht035-zero ctx)
    (let* ((index (- terms 1))
           (delta (ht035-subtract ctx x x0))
           (coefficient
            (ht035-divide
             ctx
             (ht035-derivative-value
              derivatives index x0)
             (ht035-factorial ctx index)))
           (term
            (ht035-multiply
             ctx
             coefficient
             (ht035-power ctx delta index))))
      (ht035-add
       ctx
       (ht035-taylor-sum
        ctx derivatives index x0 x)
       term))))

;; Internal existential witness for the source's Lagrange remainder.

(defun-sk ht035-lagrange-remainder-p
    (ctx function derivatives order x0 x)
  (exists (witness)
    (let* ((next-order (+ 1 order))
           (delta (ht035-subtract ctx x x0))
           (left-side
            (ht035-subtract
             ctx
             (ht035-function-value function x)
             (ht035-taylor-sum
              ctx derivatives next-order x0 x)))
           (right-side
            (ht035-divide
             ctx
             (ht035-multiply
              ctx
              (ht035-derivative-value
               derivatives next-order witness)
              (ht035-power ctx delta next-order))
             (ht035-factorial ctx next-order))))
      (and
       (ht035-in-open-interval-p
        ctx x0 x witness)
       (equal left-side right-side)))))

(defun-sk hundred-theorems-035-taylors-theorem-statement ()
  (forall (ctx function derivatives order x0 x)
    (implies
     (and
      (ht035-real-field-p ctx)
      (natp order)
      (ht035-real-p ctx x0)
      (ht035-real-p ctx x)
      (not (equal x0 x))
      (ht035-extensional-real-function-p
       ctx function)
      (ht035-extensional-derivative-family-p
       ctx derivatives (+ 1 order))
      (ht035-contdiff-through-p
       ctx function derivatives order x0 x)
      (ht035-next-derivative-on-interior-p
       ctx derivatives order x0 x))
     (ht035-lagrange-remainder-p
      ctx function derivatives order x0 x))))

(value-triple :itpeval-statement-checked)
:q
