;; Statement-only formalization of Hundred Theorems item 075,
;; "The Mean Value Theorem": Cauchy's and Lagrange's mean value theorems
;; for real-valued functions continuous on [a,b] and differentiable on
;; (a,b), where a < b.
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
;; subset used by completeness, and the arbitrary functions. All
;; quantifiers remain direct DEFUN-SK quantifiers, so
;; no finite table or opaque set/function tag replaces an extensional object.

(defun ht075-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht075-unary-value (function argument)
  (apply$ function (list argument)))

(defun ht075-binary-value (function left right)
  (apply$ function (list left right)))

;; A scalar context consists of a carrier predicate, zero, one, addition,
;; multiplication, negation, inversion, and strict order.

(defun ht075-r-carrier (ctx) (nth 0 ctx))
(defun ht075-r-zero (ctx) (nth 1 ctx))
(defun ht075-r-one (ctx) (nth 2 ctx))
(defun ht075-r-add (ctx) (nth 3 ctx))
(defun ht075-r-multiply (ctx) (nth 4 ctx))
(defun ht075-r-negate (ctx) (nth 5 ctx))
(defun ht075-r-inverse (ctx) (nth 6 ctx))
(defun ht075-r-less (ctx) (nth 7 ctx))

(defun ht075-real-p (ctx value)
  (ht075-member-p (ht075-r-carrier ctx) value))

(defun ht075-zero (ctx)
  (ht075-r-zero ctx))

(defun ht075-one (ctx)
  (ht075-r-one ctx))

(defun ht075-add (ctx left right)
  (ht075-binary-value
   (ht075-r-add ctx) left right))

(defun ht075-multiply (ctx left right)
  (ht075-binary-value
   (ht075-r-multiply ctx) left right))

(defun ht075-negate (ctx value)
  (ht075-unary-value
   (ht075-r-negate ctx) value))

(defun ht075-inverse (ctx value)
  (ht075-unary-value
   (ht075-r-inverse ctx) value))

(defun ht075-less (ctx left right)
  (if
      (ht075-binary-value
       (ht075-r-less ctx) left right)
      t nil))

(defun ht075-set-member-p (ctx set value)
  (declare (ignore ctx))
  (ht075-member-p set value))

(defun ht075-function-value (function point)
  (ht075-unary-value function point))

(defun ht075-subtract (ctx left right)
  (ht075-add ctx left (ht075-negate ctx right)))

(defun ht075-divide (ctx numerator denominator)
  (ht075-multiply
   ctx numerator (ht075-inverse ctx denominator)))

(defun ht075-less-equal-p (ctx left right)
  (not (ht075-less ctx right left)))

(defun ht075-absolute-value (ctx value)
  (if (ht075-less ctx value (ht075-zero ctx))
      (ht075-negate ctx value)
    value))

(defun ht075-positive-real-p (ctx value)
  (and
   (ht075-real-p ctx value)
   (ht075-less ctx (ht075-zero ctx) value)))

;; A Dedekind-complete ordered field, hence a presentation of the real field.

(defun-sk ht075-field-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (ht075-real-p ctx a)
      (ht075-real-p ctx b)
      (ht075-real-p ctx c))
     (let* ((ab-add (ht075-add ctx a b))
            (bc-add (ht075-add ctx b c))
            (ab-mul (ht075-multiply ctx a b))
            (bc-mul (ht075-multiply ctx b c))
            (neg-a (ht075-negate ctx a))
            (inv-a (ht075-inverse ctx a))
            (zero (ht075-zero ctx))
            (one (ht075-one ctx)))
       (and
        (ht075-real-p ctx ab-add)
        (ht075-real-p ctx ab-mul)
        (ht075-real-p ctx neg-a)
        (ht075-real-p ctx inv-a)
        (equal
         (ht075-add ctx ab-add c)
         (ht075-add ctx a bc-add))
        (equal ab-add (ht075-add ctx b a))
        (equal (ht075-add ctx a zero) a)
        (equal (ht075-add ctx a neg-a) zero)
        (equal
         (ht075-multiply ctx ab-mul c)
         (ht075-multiply ctx a bc-mul))
        (equal ab-mul (ht075-multiply ctx b a))
        (equal (ht075-multiply ctx a one) a)
        (implies
         (equal a zero)
         (equal inv-a zero))
        (implies
         (not (equal a zero))
         (equal (ht075-multiply ctx a inv-a) one))
        (equal
         (ht075-multiply ctx a bc-add)
         (ht075-add
          ctx
          (ht075-multiply ctx a b)
          (ht075-multiply ctx a c))))))))

(defun-sk ht075-order-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (ht075-real-p ctx a)
      (ht075-real-p ctx b)
      (ht075-real-p ctx c))
     (and
      (not (ht075-less ctx a a))
      (or
       (ht075-less ctx a b)
       (equal a b)
       (ht075-less ctx b a))
      (implies
       (and
        (ht075-less ctx a b)
        (ht075-less ctx b c))
       (ht075-less ctx a c))
      (implies
       (ht075-less ctx a b)
       (ht075-less
        ctx
        (ht075-add ctx a c)
        (ht075-add ctx b c)))
      (implies
       (and
        (ht075-less ctx (ht075-zero ctx) a)
        (ht075-less ctx (ht075-zero ctx) b))
       (ht075-less
        ctx
        (ht075-zero ctx)
        (ht075-multiply ctx a b)))))))

(defun-sk ht075-valid-set-p (ctx set)
  (forall (value)
    (implies
     (ht075-set-member-p ctx set value)
     (ht075-real-p ctx value))))

(defun ht075-extensional-set-p (ctx set)
  (and
   (tamep-functionp set)
   (ht075-valid-set-p ctx set)))

(defun-sk ht075-set-nonempty-p (ctx set)
  (exists (value)
    (and
     (ht075-real-p ctx value)
     (ht075-set-member-p ctx set value))))

(defun-sk ht075-upper-bound-p (ctx set upper)
  (forall (value)
    (implies
     (and
      (ht075-real-p ctx value)
      (ht075-set-member-p ctx set value))
     (not (ht075-less ctx upper value)))))

(defun-sk ht075-bounded-above-p (ctx set)
  (exists (upper)
    (and
     (ht075-real-p ctx upper)
     (ht075-upper-bound-p ctx set upper))))

(defun-sk ht075-least-upper-bound-p
    (ctx set supremum)
  (forall (upper)
    (implies
     (and
      (ht075-real-p ctx upper)
      (ht075-upper-bound-p ctx set upper))
     (not (ht075-less ctx upper supremum)))))

(defun ht075-is-supremum-p (ctx set supremum)
  (and
   (ht075-real-p ctx supremum)
   (ht075-upper-bound-p ctx set supremum)
   (ht075-least-upper-bound-p ctx set supremum)))

(defun-sk ht075-has-supremum-p (ctx set)
  (exists (supremum)
    (ht075-is-supremum-p ctx set supremum)))

(defun-sk ht075-completeness-p (ctx)
  (forall (set)
    (implies
     (and
      (ht075-extensional-set-p ctx set)
      (ht075-set-nonempty-p ctx set)
      (ht075-bounded-above-p ctx set))
     (ht075-has-supremum-p ctx set))))

(defun ht075-real-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (ht075-r-carrier ctx))
   (tamep-functionp (ht075-r-add ctx))
   (tamep-functionp (ht075-r-multiply ctx))
   (tamep-functionp (ht075-r-negate ctx))
   (tamep-functionp (ht075-r-inverse ctx))
   (tamep-functionp (ht075-r-less ctx))
   (ht075-real-p ctx (ht075-zero ctx))
   (ht075-real-p ctx (ht075-one ctx))
   (not
    (equal
     (ht075-zero ctx)
     (ht075-one ctx)))
   (ht075-field-laws-p ctx)
   (ht075-order-laws-p ctx)
   (ht075-completeness-p ctx)
   (ht075-less
    ctx (ht075-zero ctx) (ht075-one ctx))))

;; The ordered closed interval [a,b] and open interval (a,b).

(defun ht075-in-closed-interval-p
    (ctx a b point)
  (and
   (ht075-real-p ctx point)
   (not (ht075-less ctx point a))
   (not (ht075-less ctx b point))))

(defun ht075-in-open-interval-p
    (ctx a b point)
  (and
   (ht075-real-p ctx point)
   (ht075-less ctx a point)
   (ht075-less ctx point b)))

;; Arbitrary real-valued functions represented extensionally by tame APPLY$
;; objects. The explicit derivative functions below play the role of f' and
;; g' in the HasDerivAt versions of the source theorems.

(defun-sk ht075-real-function-p (ctx function)
  (forall (point)
    (implies
     (ht075-real-p ctx point)
     (ht075-real-p
      ctx (ht075-function-value function point)))))

(defun ht075-extensional-real-function-p
    (ctx function)
  (and
   (tamep-functionp function)
   (ht075-real-function-p ctx function)))

;; Epsilon-delta continuity relative to the closed interval.

(defun-sk ht075-continuity-radius-p
    (ctx function a b point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (ht075-in-closed-interval-p
       ctx a b nearby)
      (ht075-less
       ctx
       (ht075-absolute-value
        ctx (ht075-subtract ctx nearby point))
       radius))
     (ht075-less
      ctx
      (ht075-absolute-value
       ctx
       (ht075-subtract
        ctx
        (ht075-function-value function nearby)
        (ht075-function-value function point)))
      epsilon))))

(defun-sk ht075-continuity-radius-exists-p
    (ctx function a b point epsilon)
  (exists (radius)
    (and
     (ht075-positive-real-p ctx radius)
     (ht075-continuity-radius-p
      ctx function a b point epsilon radius))))

(defun-sk ht075-continuous-within-at-p
    (ctx function a b point)
  (forall (epsilon)
    (implies
     (ht075-positive-real-p ctx epsilon)
     (ht075-continuity-radius-exists-p
      ctx function a b point epsilon))))

(defun-sk ht075-continuous-on-closed-interval-p
    (ctx function a b)
  (forall (point)
    (implies
     (ht075-in-closed-interval-p ctx a b point)
     (ht075-continuous-within-at-p
      ctx function a b point))))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| for all sufficiently near y.

(defun-sk ht075-derivative-radius-p
    (ctx function derivative-value point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (ht075-real-p ctx nearby)
      (ht075-less
       ctx
       (ht075-absolute-value
        ctx (ht075-subtract ctx nearby point))
       radius))
     (ht075-less-equal-p
      ctx
      (ht075-absolute-value
       ctx
       (ht075-subtract
        ctx
        (ht075-subtract
         ctx
         (ht075-function-value function nearby)
         (ht075-function-value function point))
        (ht075-multiply
         ctx
         derivative-value
         (ht075-subtract ctx nearby point))))
      (ht075-multiply
       ctx
       epsilon
       (ht075-absolute-value
        ctx (ht075-subtract ctx nearby point)))))))

(defun-sk ht075-derivative-radius-exists-p
    (ctx function derivative-value point epsilon)
  (exists (radius)
    (and
     (ht075-positive-real-p ctx radius)
     (ht075-derivative-radius-p
      ctx function derivative-value
      point epsilon radius))))

(defun-sk ht075-derivative-epsilon-p
    (ctx function derivative-value point)
  (forall (epsilon)
    (implies
     (ht075-positive-real-p ctx epsilon)
     (ht075-derivative-radius-exists-p
      ctx function derivative-value point epsilon))))

(defun ht075-has-derivative-at-p
    (ctx function derivative-value point)
  (and
   (ht075-real-p ctx derivative-value)
   (ht075-real-p ctx point)
   (ht075-derivative-epsilon-p
    ctx function derivative-value point)))

(defun-sk ht075-derivative-function-on-open-interval-p
    (ctx function derivative-function a b)
  (forall (point)
    (implies
     (ht075-in-open-interval-p ctx a b point)
     (ht075-has-derivative-at-p
      ctx
      function
      (ht075-function-value derivative-function point)
      point))))

;; The conclusions are exactly the denominator-free Cauchy identity and the
;; Lagrange slope identity selected by the Lean source.

(defun-sk ht075-cauchy-witness-p
    (ctx f f-prime g g-prime a b)
  (exists (c)
    (and
     (ht075-in-open-interval-p ctx a b c)
     (equal
      (ht075-multiply
       ctx
       (ht075-subtract
        ctx
        (ht075-function-value g b)
        (ht075-function-value g a))
       (ht075-function-value f-prime c))
      (ht075-multiply
       ctx
       (ht075-subtract
        ctx
        (ht075-function-value f b)
        (ht075-function-value f a))
       (ht075-function-value g-prime c))))))

(defun-sk ht075-lagrange-witness-p
    (ctx f f-prime a b)
  (exists (c)
    (and
     (ht075-in-open-interval-p ctx a b c)
     (equal
      (ht075-function-value f-prime c)
      (ht075-divide
       ctx
       (ht075-subtract
        ctx
        (ht075-function-value f b)
        (ht075-function-value f a))
       (ht075-subtract ctx b a))))))

(defun-sk
    hundred-theorems-075-cauchy-mean-value-theorem-statement ()
  (forall (ctx f f-prime g g-prime a b)
    (implies
     (and
      (ht075-real-field-p ctx)
      (ht075-real-p ctx a)
      (ht075-real-p ctx b)
      (ht075-less ctx a b)
      (ht075-extensional-real-function-p ctx f)
      (ht075-extensional-real-function-p ctx f-prime)
      (ht075-extensional-real-function-p ctx g)
      (ht075-extensional-real-function-p ctx g-prime)
      (ht075-continuous-on-closed-interval-p
       ctx f a b)
      (ht075-continuous-on-closed-interval-p
       ctx g a b)
      (ht075-derivative-function-on-open-interval-p
       ctx f f-prime a b)
      (ht075-derivative-function-on-open-interval-p
       ctx g g-prime a b))
     (ht075-cauchy-witness-p
      ctx f f-prime g g-prime a b))))

(defun-sk
    hundred-theorems-075-mean-value-theorem-statement ()
  (forall (ctx f f-prime a b)
    (implies
     (and
      (ht075-real-field-p ctx)
      (ht075-real-p ctx a)
      (ht075-real-p ctx b)
      (ht075-less ctx a b)
      (ht075-extensional-real-function-p ctx f)
      (ht075-extensional-real-function-p ctx f-prime)
      (ht075-continuous-on-closed-interval-p
       ctx f a b)
      (ht075-derivative-function-on-open-interval-p
       ctx f f-prime a b))
     (ht075-lagrange-witness-p
      ctx f f-prime a b))))

(value-triple :itpeval-statement-checked)
:q
