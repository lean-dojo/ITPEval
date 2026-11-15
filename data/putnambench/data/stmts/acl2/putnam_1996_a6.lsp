;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_a6:
;; classification of the continuous real functions satisfying
;; f(x) = f(x^2 + c) for a positive real constant c. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism. APPLY$ objects represent arbitrary
;; carrier predicates, subsets, operations, and real-valued functions, while
;; DEFUN-SK keeps all source quantifiers internal to the statement.

(defun putnam-1996-a6-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun putnam-1996-a6-unary-value (operation value)
  (apply$ operation (list value)))

(defun putnam-1996-a6-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun-sk putnam-1996-a6-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1996-a6-member-p carrier x))))

(defun-sk putnam-1996-a6-real-function-p (carrier function)
  (forall (x)
    (implies
     (putnam-1996-a6-member-p carrier x)
     (putnam-1996-a6-member-p
      carrier
      (putnam-1996-a6-unary-value function x)))))

(defun-sk putnam-1996-a6-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1996-a6-member-p carrier x)
      (putnam-1996-a6-member-p carrier y)
      (putnam-1996-a6-member-p carrier z))
     (let* ((xy-add
             (putnam-1996-a6-binary-value add x y))
            (yz-add
             (putnam-1996-a6-binary-value add y z))
            (xy-multiply
             (putnam-1996-a6-binary-value multiply x y))
            (yz-multiply
             (putnam-1996-a6-binary-value multiply y z))
            (negative-x
             (putnam-1996-a6-unary-value negate x))
            (inverse-x
             (putnam-1996-a6-unary-value inverse x)))
       (and
        (putnam-1996-a6-member-p carrier xy-add)
        (putnam-1996-a6-member-p carrier xy-multiply)
        (putnam-1996-a6-member-p carrier negative-x)
        (putnam-1996-a6-member-p carrier inverse-x)
        (equal
         (putnam-1996-a6-binary-value add xy-add z)
         (putnam-1996-a6-binary-value add x yz-add))
        (equal
         xy-add
         (putnam-1996-a6-binary-value add y x))
        (equal
         (putnam-1996-a6-binary-value add x zero)
         x)
        (equal
         (putnam-1996-a6-binary-value add x negative-x)
         zero)
        (equal
         (putnam-1996-a6-binary-value multiply xy-multiply z)
         (putnam-1996-a6-binary-value multiply x yz-multiply))
        (equal
         xy-multiply
         (putnam-1996-a6-binary-value multiply y x))
        (equal
         (putnam-1996-a6-binary-value multiply x one)
         x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1996-a6-binary-value multiply x inverse-x)
          one))
        (equal
         (putnam-1996-a6-binary-value multiply x yz-add)
         (putnam-1996-a6-binary-value
          add
          (putnam-1996-a6-binary-value multiply x y)
          (putnam-1996-a6-binary-value multiply x z))))))))

(defun-sk putnam-1996-a6-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1996-a6-member-p carrier x)
      (putnam-1996-a6-member-p carrier y)
      (putnam-1996-a6-member-p carrier z))
     (and
      (not (putnam-1996-a6-binary-value less x x))
      (or
       (equal x y)
       (putnam-1996-a6-binary-value less x y)
       (putnam-1996-a6-binary-value less y x))
      (implies
       (and
        (putnam-1996-a6-binary-value less x y)
        (putnam-1996-a6-binary-value less y z))
       (putnam-1996-a6-binary-value less x z))
      (implies
       (putnam-1996-a6-binary-value less x y)
       (putnam-1996-a6-binary-value
        less
        (putnam-1996-a6-binary-value add x z)
        (putnam-1996-a6-binary-value add y z)))
      (implies
       (and
        (putnam-1996-a6-binary-value less zero x)
        (putnam-1996-a6-binary-value less zero y))
       (putnam-1996-a6-binary-value
        less
        zero
        (putnam-1996-a6-binary-value multiply x y)))))))

(defun-sk putnam-1996-a6-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1996-a6-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1996-a6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1996-a6-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1996-a6-binary-value less bound x)))))

(defun-sk putnam-1996-a6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1996-a6-member-p carrier bound)
     (putnam-1996-a6-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1996-a6-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1996-a6-member-p carrier supremum)
     (putnam-1996-a6-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1996-a6-member-p carrier bound)
       (putnam-1996-a6-upper-bound-p
        carrier less set bound))
      (not
       (putnam-1996-a6-binary-value
        less bound supremum))))))

(defun-sk putnam-1996-a6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1996-a6-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1996-a6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1996-a6-valid-set-p carrier set)
      (putnam-1996-a6-set-nonempty-p carrier set)
      (putnam-1996-a6-bounded-above-p
       carrier less set))
     (putnam-1996-a6-has-supremum-p
      carrier less set))))

(defun putnam-1996-a6-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1996-a6-member-p carrier zero)
   (putnam-1996-a6-member-p carrier one)
   (not (equal zero one))
   (putnam-1996-a6-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1996-a6-order-laws-p
    carrier zero add multiply less)
   (putnam-1996-a6-binary-value less zero one)
   (putnam-1996-a6-dedekind-complete-p
    carrier less)))

;; Real-field context and arithmetic.

(defun putnam-1996-a6-r-carrier (ctx) (nth 0 ctx))
(defun putnam-1996-a6-r-zero (ctx) (nth 1 ctx))
(defun putnam-1996-a6-r-one (ctx) (nth 2 ctx))
(defun putnam-1996-a6-r-add (ctx) (nth 3 ctx))
(defun putnam-1996-a6-r-multiply (ctx) (nth 4 ctx))
(defun putnam-1996-a6-r-negate (ctx) (nth 5 ctx))
(defun putnam-1996-a6-r-inverse (ctx) (nth 6 ctx))
(defun putnam-1996-a6-r-less (ctx) (nth 7 ctx))

(defun putnam-1996-a6-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (putnam-1996-a6-real-field-p
    (putnam-1996-a6-r-carrier ctx)
    (putnam-1996-a6-r-zero ctx)
    (putnam-1996-a6-r-one ctx)
    (putnam-1996-a6-r-add ctx)
    (putnam-1996-a6-r-multiply ctx)
    (putnam-1996-a6-r-negate ctx)
    (putnam-1996-a6-r-inverse ctx)
    (putnam-1996-a6-r-less ctx))))

(defun putnam-1996-a6-r-add-value (ctx left right)
  (putnam-1996-a6-binary-value
   (putnam-1996-a6-r-add ctx) left right))

(defun putnam-1996-a6-r-multiply-value (ctx left right)
  (putnam-1996-a6-binary-value
   (putnam-1996-a6-r-multiply ctx) left right))

(defun putnam-1996-a6-r-negate-value (ctx value)
  (putnam-1996-a6-unary-value
   (putnam-1996-a6-r-negate ctx) value))

(defun putnam-1996-a6-r-inverse-value (ctx value)
  (putnam-1996-a6-unary-value
   (putnam-1996-a6-r-inverse ctx) value))

(defun putnam-1996-a6-r-subtract-value (ctx left right)
  (putnam-1996-a6-r-add-value
   ctx left (putnam-1996-a6-r-negate-value ctx right)))

(defun putnam-1996-a6-r-less-p (ctx left right)
  (if (putnam-1996-a6-binary-value
       (putnam-1996-a6-r-less ctx) left right)
      t
    nil))

(defun putnam-1996-a6-r-less-equal-p (ctx left right)
  (not (putnam-1996-a6-r-less-p ctx right left)))

(defun putnam-1996-a6-r-absolute-value (ctx value)
  (if (putnam-1996-a6-r-less-p
       ctx value (putnam-1996-a6-r-zero ctx))
      (putnam-1996-a6-r-negate-value ctx value)
    value))

(defun putnam-1996-a6-positive-real-p (ctx value)
  (and
   (putnam-1996-a6-member-p
    (putnam-1996-a6-r-carrier ctx) value)
   (putnam-1996-a6-r-less-p
    ctx (putnam-1996-a6-r-zero ctx) value)))

(defun putnam-1996-a6-r-natural (n ctx)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1996-a6-r-zero ctx)
    (putnam-1996-a6-r-add-value
     ctx
     (putnam-1996-a6-r-one ctx)
     (putnam-1996-a6-r-natural (1- n) ctx))))

(defun putnam-1996-a6-r-quarter (ctx)
  (putnam-1996-a6-r-inverse-value
   ctx
   (putnam-1996-a6-r-natural 4 ctx)))

(defun putnam-1996-a6-function-value (function x)
  (putnam-1996-a6-unary-value function x))

(defun putnam-1996-a6-square-plus-c (ctx x c)
  (putnam-1996-a6-r-add-value
   ctx
   (putnam-1996-a6-r-multiply-value ctx x x)
   c))

(defun putnam-1996-a6-icc-member-p (ctx left right x)
  (and
   (putnam-1996-a6-member-p
    (putnam-1996-a6-r-carrier ctx) x)
   (putnam-1996-a6-r-less-equal-p ctx left x)
   (putnam-1996-a6-r-less-equal-p ctx x right)))

;; Epsilon-delta continuity on the whole real field.

(defun-sk putnam-1996-a6-global-neighborhood-p
    (ctx function x epsilon radius)
  (forall (y)
    (implies
     (and
      (putnam-1996-a6-member-p
       (putnam-1996-a6-r-carrier ctx) y)
      (putnam-1996-a6-r-less-p
       ctx
       (putnam-1996-a6-r-absolute-value
        ctx
        (putnam-1996-a6-r-subtract-value ctx y x))
       radius))
     (putnam-1996-a6-r-less-p
      ctx
      (putnam-1996-a6-r-absolute-value
       ctx
       (putnam-1996-a6-r-subtract-value
        ctx
        (putnam-1996-a6-function-value function y)
        (putnam-1996-a6-function-value function x)))
      epsilon))))

(defun-sk putnam-1996-a6-global-radius-exists-p
    (ctx function x epsilon)
  (exists (radius)
    (and
     (putnam-1996-a6-positive-real-p ctx radius)
     (putnam-1996-a6-global-neighborhood-p
      ctx function x epsilon radius))))

(defun-sk putnam-1996-a6-continuous-at-p
    (ctx function x)
  (forall (epsilon)
    (implies
     (putnam-1996-a6-positive-real-p ctx epsilon)
     (putnam-1996-a6-global-radius-exists-p
      ctx function x epsilon))))

(defun-sk putnam-1996-a6-continuous-p
    (ctx function)
  (forall (x)
    (implies
     (putnam-1996-a6-member-p
      (putnam-1996-a6-r-carrier ctx) x)
     (putnam-1996-a6-continuous-at-p
      ctx function x))))

;; Epsilon-delta continuity relative to the closed interval [0,c].

(defun-sk putnam-1996-a6-icc-neighborhood-p
    (ctx function c x epsilon radius)
  (forall (y)
    (implies
     (and
      (putnam-1996-a6-icc-member-p
       ctx (putnam-1996-a6-r-zero ctx) c y)
      (putnam-1996-a6-r-less-p
       ctx
       (putnam-1996-a6-r-absolute-value
        ctx
        (putnam-1996-a6-r-subtract-value ctx y x))
       radius))
     (putnam-1996-a6-r-less-p
      ctx
      (putnam-1996-a6-r-absolute-value
       ctx
       (putnam-1996-a6-r-subtract-value
        ctx
        (putnam-1996-a6-function-value function y)
        (putnam-1996-a6-function-value function x)))
      epsilon))))

(defun-sk putnam-1996-a6-icc-radius-exists-p
    (ctx function c x epsilon)
  (exists (radius)
    (and
     (putnam-1996-a6-positive-real-p ctx radius)
     (putnam-1996-a6-icc-neighborhood-p
      ctx function c x epsilon radius))))

(defun-sk putnam-1996-a6-continuous-within-icc-at-p
    (ctx function c x)
  (forall (epsilon)
    (implies
     (putnam-1996-a6-positive-real-p ctx epsilon)
     (putnam-1996-a6-icc-radius-exists-p
      ctx function c x epsilon))))

(defun-sk putnam-1996-a6-continuous-on-icc-p
    (ctx function c)
  (forall (x)
    (implies
     (putnam-1996-a6-icc-member-p
      ctx (putnam-1996-a6-r-zero ctx) c x)
     (putnam-1996-a6-continuous-within-icc-at-p
      ctx function c x))))

;; Functional equations and the two branches of the classified solution set.

(defun-sk putnam-1996-a6-equation-on-all-reals-p
    (ctx function c)
  (forall (x)
    (implies
     (putnam-1996-a6-member-p
      (putnam-1996-a6-r-carrier ctx) x)
     (equal
      (putnam-1996-a6-function-value function x)
      (putnam-1996-a6-function-value
       function
       (putnam-1996-a6-square-plus-c ctx x c))))))

(defun-sk putnam-1996-a6-equation-on-positive-reals-p
    (ctx function c)
  (forall (x)
    (implies
     (putnam-1996-a6-positive-real-p ctx x)
     (equal
      (putnam-1996-a6-function-value function x)
      (putnam-1996-a6-function-value
       function
       (putnam-1996-a6-square-plus-c ctx x c))))))

(defun-sk putnam-1996-a6-even-on-negative-reals-p
    (ctx function)
  (forall (x)
    (implies
     (and
      (putnam-1996-a6-member-p
       (putnam-1996-a6-r-carrier ctx) x)
      (putnam-1996-a6-r-less-p
       ctx x (putnam-1996-a6-r-zero ctx)))
     (equal
      (putnam-1996-a6-function-value function x)
      (putnam-1996-a6-function-value
       function
       (putnam-1996-a6-r-negate-value ctx x))))))

(defun-sk putnam-1996-a6-constant-value-p
    (ctx function value)
  (forall (x)
    (implies
     (putnam-1996-a6-member-p
      (putnam-1996-a6-r-carrier ctx) x)
     (equal
      (putnam-1996-a6-function-value function x)
      value))))

(defun-sk putnam-1996-a6-constant-function-p
    (ctx function)
  (exists (value)
    (and
     (putnam-1996-a6-member-p
      (putnam-1996-a6-r-carrier ctx) value)
     (putnam-1996-a6-constant-value-p
      ctx function value))))

(defun putnam-1996-a6-large-c-solution-p
    (ctx function c)
  (and
   (putnam-1996-a6-continuous-on-icc-p
    ctx function c)
   (equal
    (putnam-1996-a6-function-value
     function (putnam-1996-a6-r-zero ctx))
    (putnam-1996-a6-function-value function c))
   (putnam-1996-a6-equation-on-positive-reals-p
    ctx function c)
   (putnam-1996-a6-even-on-negative-reals-p
    ctx function)))

(defun putnam-1996-a6-solution-p (ctx function c)
  (if (putnam-1996-a6-r-less-equal-p
       ctx c (putnam-1996-a6-r-quarter ctx))
      (putnam-1996-a6-constant-function-p
       ctx function)
    (putnam-1996-a6-large-c-solution-p
     ctx function c)))

(defun putnambench-putnam-1996-a6-statement
    (ctx c function)
  (implies
   (and
    (putnam-1996-a6-context-p ctx)
    (putnam-1996-a6-positive-real-p ctx c)
    (tamep-functionp function)
    (putnam-1996-a6-real-function-p
     (putnam-1996-a6-r-carrier ctx) function))
   (iff
    (and
     (putnam-1996-a6-continuous-p
      ctx function)
     (putnam-1996-a6-equation-on-all-reals-p
      ctx function c))
    (putnam-1996-a6-solution-p
     ctx function c))))

(value-triple :itpeval-statement-checked)
:q
