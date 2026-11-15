;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__079, "The Intermediate Value Theorem": every
;; continuous real-valued function on a closed real interval attains each real
;; value between its endpoint values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present a Dedekind-complete ordered field, hence the
;; real field up to ordered-field isomorphism. APPLY$ objects retain arbitrary
;; carriers, subsets, and functions, while DEFUN-SK keeps all mathematical
;; quantifiers, including the attaining point, internal to the statement.

(defun ht079-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun ht079-unary-value (operation x)
  (apply$ operation (list x)))

(defun ht079-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk ht079-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (ht079-member-p carrier x))))

(defun-sk ht079-real-function-p (carrier function)
  (forall (x)
    (implies
     (ht079-member-p carrier x)
     (ht079-member-p
      carrier
      (ht079-unary-value function x)))))

(defun-sk ht079-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (ht079-member-p carrier x)
          (ht079-member-p carrier y)
          (ht079-member-p carrier z))
     (and
      (ht079-member-p carrier
                      (ht079-binary-value add x y))
      (ht079-member-p carrier
                      (ht079-binary-value multiply x y))
      (ht079-member-p carrier
                      (ht079-unary-value negate x))
      (implies
       (not (equal x zero))
       (ht079-member-p carrier
                       (ht079-unary-value inverse x)))
      (equal
       (ht079-binary-value
        add (ht079-binary-value add x y) z)
       (ht079-binary-value
        add x (ht079-binary-value add y z)))
      (equal (ht079-binary-value add x y)
             (ht079-binary-value add y x))
      (equal (ht079-binary-value add x zero) x)
      (equal
       (ht079-binary-value
        add x (ht079-unary-value negate x))
       zero)
      (equal
       (ht079-binary-value
        multiply
        (ht079-binary-value multiply x y)
        z)
       (ht079-binary-value
        multiply
        x
        (ht079-binary-value multiply y z)))
      (equal (ht079-binary-value multiply x y)
             (ht079-binary-value multiply y x))
      (equal (ht079-binary-value multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (ht079-binary-value
         multiply x (ht079-unary-value inverse x))
        one))
      (equal
       (ht079-binary-value
        multiply x (ht079-binary-value add y z))
       (ht079-binary-value
        add
        (ht079-binary-value multiply x y)
        (ht079-binary-value multiply x z)))))))

(defun-sk ht079-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (ht079-member-p carrier x)
          (ht079-member-p carrier y)
          (ht079-member-p carrier z))
     (and
      (not (ht079-binary-value less x x))
      (or (equal x y)
          (ht079-binary-value less x y)
          (ht079-binary-value less y x))
      (implies
       (and (ht079-binary-value less x y)
            (ht079-binary-value less y z))
       (ht079-binary-value less x z))
      (implies
       (ht079-binary-value less x y)
       (ht079-binary-value
        less
        (ht079-binary-value add x z)
        (ht079-binary-value add y z)))
      (implies
       (and (ht079-binary-value less zero x)
            (ht079-binary-value less zero y))
       (ht079-binary-value
        less
        zero
        (ht079-binary-value multiply x y)))))))

(defun-sk ht079-set-nonempty-p (carrier set)
  (exists (x)
    (and (ht079-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk ht079-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and (ht079-member-p carrier x)
          (apply$ set (list x)))
     (not (ht079-binary-value less bound x)))))

(defun-sk ht079-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (ht079-member-p carrier bound)
     (ht079-upper-bound-p
      carrier less set bound))))

(defun-sk ht079-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (ht079-member-p carrier supremum)
     (ht079-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (ht079-member-p carrier bound)
       (ht079-upper-bound-p
        carrier less set bound))
      (not
       (ht079-binary-value
        less bound supremum))))))

(defun-sk ht079-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (ht079-supremum-p
     carrier less set supremum)))

(defun-sk ht079-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (ht079-valid-set-p carrier set)
      (ht079-set-nonempty-p carrier set)
      (ht079-bounded-above-p carrier less set))
     (ht079-has-supremum-p
      carrier less set))))

(defun ht079-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (ht079-member-p carrier zero)
   (ht079-member-p carrier one)
   (not (equal zero one))
   (ht079-field-laws-p
    carrier add multiply negate inverse zero one)
   (ht079-order-laws-p
    carrier add multiply zero less)
   (ht079-binary-value less zero one)
   (ht079-dedekind-complete-p carrier less)))

;; Real-field context and arithmetic.

(defun ht079-r-carrier (ctx) (nth 0 ctx))
(defun ht079-r-zero (ctx) (nth 1 ctx))
(defun ht079-r-one (ctx) (nth 2 ctx))
(defun ht079-r-add (ctx) (nth 3 ctx))
(defun ht079-r-mul (ctx) (nth 4 ctx))
(defun ht079-r-neg (ctx) (nth 5 ctx))
(defun ht079-r-inv (ctx) (nth 6 ctx))
(defun ht079-r-lt (ctx) (nth 7 ctx))

(defun ht079-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (ht079-real-field-p
    (ht079-r-carrier ctx)
    (ht079-r-add ctx)
    (ht079-r-mul ctx)
    (ht079-r-neg ctx)
    (ht079-r-inv ctx)
    (ht079-r-zero ctx)
    (ht079-r-one ctx)
    (ht079-r-lt ctx))))

(defun ht079-r-add-value (ctx x y)
  (ht079-binary-value (ht079-r-add ctx) x y))

(defun ht079-r-neg-value (ctx x)
  (ht079-unary-value (ht079-r-neg ctx) x))

(defun ht079-r-sub-value (ctx x y)
  (ht079-r-add-value
   ctx x (ht079-r-neg-value ctx y)))

(defun ht079-r-lt-p (ctx x y)
  (if (ht079-binary-value
       (ht079-r-lt ctx) x y)
      t nil))

(defun ht079-r-le-p (ctx x y)
  (not (ht079-r-lt-p ctx y x)))

(defun ht079-r-abs-value (ctx x)
  (if (ht079-r-lt-p
       ctx x (ht079-r-zero ctx))
      (ht079-r-neg-value ctx x)
    x))

(defun ht079-positive-real-p (ctx x)
  (and
   (ht079-member-p (ht079-r-carrier ctx) x)
   (ht079-r-lt-p ctx (ht079-r-zero ctx) x)))

(defun ht079-icc-member-p (ctx a b x)
  (and
   (ht079-member-p (ht079-r-carrier ctx) x)
   (ht079-r-le-p ctx a x)
   (ht079-r-le-p ctx x b)))

;; Epsilon-delta continuity relative to the closed interval [a,b].

(defun-sk ht079-continuity-neighborhood-p
    (ctx function a b x epsilon radius)
  (forall (y)
    (implies
     (and
      (ht079-icc-member-p ctx a b y)
      (ht079-r-lt-p
       ctx
       (ht079-r-abs-value
        ctx (ht079-r-sub-value ctx y x))
       radius))
     (ht079-r-lt-p
      ctx
      (ht079-r-abs-value
       ctx
       (ht079-r-sub-value
        ctx
        (ht079-unary-value function y)
        (ht079-unary-value function x)))
      epsilon))))

(defun-sk ht079-continuity-radius-exists-p
    (ctx function a b x epsilon)
  (exists (radius)
    (and
     (ht079-positive-real-p ctx radius)
     (ht079-continuity-neighborhood-p
      ctx function a b x epsilon radius))))

(defun-sk ht079-continuous-within-icc-at-p
    (ctx function a b x)
  (forall (epsilon)
    (implies
     (ht079-positive-real-p ctx epsilon)
     (ht079-continuity-radius-exists-p
      ctx function a b x epsilon))))

(defun-sk ht079-continuous-on-icc-p
    (ctx function a b)
  (forall (x)
    (implies
     (ht079-icc-member-p ctx a b x)
     (ht079-continuous-within-icc-at-p
      ctx function a b x))))

(defun ht079-between-p (ctx left middle right)
  (or
   (and (ht079-r-le-p ctx left middle)
        (ht079-r-le-p ctx middle right))
   (and (ht079-r-le-p ctx right middle)
        (ht079-r-le-p ctx middle left))))

(defun-sk ht079-attaining-point-exists-p
    (ctx function a b target)
  (exists (x)
    (and
     (ht079-icc-member-p ctx a b x)
     (equal
      (ht079-unary-value function x)
      target))))

(defun hundred-theorems-079-intermediate-value-theorem-statement
    (ctx function a b target)
  (implies
   (and
    (ht079-context-p ctx)
    (ht079-member-p (ht079-r-carrier ctx) a)
    (ht079-member-p (ht079-r-carrier ctx) b)
    (ht079-member-p (ht079-r-carrier ctx) target)
    (ht079-r-le-p ctx a b)
    (tamep-functionp function)
    (ht079-real-function-p
     (ht079-r-carrier ctx) function)
    (ht079-continuous-on-icc-p
     ctx function a b)
    (ht079-between-p
     ctx
     (ht079-unary-value function a)
     target
     (ht079-unary-value function b)))
   (ht079-attaining-point-exists-p
    ctx function a b target)))

(value-triple :itpeval-statement-checked)
:q
