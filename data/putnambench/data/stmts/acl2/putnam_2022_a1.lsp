;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_a1:
;; the real lines y = a*x+b that meet y = ln(1+x^2) in exactly one point
;; are characterized by the stated conditions on a and b. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context presents a Dedekind-complete ordered field, hence the real
;; field up to ordered-field isomorphism, together with its standard
;; exponential and logarithm. Tame APPLY$ objects represent arbitrary sets
;; and functions extensionally, while DEFUN-SK keeps every unbounded
;; mathematical quantifier internal to the statement.

(defun p22a1-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p22a1-unary-value (function x)
  (apply$ function (list x)))

(defun p22a1-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p22a1-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p22a1-member-p carrier x))))

(defun-sk p22a1-real-function-p (carrier function)
  (forall (x)
    (implies
     (p22a1-member-p carrier x)
     (p22a1-member-p
      carrier
      (p22a1-unary-value function x)))))

(defun-sk p22a1-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p22a1-member-p carrier x)
      (p22a1-member-p carrier y)
      (p22a1-member-p carrier z))
     (and
      (p22a1-member-p carrier
                      (p22a1-binary-value add x y))
      (p22a1-member-p carrier
                      (p22a1-binary-value multiply x y))
      (p22a1-member-p carrier
                      (p22a1-unary-value negate x))
      (p22a1-member-p carrier
                      (p22a1-unary-value inverse x))
      (equal
       (p22a1-binary-value
        add (p22a1-binary-value add x y) z)
       (p22a1-binary-value
        add x (p22a1-binary-value add y z)))
      (equal
       (p22a1-binary-value add x y)
       (p22a1-binary-value add y x))
      (equal (p22a1-binary-value add x zero) x)
      (equal
       (p22a1-binary-value
        add x (p22a1-unary-value negate x))
       zero)
      (equal
       (p22a1-binary-value
        multiply (p22a1-binary-value multiply x y) z)
       (p22a1-binary-value
        multiply x (p22a1-binary-value multiply y z)))
      (equal
       (p22a1-binary-value multiply x y)
       (p22a1-binary-value multiply y x))
      (equal (p22a1-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p22a1-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p22a1-binary-value
         multiply x (p22a1-unary-value inverse x))
        one))
      (equal
       (p22a1-binary-value
        multiply x (p22a1-binary-value add y z))
       (p22a1-binary-value
        add
        (p22a1-binary-value multiply x y)
        (p22a1-binary-value multiply x z)))))))

(defun-sk p22a1-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p22a1-member-p carrier x)
      (p22a1-member-p carrier y)
      (p22a1-member-p carrier z))
     (and
      (not (p22a1-binary-value less x x))
      (or
       (equal x y)
       (p22a1-binary-value less x y)
       (p22a1-binary-value less y x))
      (implies
       (and
        (p22a1-binary-value less x y)
        (p22a1-binary-value less y z))
       (p22a1-binary-value less x z))
      (implies
       (p22a1-binary-value less x y)
       (p22a1-binary-value
        less
        (p22a1-binary-value add x z)
        (p22a1-binary-value add y z)))
      (implies
       (and
        (p22a1-binary-value less zero x)
        (p22a1-binary-value less zero y))
       (p22a1-binary-value
        less zero (p22a1-binary-value multiply x y)))))))

(defun-sk p22a1-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p22a1-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p22a1-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p22a1-member-p carrier x)
      (apply$ set (list x)))
     (not (p22a1-binary-value less bound x)))))

(defun-sk p22a1-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p22a1-member-p carrier bound)
     (p22a1-upper-bound-p
      carrier less set bound))))

(defun-sk p22a1-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p22a1-member-p carrier bound)
      (p22a1-upper-bound-p carrier less set bound))
     (not (p22a1-binary-value less bound supremum)))))

(defun p22a1-supremum-p
    (carrier less set supremum)
  (and
   (p22a1-member-p carrier supremum)
   (p22a1-upper-bound-p carrier less set supremum)
   (p22a1-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p22a1-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p22a1-supremum-p
     carrier less set supremum)))

(defun-sk p22a1-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p22a1-valid-set-p carrier set)
      (p22a1-set-nonempty-p carrier set)
      (p22a1-bounded-above-p carrier less set))
     (p22a1-has-supremum-p carrier less set))))

(defun p22a1-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p22a1-member-p carrier zero)
   (p22a1-member-p carrier one)
   (not (equal zero one))
   (p22a1-field-laws-p
    carrier add multiply negate inverse zero one)
   (p22a1-order-laws-p
    carrier add multiply zero less)
   (p22a1-binary-value less zero one)
   (p22a1-dedekind-complete-p carrier less)))

;; The outer context is
;; (field-context exponential logarithm square-root).

(defun p22a1-field-context (ctx)
  (nth 0 ctx))

(defun p22a1-r-carrier (ctx)
  (nth 0 (p22a1-field-context ctx)))

(defun p22a1-r-zero (ctx)
  (nth 1 (p22a1-field-context ctx)))

(defun p22a1-r-one (ctx)
  (nth 2 (p22a1-field-context ctx)))

(defun p22a1-r-add (ctx)
  (nth 3 (p22a1-field-context ctx)))

(defun p22a1-r-mul (ctx)
  (nth 4 (p22a1-field-context ctx)))

(defun p22a1-r-neg (ctx)
  (nth 5 (p22a1-field-context ctx)))

(defun p22a1-r-inv (ctx)
  (nth 6 (p22a1-field-context ctx)))

(defun p22a1-r-lt (ctx)
  (nth 7 (p22a1-field-context ctx)))

(defun p22a1-r-exp (ctx)
  (nth 1 ctx))

(defun p22a1-r-log (ctx)
  (nth 2 ctx))

(defun p22a1-r-sqrt (ctx)
  (nth 3 ctx))

(defun p22a1-field-context-p (field-context)
  (and
   (true-listp field-context)
   (equal (len field-context) 8)
   (p22a1-real-field-p
    (nth 0 field-context)
    (nth 1 field-context)
    (nth 2 field-context)
    (nth 3 field-context)
    (nth 4 field-context)
    (nth 5 field-context)
    (nth 6 field-context)
    (nth 7 field-context))))

(defun p22a1-r-add-value (ctx x y)
  (p22a1-binary-value (p22a1-r-add ctx) x y))

(defun p22a1-r-neg-value (ctx x)
  (p22a1-unary-value (p22a1-r-neg ctx) x))

(defun p22a1-r-sub-value (ctx x y)
  (p22a1-r-add-value
   ctx x (p22a1-r-neg-value ctx y)))

(defun p22a1-r-mul-value (ctx x y)
  (p22a1-binary-value (p22a1-r-mul ctx) x y))

(defun p22a1-r-inv-value (ctx x)
  (p22a1-unary-value (p22a1-r-inv ctx) x))

(defun p22a1-r-div-value (ctx numerator denominator)
  (p22a1-r-mul-value
   ctx numerator (p22a1-r-inv-value ctx denominator)))

(defun p22a1-r-lt-p (ctx x y)
  (if (p22a1-binary-value (p22a1-r-lt ctx) x y)
      t nil))

(defun p22a1-r-le-p (ctx x y)
  (not (p22a1-r-lt-p ctx y x)))

(defun p22a1-r-abs-value (ctx x)
  (if (p22a1-r-lt-p ctx x (p22a1-r-zero ctx))
      (p22a1-r-neg-value ctx x)
    x))

(defun p22a1-positive-real-p (ctx x)
  (and
   (p22a1-member-p (p22a1-r-carrier ctx) x)
   (p22a1-r-lt-p ctx (p22a1-r-zero ctx) x)))

;; HasDerivAt in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun-sk p22a1-derivative-neighborhood-p
    (ctx function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p22a1-member-p (p22a1-r-carrier ctx) y)
      (p22a1-r-lt-p
       ctx
       (p22a1-r-abs-value
        ctx (p22a1-r-sub-value ctx y x))
       radius))
     (p22a1-r-le-p
      ctx
      (p22a1-r-abs-value
       ctx
       (p22a1-r-sub-value
        ctx
        (p22a1-r-sub-value
         ctx
         (p22a1-unary-value function y)
         (p22a1-unary-value function x))
        (p22a1-r-mul-value
         ctx derivative
         (p22a1-r-sub-value ctx y x))))
      (p22a1-r-mul-value
       ctx epsilon
       (p22a1-r-abs-value
        ctx (p22a1-r-sub-value ctx y x)))))))

(defun-sk p22a1-derivative-radius-exists-p
    (ctx function derivative x epsilon)
  (exists (radius)
    (and
     (p22a1-positive-real-p ctx radius)
     (p22a1-derivative-neighborhood-p
      ctx function derivative x epsilon radius))))

(defun-sk p22a1-derivative-epsilon-p
    (ctx function derivative x)
  (forall (epsilon)
    (implies
     (p22a1-positive-real-p ctx epsilon)
     (p22a1-derivative-radius-exists-p
      ctx function derivative x epsilon))))

(defun p22a1-has-derivative-at-p
    (ctx function derivative x)
  (and
   (p22a1-member-p (p22a1-r-carrier ctx) derivative)
   (p22a1-member-p (p22a1-r-carrier ctx) x)
   (p22a1-derivative-epsilon-p
    ctx function derivative x)))

(defun-sk p22a1-derivative-exists-at-p
    (ctx function x)
  (exists (derivative)
    (p22a1-has-derivative-at-p
     ctx function derivative x)))

(defun-sk p22a1-differentiable-on-positive-p
    (ctx function)
  (forall (x)
    (implies
     (p22a1-positive-real-p ctx x)
     (p22a1-derivative-exists-at-p
      ctx function x))))

;; The differential initial-value problem E' = E, E(0) = 1 characterizes the
;; standard real exponential. LOG is its inverse on the positive reals.

(defun-sk p22a1-exponential-laws-p (ctx)
  (forall (x)
    (implies
     (p22a1-member-p (p22a1-r-carrier ctx) x)
     (and
      (p22a1-positive-real-p
       ctx (p22a1-unary-value (p22a1-r-exp ctx) x))
      (p22a1-has-derivative-at-p
       ctx
       (p22a1-r-exp ctx)
       (p22a1-unary-value (p22a1-r-exp ctx) x)
       x)))))

(defun p22a1-exponential-function-p (ctx)
  (and
   (tamep-functionp (p22a1-r-exp ctx))
   (p22a1-real-function-p
    (p22a1-r-carrier ctx) (p22a1-r-exp ctx))
   (equal
    (p22a1-unary-value
     (p22a1-r-exp ctx) (p22a1-r-zero ctx))
    (p22a1-r-one ctx))
   (p22a1-exponential-laws-p ctx)))

(defun-sk p22a1-logarithm-laws-p (ctx)
  (forall (x)
    (implies
     (p22a1-member-p (p22a1-r-carrier ctx) x)
     (and
      (equal
       (p22a1-unary-value
        (p22a1-r-log ctx)
        (p22a1-unary-value (p22a1-r-exp ctx) x))
       x)
      (implies
       (p22a1-positive-real-p ctx x)
       (equal
        (p22a1-unary-value
         (p22a1-r-exp ctx)
         (p22a1-unary-value (p22a1-r-log ctx) x))
        x))))))

(defun p22a1-logarithm-function-p (ctx)
  (and
   (tamep-functionp (p22a1-r-log ctx))
   (p22a1-real-function-p
    (p22a1-r-carrier ctx) (p22a1-r-log ctx))
   (p22a1-logarithm-laws-p ctx)))

(defun p22a1-r-square-value (ctx x)
  (p22a1-r-mul-value ctx x x))

(defun-sk p22a1-square-root-laws-p (ctx)
  (forall (x)
    (implies
     (and
      (p22a1-member-p (p22a1-r-carrier ctx) x)
      (p22a1-r-le-p ctx (p22a1-r-zero ctx) x))
     (let ((root
            (p22a1-unary-value (p22a1-r-sqrt ctx) x)))
       (and
        (p22a1-r-le-p ctx (p22a1-r-zero ctx) root)
        (equal (p22a1-r-square-value ctx root) x))))))

(defun p22a1-square-root-function-p (ctx)
  (and
   (tamep-functionp (p22a1-r-sqrt ctx))
   (p22a1-real-function-p
    (p22a1-r-carrier ctx) (p22a1-r-sqrt ctx))
   (p22a1-square-root-laws-p ctx)))

(defun p22a1-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 4)
   (p22a1-field-context-p (p22a1-field-context ctx))
   (p22a1-exponential-function-p ctx)
   (p22a1-logarithm-function-p ctx)
   (p22a1-square-root-function-p ctx)))

;; The equation a*x+b = ln(1+x^2), with exact unique existence.

(defun p22a1-intersection-p (ctx a b x)
  (and
   (p22a1-member-p (p22a1-r-carrier ctx) x)
   (equal
    (p22a1-r-add-value
     ctx (p22a1-r-mul-value ctx a x) b)
    (p22a1-unary-value
     (p22a1-r-log ctx)
     (p22a1-r-add-value
      ctx
      (p22a1-r-one ctx)
      (p22a1-r-square-value ctx x))))))

(defun-sk p22a1-only-intersection-p (ctx a b x)
  (forall (y)
    (implies
     (p22a1-intersection-p ctx a b y)
     (equal y x))))

(defun-sk p22a1-exactly-one-intersection-p (ctx a b)
  (exists (x)
    (and
     (p22a1-intersection-p ctx a b x)
     (p22a1-only-intersection-p ctx a b x))))

;; Explicit classification from the published problem. For 0 < |a| < 1,
;; RMIN and RMAX are the two critical points of ln(1+x^2)-a*x.

(defun p22a1-rmin (ctx a root)
  (p22a1-r-div-value
   ctx
   (p22a1-r-sub-value ctx (p22a1-r-one ctx) root)
   a))

(defun p22a1-rmax (ctx a root)
  (p22a1-r-div-value
   ctx
   (p22a1-r-add-value ctx (p22a1-r-one ctx) root)
   a))

(defun p22a1-critical-value (ctx a x)
  (p22a1-r-sub-value
   ctx
   (p22a1-unary-value
    (p22a1-r-log ctx)
    (p22a1-r-add-value
     ctx
     (p22a1-r-one ctx)
     (p22a1-r-square-value ctx x)))
   (p22a1-r-mul-value ctx a x)))

(defun p22a1-middle-solution-p (ctx a b absolute-a)
  (let* ((one-minus-a-square
          (p22a1-r-sub-value
           ctx
           (p22a1-r-one ctx)
           (p22a1-r-square-value ctx a)))
         (root
          (p22a1-unary-value
           (p22a1-r-sqrt ctx)
           one-minus-a-square))
         (rmin (p22a1-rmin ctx a root))
         (rmax (p22a1-rmax ctx a root)))
    (and
     (p22a1-r-lt-p ctx (p22a1-r-zero ctx) absolute-a)
     (p22a1-r-lt-p ctx absolute-a (p22a1-r-one ctx))
     (or
      (p22a1-r-lt-p
       ctx b (p22a1-critical-value ctx a rmin))
      (p22a1-r-lt-p
       ctx (p22a1-critical-value ctx a rmax) b)))))

(defun p22a1-solution-member-p (ctx a b)
  (let ((absolute-a (p22a1-r-abs-value ctx a)))
    (or
     (and
      (equal a (p22a1-r-zero ctx))
      (equal b (p22a1-r-zero ctx)))
     (p22a1-r-le-p ctx (p22a1-r-one ctx) absolute-a)
     (p22a1-middle-solution-p ctx a b absolute-a))))

;; ACL2 universally closes CTX, A, and B. The IFF is the pointwise form of
;; equality between the set of uniquely intersecting pairs and the displayed
;; solution set.
(defun putnambench-putnam-2022-a1-statement (ctx a b)
  (implies
   (and
    (p22a1-context-p ctx)
    (p22a1-member-p (p22a1-r-carrier ctx) a)
    (p22a1-member-p (p22a1-r-carrier ctx) b))
   (iff
    (p22a1-exactly-one-intersection-p ctx a b)
    (p22a1-solution-member-p ctx a b))))

(value-triple :itpeval-statement-checked)
:q
