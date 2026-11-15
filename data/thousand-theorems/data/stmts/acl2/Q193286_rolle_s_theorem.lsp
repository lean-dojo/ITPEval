;; Statement-only formalization of thousand-theorems corpus artifact Q193286,
;; "Rolle's theorem": a real function continuous on a closed interval with
;; equal endpoint values has an interior point where its derivative is zero.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Real values, real functions, and sets are arbitrary ACL2 objects interpreted
;; by conservative fixed-arity interfaces. The explicit laws below present a
;; Dedekind-complete ordered field, hence the real field, and expand continuity
;; and differentiation by epsilon-delta definitions.

(defstub q193286-real-p (r-type value) t)
(defstub q193286-zero (r-type) t)
(defstub q193286-one (r-type) t)
(defstub q193286-add (r-type left right) t)
(defstub q193286-mul (r-type left right) t)
(defstub q193286-neg (r-type value) t)
(defstub q193286-inv (r-type value) t)
(defstub q193286-lt (r-type left right) t)

(defstub q193286-function-value (r-type function argument) t)
(defstub q193286-set-member-p (r-type set value) t)

(defun q193286-sub (r-type x y)
  (q193286-add r-type x (q193286-neg r-type y)))

(defun q193286-le (r-type x y)
  (not (q193286-lt r-type y x)))

(defun q193286-abs (r-type x)
  (if (q193286-lt r-type x (q193286-zero r-type))
      (q193286-neg r-type x)
    x))

(defun q193286-in-closed-interval-p (r-type a b x)
  (and
   (q193286-real-p r-type x)
   (q193286-le r-type a x)
   (q193286-le r-type x b)))

(defun q193286-in-open-interval-p (r-type a b x)
  (and
   (q193286-real-p r-type x)
   (q193286-lt r-type a x)
   (q193286-lt r-type x b)))

;; A complete ordered-field presentation of the real carrier.

(defun-sk q193286-operation-closure-p (r-type)
  (forall (x y)
    (and
     (q193286-real-p r-type (q193286-zero r-type))
     (q193286-real-p r-type (q193286-one r-type))
     (implies
      (q193286-real-p r-type x)
      (and
       (q193286-real-p r-type (q193286-neg r-type x))
       (q193286-real-p r-type (q193286-inv r-type x))))
     (implies
      (and
       (q193286-real-p r-type x)
       (q193286-real-p r-type y))
      (and
       (q193286-real-p r-type (q193286-add r-type x y))
       (q193286-real-p r-type (q193286-mul r-type x y)))))))

(defun-sk q193286-unary-field-laws-p (r-type)
  (forall (x)
    (implies
     (q193286-real-p r-type x)
     (let ((zero (q193286-zero r-type))
           (one (q193286-one r-type)))
       (and
        (equal (q193286-add r-type zero x) x)
        (equal (q193286-add r-type x zero) x)
        (equal (q193286-add r-type x (q193286-neg r-type x)) zero)
        (equal (q193286-add r-type (q193286-neg r-type x) x) zero)
        (equal (q193286-mul r-type one x) x)
        (equal (q193286-mul r-type x one) x)
        (implies
         (not (equal x zero))
         (and
          (equal
           (q193286-mul r-type x (q193286-inv r-type x))
           one)
          (equal
           (q193286-mul r-type (q193286-inv r-type x) x)
           one))))))))

(defun-sk q193286-binary-field-laws-p (r-type)
  (forall (x y)
    (implies
     (and
      (q193286-real-p r-type x)
      (q193286-real-p r-type y))
     (and
      (equal
       (q193286-add r-type x y)
       (q193286-add r-type y x))
      (equal
       (q193286-mul r-type x y)
       (q193286-mul r-type y x))))))

(defun-sk q193286-ternary-field-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (q193286-real-p r-type x)
      (q193286-real-p r-type y)
      (q193286-real-p r-type z))
     (and
      (equal
       (q193286-add r-type (q193286-add r-type x y) z)
       (q193286-add r-type x (q193286-add r-type y z)))
      (equal
       (q193286-mul r-type (q193286-mul r-type x y) z)
       (q193286-mul r-type x (q193286-mul r-type y z)))
      (equal
       (q193286-mul r-type x (q193286-add r-type y z))
       (q193286-add
        r-type
        (q193286-mul r-type x y)
        (q193286-mul r-type x z)))))))

(defun-sk q193286-order-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (q193286-real-p r-type x)
      (q193286-real-p r-type y)
      (q193286-real-p r-type z))
     (and
      (not (q193286-lt r-type x x))
      (implies
       (and
        (q193286-lt r-type x y)
        (q193286-lt r-type y z))
       (q193286-lt r-type x z))
      (or
       (q193286-lt r-type x y)
       (equal x y)
       (q193286-lt r-type y x))
      (implies
       (q193286-lt r-type x y)
       (q193286-lt
        r-type
        (q193286-add r-type x z)
        (q193286-add r-type y z)))
      (implies
       (and
        (q193286-lt r-type (q193286-zero r-type) x)
        (q193286-lt r-type (q193286-zero r-type) y))
       (q193286-lt
        r-type
        (q193286-zero r-type)
        (q193286-mul r-type x y)))))))

(defun-sk q193286-valid-real-set-p (r-type set)
  (forall (x)
    (implies
     (q193286-set-member-p r-type set x)
     (q193286-real-p r-type x))))

(defun-sk q193286-set-nonempty-p (r-type set)
  (exists (x)
    (and
     (q193286-real-p r-type x)
     (q193286-set-member-p r-type set x))))

(defun-sk q193286-upper-bound-p (r-type set bound)
  (forall (x)
    (implies
     (q193286-set-member-p r-type set x)
     (q193286-le r-type x bound))))

(defun-sk q193286-set-bounded-above-p (r-type set)
  (exists (bound)
    (and
     (q193286-real-p r-type bound)
     (q193286-upper-bound-p r-type set bound))))

(defun-sk q193286-least-upper-bound-p (r-type set supremum)
  (forall (bound)
    (and
     (q193286-real-p r-type supremum)
     (q193286-upper-bound-p r-type set supremum)
     (implies
      (and
       (q193286-real-p r-type bound)
       (q193286-upper-bound-p r-type set bound))
      (q193286-le r-type supremum bound)))))

(defun-sk q193286-supremum-exists-p (r-type set)
  (exists (supremum)
    (and
     (q193286-real-p r-type supremum)
     (q193286-least-upper-bound-p r-type set supremum))))

(defun-sk q193286-dedekind-complete-p (r-type)
  (forall (set)
    (implies
     (and
      (q193286-valid-real-set-p r-type set)
      (q193286-set-nonempty-p r-type set)
      (q193286-set-bounded-above-p r-type set))
     (q193286-supremum-exists-p r-type set))))

(defun q193286-real-structure-p (r-type)
  (and
   (q193286-operation-closure-p r-type)
   (q193286-unary-field-laws-p r-type)
   (q193286-binary-field-laws-p r-type)
   (q193286-ternary-field-laws-p r-type)
   (q193286-order-laws-p r-type)
   (not (equal (q193286-zero r-type) (q193286-one r-type)))
   (q193286-lt
    r-type
    (q193286-zero r-type)
    (q193286-one r-type))
   (q193286-dedekind-complete-p r-type)))

;; The source function has type R -> R.

(defun-sk q193286-real-function-p (r-type function)
  (forall (x)
    (implies
     (q193286-real-p r-type x)
     (q193286-real-p
      r-type
      (q193286-function-value r-type function x)))))

;; ContinuousOn f [a,b], using continuity within the closed interval at each
;; point, including the one-sided endpoint neighborhoods.

(defun-sk q193286-continuity-neighborhood-p
    (r-type function a b x epsilon radius)
  (forall (y)
    (implies
     (and
      (q193286-in-closed-interval-p r-type a b y)
      (q193286-lt
       r-type
       (q193286-abs r-type (q193286-sub r-type y x))
       radius))
     (q193286-lt
      r-type
      (q193286-abs
       r-type
       (q193286-sub
        r-type
        (q193286-function-value r-type function y)
        (q193286-function-value r-type function x)))
      epsilon))))

(defun-sk q193286-continuity-radius-exists-p
    (r-type function a b x epsilon)
  (exists (radius)
    (and
     (q193286-real-p r-type radius)
     (q193286-lt r-type (q193286-zero r-type) radius)
     (q193286-continuity-neighborhood-p
      r-type function a b x epsilon radius))))

(defun-sk q193286-continuous-within-icc-at-p
    (r-type function a b x)
  (forall (epsilon)
    (implies
     (and
      (q193286-real-p r-type epsilon)
      (q193286-lt r-type (q193286-zero r-type) epsilon))
     (q193286-continuity-radius-exists-p
      r-type function a b x epsilon))))

(defun-sk q193286-continuous-on-icc-p
    (r-type function a b)
  (forall (x)
    (implies
     (q193286-in-closed-interval-p r-type a b x)
     (q193286-continuous-within-icc-at-p
      r-type function a b x))))

;; HasDerivAt f d x in epsilon-delta form:
;; |f(y)-f(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun-sk q193286-derivative-neighborhood-p
    (r-type function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (q193286-real-p r-type y)
      (q193286-lt
       r-type
       (q193286-abs r-type (q193286-sub r-type y x))
       radius))
     (q193286-le
      r-type
      (q193286-abs
       r-type
       (q193286-sub
        r-type
        (q193286-sub
         r-type
         (q193286-function-value r-type function y)
         (q193286-function-value r-type function x))
        (q193286-mul
         r-type
         derivative
         (q193286-sub r-type y x))))
      (q193286-mul
       r-type
       epsilon
       (q193286-abs r-type (q193286-sub r-type y x)))))))

(defun-sk q193286-derivative-radius-exists-p
    (r-type function derivative x epsilon)
  (exists (radius)
    (and
     (q193286-real-p r-type radius)
     (q193286-lt r-type (q193286-zero r-type) radius)
     (q193286-derivative-neighborhood-p
      r-type function derivative x epsilon radius))))

(defun-sk q193286-has-derivative-at-p
    (r-type function derivative x)
  (forall (epsilon)
    (implies
     (and
      (q193286-real-p r-type epsilon)
      (q193286-lt r-type (q193286-zero r-type) epsilon))
     (and
      (q193286-real-p r-type derivative)
      (q193286-real-p r-type x)
      (q193286-derivative-radius-exists-p
       r-type function derivative x epsilon)))))

(defun-sk q193286-differentiable-at-p
    (r-type function x)
  (exists (derivative)
    (and
     (q193286-real-p r-type derivative)
     (q193286-has-derivative-at-p
      r-type function derivative x))))

;; Mathlib defines deriv f x to be zero when f is not differentiable at x.
;; Therefore deriv f x = 0 is equivalent to the following disjunction.

(defun q193286-deriv-equals-zero-p
    (r-type function x)
  (or
   (not (q193286-differentiable-at-p r-type function x))
   (q193286-has-derivative-at-p
    r-type function (q193286-zero r-type) x)))

(defun-sk q193286-rolle-witness-exists-p
    (r-type function a b)
  (exists (c)
    (and
     (q193286-in-open-interval-p r-type a b c)
     (q193286-deriv-equals-zero-p r-type function c))))

(defun-sk thousand-theorems-q193286-rolle-s-theorem-statement ()
  (forall (r-type function a b)
    (implies
     (and
      (q193286-real-structure-p r-type)
      (q193286-real-p r-type a)
      (q193286-real-p r-type b)
      (q193286-lt r-type a b)
      (q193286-real-function-p r-type function)
      (q193286-continuous-on-icc-p r-type function a b)
      (equal
       (q193286-function-value r-type function a)
       (q193286-function-value r-type function b)))
     (q193286-rolle-witness-exists-p
      r-type function a b))))

(value-triple :itpeval-statement-checked)

:q
