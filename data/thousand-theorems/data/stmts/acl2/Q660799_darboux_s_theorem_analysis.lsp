;; Statement-only formalization of thousand-theorems corpus artifact Q660799,
;; "Darboux's theorem (analysis)": derivatives of real functions have the
;; intermediate-value property on intervals, order-connected sets, and convex
;; sets, in HasDerivWithinAt, derivWithin, and deriv forms. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Real values, real functions, and sets are arbitrary ACL2 objects interpreted
;; by conservative fixed-arity interfaces. The explicit laws below present a
;; Dedekind-complete ordered field, hence the real field. Differentiation
;; within arbitrary sets and closed intervals is expanded by its epsilon-delta
;; remainder definition. Conservative DEFCHOOSE events retain the canonical
;; derivative-value witnesses internally for the derivWithin and deriv forms.

(defstub q660799-real-p (r-type value) t)
(defstub q660799-zero (r-type) t)
(defstub q660799-one (r-type) t)
(defstub q660799-add (r-type left right) t)
(defstub q660799-mul (r-type left right) t)
(defstub q660799-neg (r-type value) t)
(defstub q660799-inv (r-type value) t)
(defstub q660799-lt (r-type left right) t)

(defstub q660799-function-value (r-type function argument) t)
(defstub q660799-set-member-p (r-type set value) t)

(defun q660799-sub (r-type x y)
  (q660799-add r-type x (q660799-neg r-type y)))

(defun q660799-le (r-type x y)
  (not (q660799-lt r-type y x)))

(defun q660799-abs (r-type x)
  (if (q660799-lt r-type x (q660799-zero r-type))
      (q660799-neg r-type x)
    x))

(defun q660799-in-closed-interval-p (r-type a b x)
  (and
   (q660799-real-p r-type x)
   (q660799-le r-type a x)
   (q660799-le r-type x b)))

(defun q660799-in-open-interval-p (r-type a b x)
  (and
   (q660799-real-p r-type x)
   (q660799-lt r-type a x)
   (q660799-lt r-type x b)))

;; A complete ordered-field presentation of the real carrier.

(defun-sk q660799-operation-closure-p (r-type)
  (forall (x y)
    (and
     (q660799-real-p r-type (q660799-zero r-type))
     (q660799-real-p r-type (q660799-one r-type))
     (implies
      (q660799-real-p r-type x)
      (and
       (q660799-real-p r-type (q660799-neg r-type x))
       (q660799-real-p r-type (q660799-inv r-type x))))
     (implies
      (and
       (q660799-real-p r-type x)
       (q660799-real-p r-type y))
      (and
       (q660799-real-p r-type (q660799-add r-type x y))
       (q660799-real-p r-type (q660799-mul r-type x y)))))))

(defun-sk q660799-unary-field-laws-p (r-type)
  (forall (x)
    (implies
     (q660799-real-p r-type x)
     (let ((zero (q660799-zero r-type))
           (one (q660799-one r-type)))
       (and
        (equal (q660799-add r-type zero x) x)
        (equal (q660799-add r-type x zero) x)
        (equal (q660799-add r-type x (q660799-neg r-type x)) zero)
        (equal (q660799-add r-type (q660799-neg r-type x) x) zero)
        (equal (q660799-mul r-type one x) x)
        (equal (q660799-mul r-type x one) x)
        (implies
         (not (equal x zero))
         (and
          (equal
           (q660799-mul r-type x (q660799-inv r-type x))
           one)
          (equal
           (q660799-mul r-type (q660799-inv r-type x) x)
           one))))))))

(defun-sk q660799-binary-field-laws-p (r-type)
  (forall (x y)
    (implies
     (and
      (q660799-real-p r-type x)
      (q660799-real-p r-type y))
     (and
      (equal
       (q660799-add r-type x y)
       (q660799-add r-type y x))
      (equal
       (q660799-mul r-type x y)
       (q660799-mul r-type y x))))))

(defun-sk q660799-ternary-field-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (q660799-real-p r-type x)
      (q660799-real-p r-type y)
      (q660799-real-p r-type z))
     (and
      (equal
       (q660799-add r-type (q660799-add r-type x y) z)
       (q660799-add r-type x (q660799-add r-type y z)))
      (equal
       (q660799-mul r-type (q660799-mul r-type x y) z)
       (q660799-mul r-type x (q660799-mul r-type y z)))
      (equal
       (q660799-mul r-type x (q660799-add r-type y z))
       (q660799-add
        r-type
        (q660799-mul r-type x y)
        (q660799-mul r-type x z)))))))

(defun-sk q660799-order-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (q660799-real-p r-type x)
      (q660799-real-p r-type y)
      (q660799-real-p r-type z))
     (and
      (not (q660799-lt r-type x x))
      (implies
       (and
        (q660799-lt r-type x y)
        (q660799-lt r-type y z))
       (q660799-lt r-type x z))
      (or
       (q660799-lt r-type x y)
       (equal x y)
       (q660799-lt r-type y x))
      (implies
       (q660799-lt r-type x y)
       (q660799-lt
        r-type
        (q660799-add r-type x z)
        (q660799-add r-type y z)))
      (implies
       (and
        (q660799-lt r-type (q660799-zero r-type) x)
        (q660799-lt r-type (q660799-zero r-type) y))
       (q660799-lt
        r-type
        (q660799-zero r-type)
        (q660799-mul r-type x y)))))))

(defun-sk q660799-valid-real-set-p (r-type set)
  (forall (x)
    (implies
     (q660799-set-member-p r-type set x)
     (q660799-real-p r-type x))))

(defun-sk q660799-set-nonempty-p (r-type set)
  (exists (x)
    (and
     (q660799-real-p r-type x)
     (q660799-set-member-p r-type set x))))

(defun-sk q660799-upper-bound-p (r-type set bound)
  (forall (x)
    (implies
     (q660799-set-member-p r-type set x)
     (q660799-le r-type x bound))))

(defun-sk q660799-set-bounded-above-p (r-type set)
  (exists (bound)
    (and
     (q660799-real-p r-type bound)
     (q660799-upper-bound-p r-type set bound))))

(defun-sk q660799-least-upper-bound-p (r-type set supremum)
  (forall (bound)
    (and
     (q660799-real-p r-type supremum)
     (q660799-upper-bound-p r-type set supremum)
     (implies
      (and
       (q660799-real-p r-type bound)
       (q660799-upper-bound-p r-type set bound))
      (q660799-le r-type supremum bound)))))

(defun-sk q660799-supremum-exists-p (r-type set)
  (exists (supremum)
    (and
     (q660799-real-p r-type supremum)
     (q660799-least-upper-bound-p r-type set supremum))))

(defun-sk q660799-dedekind-complete-p (r-type)
  (forall (set)
    (implies
     (and
      (q660799-valid-real-set-p r-type set)
      (q660799-set-nonempty-p r-type set)
      (q660799-set-bounded-above-p r-type set))
     (q660799-supremum-exists-p r-type set))))

(defun q660799-real-structure-p (r-type)
  (and
   (q660799-operation-closure-p r-type)
   (q660799-unary-field-laws-p r-type)
   (q660799-binary-field-laws-p r-type)
   (q660799-ternary-field-laws-p r-type)
   (q660799-order-laws-p r-type)
   (not (equal (q660799-zero r-type) (q660799-one r-type)))
   (q660799-lt
    r-type
    (q660799-zero r-type)
    (q660799-one r-type))
   (q660799-dedekind-complete-p r-type)))

;; The source function has type R -> R.

(defun-sk q660799-real-function-p (r-type function)
  (forall (x)
    (implies
     (q660799-real-p r-type x)
     (q660799-real-p
      r-type
      (q660799-function-value r-type function x)))))

;; The norm-linear derivative remainder
;;   f(y) - f(x) - derivative * (y - x).

(defun q660799-derivative-remainder
    (r-type function derivative x y)
  (q660799-sub
   r-type
   (q660799-sub
    r-type
    (q660799-function-value r-type function y)
    (q660799-function-value r-type function x))
   (q660799-mul
    r-type derivative (q660799-sub r-type y x))))

;; HasDerivWithinAt f derivative set x, expanded by the epsilon-delta
;; remainder condition over points y belonging to set.

(defun-sk q660799-derivative-within-neighborhood-p
    (r-type function derivative set x epsilon radius)
  (forall (y)
    (implies
     (and
      (q660799-real-p r-type y)
      (q660799-set-member-p r-type set y)
      (q660799-lt
       r-type
       (q660799-abs r-type (q660799-sub r-type y x))
       radius))
     (q660799-le
      r-type
      (q660799-abs
       r-type
       (q660799-derivative-remainder
        r-type function derivative x y))
      (q660799-mul
       r-type epsilon
       (q660799-abs r-type (q660799-sub r-type y x)))))))

(defun-sk q660799-derivative-within-radius-exists-p
    (r-type function derivative set x epsilon)
  (exists (radius)
    (and
     (q660799-real-p r-type radius)
     (q660799-lt r-type (q660799-zero r-type) radius)
     (q660799-derivative-within-neighborhood-p
      r-type function derivative set x epsilon radius))))

(defun-sk q660799-has-deriv-within-at-p
    (r-type function derivative set x)
  (forall (epsilon)
    (implies
     (and
      (q660799-real-p r-type epsilon)
      (q660799-lt r-type (q660799-zero r-type) epsilon))
     (and
      (q660799-real-p r-type derivative)
      (q660799-real-p r-type x)
      (q660799-derivative-within-radius-exists-p
       r-type function derivative set x epsilon)))))

;; The corresponding closed-interval specialization.

(defun-sk q660799-derivative-icc-neighborhood-p
    (r-type function derivative a b x epsilon radius)
  (forall (y)
    (implies
     (and
      (q660799-in-closed-interval-p r-type a b y)
      (q660799-lt
       r-type
       (q660799-abs r-type (q660799-sub r-type y x))
       radius))
     (q660799-le
      r-type
      (q660799-abs
       r-type
       (q660799-derivative-remainder
        r-type function derivative x y))
      (q660799-mul
       r-type epsilon
       (q660799-abs r-type (q660799-sub r-type y x)))))))

(defun-sk q660799-derivative-icc-radius-exists-p
    (r-type function derivative a b x epsilon)
  (exists (radius)
    (and
     (q660799-real-p r-type radius)
     (q660799-lt r-type (q660799-zero r-type) radius)
     (q660799-derivative-icc-neighborhood-p
      r-type function derivative a b x epsilon radius))))

(defun-sk q660799-has-deriv-within-icc-at-p
    (r-type function derivative a b x)
  (forall (epsilon)
    (implies
     (and
      (q660799-real-p r-type epsilon)
      (q660799-lt r-type (q660799-zero r-type) epsilon))
     (and
      (q660799-real-p r-type derivative)
      (q660799-real-p r-type x)
      (q660799-derivative-icc-radius-exists-p
       r-type function derivative a b x epsilon)))))

(defun-sk q660799-derivative-function-on-icc-p
    (r-type function derivative-function a b)
  (forall (x)
    (implies
     (q660799-in-closed-interval-p r-type a b x)
     (q660799-has-deriv-within-icc-at-p
      r-type
      function
      (q660799-function-value r-type derivative-function x)
      a b x))))

(defun-sk q660799-derivative-function-on-set-p
    (r-type function derivative-function set)
  (forall (x)
    (implies
     (and
      (q660799-real-p r-type x)
      (q660799-set-member-p r-type set x))
     (q660799-has-deriv-within-at-p
      r-type
      function
      (q660799-function-value r-type derivative-function x)
      set x))))

;; Differentiability within a set and the conservative internal choice used
;; for mathlib's derivWithin value under a DifferentiableOn hypothesis.

(defun-sk q660799-differentiable-within-at-p
    (r-type function set x)
  (exists (derivative)
    (and
     (q660799-real-p r-type derivative)
     (q660799-has-deriv-within-at-p
      r-type function derivative set x))))

(defun-sk q660799-differentiable-on-set-p
    (r-type function set)
  (forall (x)
    (implies
     (and
      (q660799-real-p r-type x)
      (q660799-set-member-p r-type set x))
     (q660799-differentiable-within-at-p
      r-type function set x))))

(defchoose q660799-deriv-within-value
    (derivative)
    (r-type function set x)
  (and
   (q660799-real-p r-type derivative)
   (q660799-has-deriv-within-at-p
    r-type function derivative set x)))

;; HasDerivAt and deriv use the full real carrier as the limiting domain.

(defun-sk q660799-derivative-at-neighborhood-p
    (r-type function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (q660799-real-p r-type y)
      (q660799-lt
       r-type
       (q660799-abs r-type (q660799-sub r-type y x))
       radius))
     (q660799-le
      r-type
      (q660799-abs
       r-type
       (q660799-derivative-remainder
        r-type function derivative x y))
      (q660799-mul
       r-type epsilon
       (q660799-abs r-type (q660799-sub r-type y x)))))))

(defun-sk q660799-derivative-at-radius-exists-p
    (r-type function derivative x epsilon)
  (exists (radius)
    (and
     (q660799-real-p r-type radius)
     (q660799-lt r-type (q660799-zero r-type) radius)
     (q660799-derivative-at-neighborhood-p
      r-type function derivative x epsilon radius))))

(defun-sk q660799-has-deriv-at-p
    (r-type function derivative x)
  (forall (epsilon)
    (implies
     (and
      (q660799-real-p r-type epsilon)
      (q660799-lt r-type (q660799-zero r-type) epsilon))
     (and
      (q660799-real-p r-type derivative)
      (q660799-real-p r-type x)
      (q660799-derivative-at-radius-exists-p
       r-type function derivative x epsilon)))))

(defun-sk q660799-differentiable-at-p
    (r-type function x)
  (exists (derivative)
    (and
     (q660799-real-p r-type derivative)
     (q660799-has-deriv-at-p
      r-type function derivative x))))

(defun-sk q660799-differentiable-at-on-set-p
    (r-type function set)
  (forall (x)
    (implies
     (and
      (q660799-real-p r-type x)
      (q660799-set-member-p r-type set x))
     (q660799-differentiable-at-p r-type function x))))

(defchoose q660799-deriv-value
    (derivative)
    (r-type function x)
  (and
   (q660799-real-p r-type derivative)
   (q660799-has-deriv-at-p
    r-type function derivative x)))

;; Order-connected and convex subsets of the real line.

(defun q660799-between-p (r-type left middle right)
  (and
   (q660799-real-p r-type middle)
   (or
    (and
     (q660799-le r-type left middle)
     (q660799-le r-type middle right))
    (and
     (q660799-le r-type right middle)
     (q660799-le r-type middle left)))))

(defun-sk q660799-ord-connected-p (r-type set)
  (forall (left right middle)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-between-p r-type left middle right))
     (q660799-set-member-p r-type set middle))))

(defun q660799-convex-combination
    (r-type left right weight)
  (q660799-add
   r-type
   (q660799-mul
    r-type
    (q660799-sub r-type (q660799-one r-type) weight)
    left)
   (q660799-mul r-type weight right)))

(defun-sk q660799-convex-p (r-type set)
  (forall (left right weight)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-real-p r-type weight)
      (q660799-le r-type (q660799-zero r-type) weight)
      (q660799-le r-type weight (q660799-one r-type)))
     (q660799-set-member-p
      r-type set
      (q660799-convex-combination
       r-type left right weight)))))

;; Existential image witnesses for the supplied derivative function.

(defun-sk q660799-function-image-witness-exists-p
    (r-type value-function set target)
  (exists (point)
    (and
     (q660799-real-p r-type point)
     (q660799-set-member-p r-type set point)
     (equal
      (q660799-function-value r-type value-function point)
      target))))

(defun-sk q660799-function-image-ord-connected-p
    (r-type value-function set)
  (forall (left right middle)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-between-p
       r-type
       (q660799-function-value r-type value-function left)
       middle
       (q660799-function-value r-type value-function right)))
     (q660799-function-image-witness-exists-p
      r-type value-function set middle))))

(defun-sk q660799-function-image-convex-p
    (r-type value-function set)
  (forall (left right weight)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-real-p r-type weight)
      (q660799-le r-type (q660799-zero r-type) weight)
      (q660799-le r-type weight (q660799-one r-type)))
     (q660799-function-image-witness-exists-p
      r-type
      value-function
      set
      (q660799-convex-combination
       r-type
       (q660799-function-value r-type value-function left)
       (q660799-function-value r-type value-function right)
       weight)))))

;; Image witnesses for the internally selected derivWithin values.

(defun-sk q660799-deriv-within-image-witness-exists-p
    (r-type function set target)
  (exists (point)
    (and
     (q660799-real-p r-type point)
     (q660799-set-member-p r-type set point)
     (equal
      (q660799-deriv-within-value r-type function set point)
      target))))

(defun-sk q660799-deriv-within-image-ord-connected-p
    (r-type function set)
  (forall (left right middle)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-between-p
       r-type
       (q660799-deriv-within-value
        r-type function set left)
       middle
       (q660799-deriv-within-value
        r-type function set right)))
     (q660799-deriv-within-image-witness-exists-p
      r-type function set middle))))

(defun-sk q660799-deriv-within-image-convex-p
    (r-type function set)
  (forall (left right weight)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-real-p r-type weight)
      (q660799-le r-type (q660799-zero r-type) weight)
      (q660799-le r-type weight (q660799-one r-type)))
     (q660799-deriv-within-image-witness-exists-p
      r-type
      function
      set
      (q660799-convex-combination
       r-type
       (q660799-deriv-within-value
        r-type function set left)
       (q660799-deriv-within-value
        r-type function set right)
       weight)))))

;; Image witnesses for the internally selected unrestricted deriv values.

(defun-sk q660799-deriv-image-witness-exists-p
    (r-type function set target)
  (exists (point)
    (and
     (q660799-real-p r-type point)
     (q660799-set-member-p r-type set point)
     (equal
      (q660799-deriv-value r-type function point)
      target))))

(defun-sk q660799-deriv-image-ord-connected-p
    (r-type function set)
  (forall (left right middle)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-between-p
       r-type
       (q660799-deriv-value r-type function left)
       middle
       (q660799-deriv-value r-type function right)))
     (q660799-deriv-image-witness-exists-p
      r-type function set middle))))

(defun-sk q660799-deriv-image-convex-p
    (r-type function set)
  (forall (left right weight)
    (implies
     (and
      (q660799-set-member-p r-type set left)
      (q660799-set-member-p r-type set right)
      (q660799-real-p r-type weight)
      (q660799-le r-type (q660799-zero r-type) weight)
      (q660799-le r-type weight (q660799-one r-type)))
     (q660799-deriv-image-witness-exists-p
      r-type
      function
      set
      (q660799-convex-combination
       r-type
       (q660799-deriv-value r-type function left)
       (q660799-deriv-value r-type function right)
       weight)))))

;; Interval image conclusions, with the attaining point kept existential.

(defun-sk q660799-open-interval-image-witness-exists-p
    (r-type derivative-function a b target)
  (exists (point)
    (and
     (q660799-in-open-interval-p r-type a b point)
     (equal
      (q660799-function-value r-type derivative-function point)
      target))))

(defun-sk q660799-closed-interval-image-witness-exists-p
    (r-type derivative-function a b target)
  (exists (point)
    (and
     (q660799-in-closed-interval-p r-type a b point)
     (equal
      (q660799-function-value r-type derivative-function point)
      target))))

;; exists_hasDerivWithinAt_eq_of_gt_of_lt
(defun-sk
    thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-gt-of-lt-statement
    ()
  (forall (r-type function derivative-function a b target)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-real-p r-type a)
      (q660799-real-p r-type b)
      (q660799-real-p r-type target)
      (q660799-le r-type a b)
      (q660799-real-function-p r-type function)
      (q660799-real-function-p r-type derivative-function)
      (q660799-derivative-function-on-icc-p
       r-type function derivative-function a b)
      (q660799-lt
       r-type
       (q660799-function-value
        r-type derivative-function a)
       target)
      (q660799-lt
       r-type
       target
       (q660799-function-value
        r-type derivative-function b)))
     (q660799-open-interval-image-witness-exists-p
      r-type derivative-function a b target))))

;; exists_hasDerivWithinAt_eq_of_lt_of_gt
(defun-sk
    thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-lt-of-gt-statement
    ()
  (forall (r-type function derivative-function a b target)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-real-p r-type a)
      (q660799-real-p r-type b)
      (q660799-real-p r-type target)
      (q660799-le r-type a b)
      (q660799-real-function-p r-type function)
      (q660799-real-function-p r-type derivative-function)
      (q660799-derivative-function-on-icc-p
       r-type function derivative-function a b)
      (q660799-lt
       r-type
       target
       (q660799-function-value
        r-type derivative-function a))
      (q660799-lt
       r-type
       (q660799-function-value
        r-type derivative-function b)
       target))
     (q660799-open-interval-image-witness-exists-p
      r-type derivative-function a b target))))

;; Set.OrdConnected.image_hasDerivWithinAt
(defun-sk
    thousand-theorems-q660799-set-ord-connected-image-has-deriv-within-at-statement
    ()
  (forall (r-type function derivative-function set)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-valid-real-set-p r-type set)
      (q660799-real-function-p r-type function)
      (q660799-real-function-p r-type derivative-function)
      (q660799-ord-connected-p r-type set)
      (q660799-derivative-function-on-set-p
       r-type function derivative-function set))
     (q660799-function-image-ord-connected-p
      r-type derivative-function set))))

;; Set.OrdConnected.image_derivWithin
(defun-sk
    thousand-theorems-q660799-set-ord-connected-image-deriv-within-statement
    ()
  (forall (r-type function set)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-valid-real-set-p r-type set)
      (q660799-real-function-p r-type function)
      (q660799-ord-connected-p r-type set)
      (q660799-differentiable-on-set-p
       r-type function set))
     (q660799-deriv-within-image-ord-connected-p
      r-type function set))))

;; Set.OrdConnected.image_deriv
(defun-sk
    thousand-theorems-q660799-set-ord-connected-image-deriv-statement
    ()
  (forall (r-type function set)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-valid-real-set-p r-type set)
      (q660799-real-function-p r-type function)
      (q660799-ord-connected-p r-type set)
      (q660799-differentiable-at-on-set-p
       r-type function set))
     (q660799-deriv-image-ord-connected-p
      r-type function set))))

;; Convex.image_hasDerivWithinAt
(defun-sk
    thousand-theorems-q660799-convex-image-has-deriv-within-at-statement
    ()
  (forall (r-type function derivative-function set)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-valid-real-set-p r-type set)
      (q660799-real-function-p r-type function)
      (q660799-real-function-p r-type derivative-function)
      (q660799-convex-p r-type set)
      (q660799-derivative-function-on-set-p
       r-type function derivative-function set))
     (q660799-function-image-convex-p
      r-type derivative-function set))))

;; Convex.image_derivWithin
(defun-sk
    thousand-theorems-q660799-convex-image-deriv-within-statement
    ()
  (forall (r-type function set)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-valid-real-set-p r-type set)
      (q660799-real-function-p r-type function)
      (q660799-convex-p r-type set)
      (q660799-differentiable-on-set-p
       r-type function set))
     (q660799-deriv-within-image-convex-p
      r-type function set))))

;; Convex.image_deriv
(defun-sk
    thousand-theorems-q660799-convex-image-deriv-statement
    ()
  (forall (r-type function set)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-valid-real-set-p r-type set)
      (q660799-real-function-p r-type function)
      (q660799-convex-p r-type set)
      (q660799-differentiable-at-on-set-p
       r-type function set))
     (q660799-deriv-image-convex-p
      r-type function set))))

;; exists_hasDerivWithinAt_eq_of_ge_of_le
(defun-sk
    thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-ge-of-le-statement
    ()
  (forall (r-type function derivative-function a b target)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-real-p r-type a)
      (q660799-real-p r-type b)
      (q660799-real-p r-type target)
      (q660799-le r-type a b)
      (q660799-real-function-p r-type function)
      (q660799-real-function-p r-type derivative-function)
      (q660799-derivative-function-on-icc-p
       r-type function derivative-function a b)
      (q660799-le
       r-type
       (q660799-function-value
        r-type derivative-function a)
       target)
      (q660799-le
       r-type
       target
       (q660799-function-value
        r-type derivative-function b)))
     (q660799-closed-interval-image-witness-exists-p
      r-type derivative-function a b target))))

;; exists_hasDerivWithinAt_eq_of_le_of_ge
;; The indexed Lean source has the same formal endpoint inequalities as the
;; preceding theorem, despite the reversed prose description in its docstring.
(defun-sk
    thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-le-of-ge-statement
    ()
  (forall (r-type function derivative-function a b target)
    (implies
     (and
      (q660799-real-structure-p r-type)
      (q660799-real-p r-type a)
      (q660799-real-p r-type b)
      (q660799-real-p r-type target)
      (q660799-le r-type a b)
      (q660799-real-function-p r-type function)
      (q660799-real-function-p r-type derivative-function)
      (q660799-derivative-function-on-icc-p
       r-type function derivative-function a b)
      (q660799-le
       r-type
       (q660799-function-value
        r-type derivative-function a)
       target)
      (q660799-le
       r-type
       target
       (q660799-function-value
        r-type derivative-function b)))
     (q660799-closed-interval-image-witness-exists-p
      r-type derivative-function a b target))))

;; The corpus artifact is the conjunction of exactly the ten indexed source
;; statements above.
(defun thousand-theorems-q660799-darboux-s-theorem-analysis-statement ()
  (and
   (thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-gt-of-lt-statement)
   (thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-lt-of-gt-statement)
   (thousand-theorems-q660799-set-ord-connected-image-has-deriv-within-at-statement)
   (thousand-theorems-q660799-set-ord-connected-image-deriv-within-statement)
   (thousand-theorems-q660799-set-ord-connected-image-deriv-statement)
   (thousand-theorems-q660799-convex-image-has-deriv-within-at-statement)
   (thousand-theorems-q660799-convex-image-deriv-within-statement)
   (thousand-theorems-q660799-convex-image-deriv-statement)
   (thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-ge-of-le-statement)
   (thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-le-of-ge-statement)))

(value-triple :itpeval-statement-checked)

:q
