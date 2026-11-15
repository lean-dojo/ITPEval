;; Statement-only formalization of PutnamBench corpus artifact putnam_1968_b4:
;; invariance of a convergent symmetric improper integral of a continuous
;; real function under the substitution x |-> x - 1/x. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the full real field as an arbitrary
;; Dedekind-complete ordered field. Functions and subsets are unbounded tame
;; APPLY$ objects, and DEFUN-SK keeps every analytic witness and quantifier
;; internal. On bounded intervals the integrals are defined by convergence of
;; uniform left Riemann sums. For continuous functions these are exactly the
;; corresponding Lebesgue integrals. The transformed truncation is the union
;; [-y,-1/y] U [1/y,y], matching the punctured Lean formulation; endpoints and
;; the single value at zero do not affect the integral.

(defun p68b4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p68b4-unary (operation x)
  (apply$ operation (list x)))

(defun p68b4-binary (operation x y)
  (apply$ operation (list x y)))

(defun p68b4-function-value (function x)
  (apply$ function (list x)))

(defun-sk p68b4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (p68b4-member-p carrier x)
          (p68b4-member-p carrier y)
          (p68b4-member-p carrier z))
     (and
      (p68b4-member-p carrier
                      (p68b4-binary add x y))
      (p68b4-member-p carrier
                      (p68b4-binary multiply x y))
      (p68b4-member-p carrier
                      (p68b4-unary negate x))
      (p68b4-member-p carrier
                      (p68b4-unary inverse x))
      (equal
       (p68b4-binary add (p68b4-binary add x y) z)
       (p68b4-binary add x (p68b4-binary add y z)))
      (equal (p68b4-binary add x y)
             (p68b4-binary add y x))
      (equal (p68b4-binary add x zero) x)
      (equal
       (p68b4-binary add x (p68b4-unary negate x))
       zero)
      (equal
       (p68b4-binary multiply
                      (p68b4-binary multiply x y) z)
       (p68b4-binary multiply
                      x (p68b4-binary multiply y z)))
      (equal (p68b4-binary multiply x y)
             (p68b4-binary multiply y x))
      (equal (p68b4-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p68b4-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p68b4-binary multiply
                       x (p68b4-unary inverse x))
        one))
      (equal
       (p68b4-binary multiply
                      x (p68b4-binary add y z))
       (p68b4-binary add
                     (p68b4-binary multiply x y)
                     (p68b4-binary multiply x z)))))))

(defun-sk p68b4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (p68b4-member-p carrier x)
          (p68b4-member-p carrier y)
          (p68b4-member-p carrier z))
     (and
      (not (p68b4-binary less x x))
      (or (equal x y)
          (p68b4-binary less x y)
          (p68b4-binary less y x))
      (implies
       (and (p68b4-binary less x y)
            (p68b4-binary less y z))
       (p68b4-binary less x z))
      (implies
       (p68b4-binary less x y)
       (p68b4-binary
        less
        (p68b4-binary add x z)
        (p68b4-binary add y z)))
      (implies
       (and (p68b4-binary less zero x)
            (p68b4-binary less zero y))
       (p68b4-binary
        less zero (p68b4-binary multiply x y)))))))

(defun-sk p68b4-set-nonempty-p (carrier set)
  (exists (x)
    (and (p68b4-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk p68b4-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (p68b4-member-p carrier x)
          (apply$ set (list x)))
     (not (p68b4-binary less bound x)))))

(defun-sk p68b4-bounded-above-p (carrier less set)
  (exists (bound)
    (and (p68b4-member-p carrier bound)
         (p68b4-upper-bound-p carrier less set bound))))

(defun-sk p68b4-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p68b4-member-p carrier supremum)
     (p68b4-upper-bound-p carrier less set supremum)
     (implies
      (and (p68b4-member-p carrier bound)
           (p68b4-upper-bound-p carrier less set bound))
      (not (p68b4-binary less bound supremum))))))

(defun-sk p68b4-has-supremum-p (carrier less set)
  (exists (supremum)
    (p68b4-supremum-p carrier less set supremum)))

(defun-sk p68b4-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (p68b4-set-nonempty-p carrier set)
          (p68b4-bounded-above-p carrier less set))
     (p68b4-has-supremum-p carrier less set))))

(defun p68b4-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p68b4-member-p carrier zero)
   (p68b4-member-p carrier one)
   (not (equal zero one))
   (p68b4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p68b4-order-laws-p carrier add multiply zero less)
   (p68b4-binary less zero one)
   (p68b4-dedekind-complete-p carrier less)))

(defun p68b4-add (add x y)
  (p68b4-binary add x y))

(defun p68b4-negate (negate x)
  (p68b4-unary negate x))

(defun p68b4-subtract (add negate x y)
  (p68b4-add add x (p68b4-negate negate y)))

(defun p68b4-multiply (multiply x y)
  (p68b4-binary multiply x y))

(defun p68b4-inverse (inverse x)
  (p68b4-unary inverse x))

(defun p68b4-divide (multiply inverse x y)
  (p68b4-multiply multiply x (p68b4-inverse inverse y)))

(defun p68b4-less-p (less x y)
  (if (p68b4-binary less x y) t nil))

(defun p68b4-less-equal-p (less x y)
  (not (p68b4-less-p less y x)))

(defun p68b4-absolute-value (less negate zero x)
  (if (p68b4-less-p less x zero)
      (p68b4-negate negate x)
    x))

(defun p68b4-positive-p (carrier less zero x)
  (and (p68b4-member-p carrier x)
       (p68b4-less-p less zero x)))

(defun-sk p68b4-function-values-p (carrier function)
  (forall (x)
    (implies
     (p68b4-member-p carrier x)
     (p68b4-member-p
      carrier (p68b4-function-value function x)))))

(defun p68b4-real-function-p (carrier function)
  (and (tamep-functionp function)
       (p68b4-function-values-p carrier function)))

(defun-sk p68b4-continuity-neighborhood-p
    (carrier function add negate zero less
     x epsilon delta)
  (forall (z)
    (implies
     (and
      (p68b4-member-p carrier z)
      (p68b4-less-p
       less
       (p68b4-absolute-value
        less negate zero
        (p68b4-subtract add negate z x))
       delta))
     (p68b4-less-p
      less
      (p68b4-absolute-value
       less negate zero
       (p68b4-subtract
        add negate
        (p68b4-function-value function z)
        (p68b4-function-value function x)))
      epsilon))))

(defun-sk p68b4-continuity-radius-exists-p
    (carrier function add negate zero less x epsilon)
  (exists (delta)
    (and
     (p68b4-positive-p carrier less zero delta)
     (p68b4-continuity-neighborhood-p
      carrier function add negate zero less
      x epsilon delta))))

(defun-sk p68b4-continuous-p
    (carrier function add negate zero less)
  (forall (x epsilon)
    (implies
     (and
      (p68b4-member-p carrier x)
      (p68b4-positive-p carrier less zero epsilon))
     (p68b4-continuity-radius-exists-p
      carrier function add negate zero less
      x epsilon))))

(defun p68b4-nat-multiple (count x zero add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p68b4-add
     add x
     (p68b4-nat-multiple (- count 1) x zero add))))

(defun p68b4-riemann-width
    (subdivisions a b zero one add multiply negate inverse)
  (let ((n-real
         (p68b4-nat-multiple subdivisions one zero add)))
    (p68b4-divide
     multiply inverse
     (p68b4-subtract add negate b a)
     n-real)))

(defun p68b4-riemann-point
    (index subdivisions a b
     zero one add multiply negate inverse)
  (let* ((width
          (p68b4-riemann-width
           subdivisions a b zero one add multiply negate inverse))
         (index-real
          (p68b4-nat-multiple index one zero add)))
    (p68b4-add
     add a
     (p68b4-multiply multiply index-real width))))

(defun p68b4-integrand-value
    (function transformedp x add negate inverse)
  (if transformedp
      (p68b4-function-value
       function
       (p68b4-subtract
        add negate x (p68b4-inverse inverse x)))
    (p68b4-function-value function x)))

(defun p68b4-riemann-sum-aux
    (remaining subdivisions a b function transformedp
     zero one add multiply negate inverse)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      zero
    (let* ((index (- remaining 1))
           (width
            (p68b4-riemann-width
             subdivisions a b
             zero one add multiply negate inverse))
           (point
            (p68b4-riemann-point
             index subdivisions a b
             zero one add multiply negate inverse))
           (summand
            (p68b4-multiply
             multiply width
             (p68b4-integrand-value
              function transformedp point
              add negate inverse))))
      (p68b4-add
       add
       (p68b4-riemann-sum-aux
        index subdivisions a b function transformedp
        zero one add multiply negate inverse)
       summand))))

(defun p68b4-riemann-sum
    (subdivisions a b function transformedp
     zero one add multiply negate inverse)
  (if (posp subdivisions)
      (p68b4-riemann-sum-aux
       subdivisions subdivisions a b function transformedp
       zero one add multiply negate inverse)
    zero))

(defun-sk p68b4-riemann-tail-p
    (function transformedp a b value epsilon cutoff
     zero one add multiply negate inverse less)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (< 0 subdivisions)
      (<= cutoff subdivisions))
     (p68b4-less-p
      less
      (p68b4-absolute-value
       less negate zero
       (p68b4-subtract
        add negate
        (p68b4-riemann-sum
         subdivisions a b function transformedp
         zero one add multiply negate inverse)
        value))
      epsilon))))

(defun-sk p68b4-riemann-cutoff-exists-p
    (function transformedp a b value epsilon
     zero one add multiply negate inverse less)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (p68b4-riemann-tail-p
      function transformedp a b value epsilon cutoff
      zero one add multiply negate inverse less))))

(defun-sk p68b4-riemann-integral-converges-p
    (carrier function transformedp a b value
     zero one add multiply negate inverse less)
  (forall (epsilon)
    (implies
     (p68b4-positive-p carrier less zero epsilon)
     (p68b4-riemann-cutoff-exists-p
      function transformedp a b value epsilon
      zero one add multiply negate inverse less))))

(defun p68b4-interval-integral-p
    (carrier function transformedp a b value
     zero one add multiply negate inverse less)
  (and
   (p68b4-member-p carrier a)
   (p68b4-member-p carrier b)
   (p68b4-member-p carrier value)
   (p68b4-less-equal-p less a b)
   (p68b4-riemann-integral-converges-p
    carrier function transformedp a b value
    zero one add multiply negate inverse less)))

(defun-sk p68b4-original-at-radius-p
    (carrier function radius limit epsilon
     zero one add multiply negate inverse less)
  (exists (value)
    (and
     (p68b4-interval-integral-p
      carrier function nil
      (p68b4-negate negate radius) radius value
      zero one add multiply negate inverse less)
     (p68b4-less-p
      less
      (p68b4-absolute-value
       less negate zero
       (p68b4-subtract add negate value limit))
      epsilon))))

(defun-sk p68b4-original-tail-p
    (carrier function limit epsilon cutoff
     zero one add multiply negate inverse less)
  (forall (radius)
    (implies
     (and
      (p68b4-member-p carrier radius)
      (p68b4-less-equal-p less cutoff radius))
     (p68b4-original-at-radius-p
      carrier function radius limit epsilon
      zero one add multiply negate inverse less))))

(defun-sk p68b4-original-cutoff-exists-p
    (carrier function limit epsilon
     zero one add multiply negate inverse less)
  (exists (cutoff)
    (and
     (p68b4-positive-p carrier less zero cutoff)
     (p68b4-original-tail-p
      carrier function limit epsilon cutoff
      zero one add multiply negate inverse less))))

(defun-sk p68b4-original-limit-p
    (carrier function limit
     zero one add multiply negate inverse less)
  (forall (epsilon)
    (implies
     (p68b4-positive-p carrier less zero epsilon)
     (p68b4-original-cutoff-exists-p
      carrier function limit epsilon
      zero one add multiply negate inverse less))))

(defun-sk p68b4-original-limit-exists-p
    (carrier function
     zero one add multiply negate inverse less)
  (exists (limit)
    (and
     (p68b4-member-p carrier limit)
     (p68b4-original-limit-p
      carrier function limit
      zero one add multiply negate inverse less))))

(defun-sk p68b4-transformed-at-radius-p
    (carrier function radius limit epsilon
     zero one add multiply negate inverse less)
  (exists (left-value right-value)
    (let ((reciprocal
           (p68b4-inverse inverse radius)))
      (and
       (p68b4-interval-integral-p
        carrier function t
        (p68b4-negate negate radius)
        (p68b4-negate negate reciprocal)
        left-value
        zero one add multiply negate inverse less)
       (p68b4-interval-integral-p
        carrier function t
        reciprocal radius right-value
        zero one add multiply negate inverse less)
       (p68b4-less-p
        less
        (p68b4-absolute-value
         less negate zero
         (p68b4-subtract
          add negate
          (p68b4-add add left-value right-value)
          limit))
        epsilon)))))

(defun-sk p68b4-transformed-tail-p
    (carrier function limit epsilon cutoff
     zero one add multiply negate inverse less)
  (forall (radius)
    (implies
     (and
      (p68b4-member-p carrier radius)
      (p68b4-less-equal-p less cutoff radius))
     (p68b4-transformed-at-radius-p
      carrier function radius limit epsilon
      zero one add multiply negate inverse less))))

(defun-sk p68b4-transformed-cutoff-exists-p
    (carrier function limit epsilon
     zero one add multiply negate inverse less)
  (exists (cutoff)
    (and
     (p68b4-member-p carrier cutoff)
     (p68b4-less-equal-p less one cutoff)
     (p68b4-transformed-tail-p
      carrier function limit epsilon cutoff
      zero one add multiply negate inverse less))))

(defun-sk p68b4-transformed-limit-p
    (carrier function limit
     zero one add multiply negate inverse less)
  (forall (epsilon)
    (implies
     (p68b4-positive-p carrier less zero epsilon)
     (p68b4-transformed-cutoff-exists-p
      carrier function limit epsilon
      zero one add multiply negate inverse less))))

(defun-sk p68b4-common-limit-exists-p
    (carrier function
     zero one add multiply negate inverse less)
  (exists (limit)
    (and
     (p68b4-member-p carrier limit)
     (p68b4-transformed-limit-p
      carrier function limit
      zero one add multiply negate inverse less)
     (p68b4-original-limit-p
      carrier function limit
      zero one add multiply negate inverse less))))

(defun putnambench-putnam-1968-b4-statement
    (carrier add multiply negate inverse zero one less function)
  (implies
   (and
    (p68b4-real-field-p
     carrier add multiply negate inverse zero one less)
    (p68b4-real-function-p carrier function)
    (p68b4-continuous-p
     carrier function add negate zero less)
    (p68b4-original-limit-exists-p
     carrier function
     zero one add multiply negate inverse less))
   (p68b4-common-limit-exists-p
    carrier function
    zero one add multiply negate inverse less)))

(value-triple :itpeval-statement-checked)
:q
