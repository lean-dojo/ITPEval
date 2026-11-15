;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_a2:
;; the continuous real functions satisfying f(f(x)) = k*x^9 exist exactly for
;; nonnegative real parameters k. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no primitive classical-real sort or higher-order quantifiers. The
;; final predicate therefore takes an exact presentation of the real field as
;; a Dedekind-complete ordered field. Arbitrary subsets and functions use the
;; repository's tame APPLY$ function objects, and DEFUN-SK keeps both the
;; function witness and every epsilon-delta witness internally quantified.

(defun putnam-1979-a2-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1979-a2-unary-value (function x)
  (apply$ function (list x)))

(defun putnam-1979-a2-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk putnam-1979-a2-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1979-a2-member-p carrier x)
      (putnam-1979-a2-member-p carrier y)
      (putnam-1979-a2-member-p carrier z))
     (and
      (putnam-1979-a2-member-p
       carrier
       (putnam-1979-a2-binary-value add x y))
      (putnam-1979-a2-member-p
       carrier
       (putnam-1979-a2-binary-value multiply x y))
      (putnam-1979-a2-member-p
       carrier
       (putnam-1979-a2-unary-value negate x))
      (implies
       (not (equal x zero))
       (putnam-1979-a2-member-p
        carrier
        (putnam-1979-a2-unary-value inverse x)))
      (equal
       (putnam-1979-a2-binary-value
        add
        (putnam-1979-a2-binary-value add x y)
        z)
       (putnam-1979-a2-binary-value
        add
        x
        (putnam-1979-a2-binary-value add y z)))
      (equal
       (putnam-1979-a2-binary-value add x y)
       (putnam-1979-a2-binary-value add y x))
      (equal
       (putnam-1979-a2-binary-value add x zero)
       x)
      (equal
       (putnam-1979-a2-binary-value
        add x (putnam-1979-a2-unary-value negate x))
       zero)
      (equal
       (putnam-1979-a2-binary-value
        multiply
        (putnam-1979-a2-binary-value multiply x y)
        z)
       (putnam-1979-a2-binary-value
        multiply
        x
        (putnam-1979-a2-binary-value multiply y z)))
      (equal
       (putnam-1979-a2-binary-value multiply x y)
       (putnam-1979-a2-binary-value multiply y x))
      (equal
       (putnam-1979-a2-binary-value multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1979-a2-binary-value
         multiply
         x
         (putnam-1979-a2-unary-value inverse x))
        one))
      (equal
       (putnam-1979-a2-binary-value
        multiply
        x
        (putnam-1979-a2-binary-value add y z))
       (putnam-1979-a2-binary-value
        add
        (putnam-1979-a2-binary-value multiply x y)
        (putnam-1979-a2-binary-value multiply x z)))))))

(defun-sk putnam-1979-a2-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (putnam-1979-a2-member-p carrier x)
      (putnam-1979-a2-member-p carrier y)
      (putnam-1979-a2-member-p carrier z))
     (and
      (not (putnam-1979-a2-binary-value less x x))
      (or
       (equal x y)
       (putnam-1979-a2-binary-value less x y)
       (putnam-1979-a2-binary-value less y x))
      (implies
       (and
        (putnam-1979-a2-binary-value less x y)
        (putnam-1979-a2-binary-value less y z))
       (putnam-1979-a2-binary-value less x z))
      (implies
       (putnam-1979-a2-binary-value less x y)
       (putnam-1979-a2-binary-value
        less
        (putnam-1979-a2-binary-value add x z)
        (putnam-1979-a2-binary-value add y z)))
      (implies
       (and
        (putnam-1979-a2-binary-value less zero x)
        (putnam-1979-a2-binary-value less zero y))
       (putnam-1979-a2-binary-value
        less
        zero
        (putnam-1979-a2-binary-value multiply x y)))))))

(defun-sk putnam-1979-a2-set-subset-carrier-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1979-a2-member-p carrier x))))

(defun putnam-1979-a2-valid-set-p (carrier set)
  (and
   (tamep-functionp set)
   (putnam-1979-a2-set-subset-carrier-p carrier set)))

(defun-sk putnam-1979-a2-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1979-a2-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1979-a2-upper-bound-p
    (carrier less set upper)
  (forall (x)
    (implies
     (and
      (putnam-1979-a2-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1979-a2-binary-value less upper x)))))

(defun putnam-1979-a2-is-upper-bound-p
    (carrier less set upper)
  (and
   (putnam-1979-a2-member-p carrier upper)
   (putnam-1979-a2-upper-bound-p
    carrier less set upper)))

(defun-sk putnam-1979-a2-bounded-above-p
    (carrier less set)
  (exists (upper)
    (putnam-1979-a2-is-upper-bound-p
     carrier less set upper)))

(defun-sk putnam-1979-a2-least-upper-bound-p
    (carrier less set supremum)
  (forall (upper)
    (implies
     (putnam-1979-a2-is-upper-bound-p
      carrier less set upper)
     (not
      (putnam-1979-a2-binary-value
       less upper supremum)))))

(defun putnam-1979-a2-supremum-p
    (carrier less set supremum)
  (and
   (putnam-1979-a2-is-upper-bound-p
    carrier less set supremum)
   (putnam-1979-a2-least-upper-bound-p
    carrier less set supremum)))

(defun-sk putnam-1979-a2-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1979-a2-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1979-a2-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (putnam-1979-a2-valid-set-p carrier set)
      (putnam-1979-a2-set-nonempty-p carrier set)
      (putnam-1979-a2-bounded-above-p
       carrier less set))
     (putnam-1979-a2-has-supremum-p
      carrier less set))))

(defun putnam-1979-a2-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1979-a2-member-p carrier zero)
   (putnam-1979-a2-member-p carrier one)
   (not (equal zero one))
   (putnam-1979-a2-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-1979-a2-order-laws-p
    carrier add multiply zero less)
   (putnam-1979-a2-binary-value less zero one)
   (putnam-1979-a2-dedekind-complete-p
    carrier less)))

(defun putnam-1979-a2-subtract
    (add negate left right)
  (putnam-1979-a2-binary-value
   add
   left
   (putnam-1979-a2-unary-value negate right)))

(defun putnam-1979-a2-absolute-value
    (negate zero less value)
  (if (putnam-1979-a2-binary-value less value zero)
      (putnam-1979-a2-unary-value negate value)
    value))

(defun putnam-1979-a2-positive-p
    (carrier zero less value)
  (and
   (putnam-1979-a2-member-p carrier value)
   (putnam-1979-a2-binary-value less zero value)))

(defun-sk putnam-1979-a2-function-values-p
    (carrier function)
  (forall (x)
    (implies
     (putnam-1979-a2-member-p carrier x)
     (putnam-1979-a2-member-p
      carrier
      (putnam-1979-a2-unary-value function x)))))

(defun putnam-1979-a2-real-function-p
    (carrier function)
  (and
   (tamep-functionp function)
   (putnam-1979-a2-function-values-p
    carrier function)))

(defun-sk putnam-1979-a2-continuity-ball-p
    (carrier add negate zero less function
     point epsilon radius)
  (forall (nearby)
    (implies
     (and
      (putnam-1979-a2-member-p carrier nearby)
      (putnam-1979-a2-binary-value
       less
       (putnam-1979-a2-absolute-value
        negate
        zero
        less
        (putnam-1979-a2-subtract
         add negate nearby point))
       radius))
     (putnam-1979-a2-binary-value
      less
      (putnam-1979-a2-absolute-value
       negate
       zero
       less
       (putnam-1979-a2-subtract
        add
        negate
        (putnam-1979-a2-unary-value
         function nearby)
        (putnam-1979-a2-unary-value
         function point)))
      epsilon))))

(defun-sk putnam-1979-a2-continuity-radius-exists-p
    (carrier add negate zero less function
     point epsilon)
  (exists (radius)
    (and
     (putnam-1979-a2-positive-p
      carrier zero less radius)
     (putnam-1979-a2-continuity-ball-p
      carrier add negate zero less function
      point epsilon radius))))

(defun-sk putnam-1979-a2-continuous-p
    (carrier add negate zero less function)
  (forall (point epsilon)
    (implies
     (and
      (putnam-1979-a2-member-p carrier point)
      (putnam-1979-a2-positive-p
       carrier zero less epsilon))
     (putnam-1979-a2-continuity-radius-exists-p
      carrier add negate zero less function
      point epsilon))))

(defun putnam-1979-a2-power
    (multiply one base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1979-a2-binary-value
     multiply
     base
     (putnam-1979-a2-power
      multiply one base (- exponent 1)))))

(defun-sk putnam-1979-a2-functional-equation-p
    (carrier multiply one function k)
  (forall (x)
    (implies
     (putnam-1979-a2-member-p carrier x)
     (equal
      (putnam-1979-a2-unary-value
       function
       (putnam-1979-a2-unary-value function x))
      (putnam-1979-a2-binary-value
       multiply
       k
       (putnam-1979-a2-power
        multiply one x 9))))))

(defun-sk putnam-1979-a2-function-exists-p
    (carrier add multiply negate zero one less k)
  (exists (function)
    (and
     (putnam-1979-a2-real-function-p
      carrier function)
     (putnam-1979-a2-continuous-p
      carrier add negate zero less function)
     (putnam-1979-a2-functional-equation-p
      carrier multiply one function k))))

(defun-sk putnam-1979-a2-classification-p
    (carrier add multiply negate zero one less)
  (forall (k)
    (implies
     (putnam-1979-a2-member-p carrier k)
     (iff
      (putnam-1979-a2-function-exists-p
       carrier add multiply negate zero one less k)
      (not
       (putnam-1979-a2-binary-value
        less k zero))))))

(defun putnambench-putnam-1979-a2-statement
    (carrier add multiply negate inverse zero one less)
  (implies
   (putnam-1979-a2-real-field-p
    carrier add multiply negate inverse zero one less)
   (putnam-1979-a2-classification-p
    carrier add multiply negate zero one less)))

(value-triple :itpeval-statement-checked)
:q
