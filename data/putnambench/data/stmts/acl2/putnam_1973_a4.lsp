;; Statement-only formalization of PutnamBench corpus artifact putnam_1973_a4:
;; the real function 2^x - 1 - x^2 has exactly three distinct zeros on the
;; real line. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A context presents a Dedekind-complete ordered field, hence the real field
;; up to ordered-field isomorphism. Its final operation is base-2 real
;; exponentiation. Positivity, normalization at 0 and 1, the exponential
;; addition law, and strict monotonicity uniquely characterize x |-> 2^x.
;; Thus the operation is not an uninterpreted surrogate or a restriction to
;; rational exponents.

(defun putnam-1973-a4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1973-a4-unary-value (operation x)
  (apply$ operation (list x)))

(defun putnam-1973-a4-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk putnam-1973-a4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1973-a4-member-p carrier x))))

(defun-sk putnam-1973-a4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (putnam-1973-a4-member-p carrier x)
          (putnam-1973-a4-member-p carrier y)
          (putnam-1973-a4-member-p carrier z))
     (and
      (putnam-1973-a4-member-p
       carrier
       (putnam-1973-a4-binary-value add x y))
      (putnam-1973-a4-member-p
       carrier
       (putnam-1973-a4-binary-value multiply x y))
      (putnam-1973-a4-member-p
       carrier
       (putnam-1973-a4-unary-value negate x))
      (implies
       (not (equal x zero))
       (putnam-1973-a4-member-p
        carrier
        (putnam-1973-a4-unary-value inverse x)))
      (equal
       (putnam-1973-a4-binary-value
        add
        (putnam-1973-a4-binary-value add x y)
        z)
       (putnam-1973-a4-binary-value
        add
        x
        (putnam-1973-a4-binary-value add y z)))
      (equal
       (putnam-1973-a4-binary-value add x y)
       (putnam-1973-a4-binary-value add y x))
      (equal
       (putnam-1973-a4-binary-value add x zero)
       x)
      (equal
       (putnam-1973-a4-binary-value
        add x (putnam-1973-a4-unary-value negate x))
       zero)
      (equal
       (putnam-1973-a4-binary-value
        multiply
        (putnam-1973-a4-binary-value multiply x y)
        z)
       (putnam-1973-a4-binary-value
        multiply
        x
        (putnam-1973-a4-binary-value multiply y z)))
      (equal
       (putnam-1973-a4-binary-value multiply x y)
       (putnam-1973-a4-binary-value multiply y x))
      (equal
       (putnam-1973-a4-binary-value multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1973-a4-binary-value
         multiply
         x
         (putnam-1973-a4-unary-value inverse x))
        one))
      (equal
       (putnam-1973-a4-binary-value
        multiply
        x
        (putnam-1973-a4-binary-value add y z))
       (putnam-1973-a4-binary-value
        add
        (putnam-1973-a4-binary-value multiply x y)
        (putnam-1973-a4-binary-value multiply x z)))))))

(defun-sk putnam-1973-a4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (putnam-1973-a4-member-p carrier x)
          (putnam-1973-a4-member-p carrier y)
          (putnam-1973-a4-member-p carrier z))
     (and
      (not (putnam-1973-a4-binary-value less x x))
      (or (equal x y)
          (putnam-1973-a4-binary-value less x y)
          (putnam-1973-a4-binary-value less y x))
      (implies
       (and (putnam-1973-a4-binary-value less x y)
            (putnam-1973-a4-binary-value less y z))
       (putnam-1973-a4-binary-value less x z))
      (implies
       (putnam-1973-a4-binary-value less x y)
       (putnam-1973-a4-binary-value
        less
        (putnam-1973-a4-binary-value add x z)
        (putnam-1973-a4-binary-value add y z)))
      (implies
       (and (putnam-1973-a4-binary-value less zero x)
            (putnam-1973-a4-binary-value less zero y))
       (putnam-1973-a4-binary-value
        less
        zero
        (putnam-1973-a4-binary-value multiply x y)))))))

(defun-sk putnam-1973-a4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1973-a4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1973-a4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1973-a4-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1973-a4-binary-value less bound x)))))

(defun-sk putnam-1973-a4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1973-a4-member-p carrier bound)
     (putnam-1973-a4-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1973-a4-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1973-a4-member-p carrier supremum)
     (putnam-1973-a4-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1973-a4-member-p carrier bound)
       (putnam-1973-a4-upper-bound-p
        carrier less set bound))
      (not
       (putnam-1973-a4-binary-value
        less bound supremum))))))

(defun-sk putnam-1973-a4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1973-a4-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1973-a4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1973-a4-valid-set-p carrier set)
      (putnam-1973-a4-set-nonempty-p carrier set)
      (putnam-1973-a4-bounded-above-p
       carrier less set))
     (putnam-1973-a4-has-supremum-p
      carrier less set))))

(defun putnam-1973-a4-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1973-a4-member-p carrier zero)
   (putnam-1973-a4-member-p carrier one)
   (not (equal zero one))
   (putnam-1973-a4-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-1973-a4-order-laws-p
    carrier add multiply zero less)
   (putnam-1973-a4-binary-value less zero one)
   (putnam-1973-a4-dedekind-complete-p
    carrier less)))

;; Context layout:
;; (carrier zero one add multiply negate inverse less power-of-two).

(defun putnam-1973-a4-carrier (ctx) (nth 0 ctx))
(defun putnam-1973-a4-zero (ctx) (nth 1 ctx))
(defun putnam-1973-a4-one (ctx) (nth 2 ctx))
(defun putnam-1973-a4-add (ctx) (nth 3 ctx))
(defun putnam-1973-a4-multiply (ctx) (nth 4 ctx))
(defun putnam-1973-a4-negate (ctx) (nth 5 ctx))
(defun putnam-1973-a4-inverse (ctx) (nth 6 ctx))
(defun putnam-1973-a4-less (ctx) (nth 7 ctx))
(defun putnam-1973-a4-power-of-two (ctx) (nth 8 ctx))

(defun putnam-1973-a4-add-value (ctx x y)
  (putnam-1973-a4-binary-value
   (putnam-1973-a4-add ctx) x y))

(defun putnam-1973-a4-multiply-value (ctx x y)
  (putnam-1973-a4-binary-value
   (putnam-1973-a4-multiply ctx) x y))

(defun putnam-1973-a4-negate-value (ctx x)
  (putnam-1973-a4-unary-value
   (putnam-1973-a4-negate ctx) x))

(defun putnam-1973-a4-subtract-value (ctx x y)
  (putnam-1973-a4-add-value
   ctx x (putnam-1973-a4-negate-value ctx y)))

(defun putnam-1973-a4-power-of-two-value (ctx x)
  (putnam-1973-a4-unary-value
   (putnam-1973-a4-power-of-two ctx) x))

(defun-sk putnam-1973-a4-power-of-two-laws-p (ctx)
  (forall (x y)
    (implies
     (and
      (putnam-1973-a4-member-p
       (putnam-1973-a4-carrier ctx) x)
      (putnam-1973-a4-member-p
       (putnam-1973-a4-carrier ctx) y))
     (let* ((zero (putnam-1973-a4-zero ctx))
            (one (putnam-1973-a4-one ctx))
            (two (putnam-1973-a4-add-value
                  ctx one one))
            (power-x
             (putnam-1973-a4-power-of-two-value ctx x))
            (power-y
             (putnam-1973-a4-power-of-two-value ctx y)))
       (and
        (putnam-1973-a4-member-p
         (putnam-1973-a4-carrier ctx) power-x)
        (putnam-1973-a4-binary-value
         (putnam-1973-a4-less ctx) zero power-x)
        (equal
         (putnam-1973-a4-power-of-two-value ctx zero)
         one)
        (equal
         (putnam-1973-a4-power-of-two-value ctx one)
         two)
        (equal
         (putnam-1973-a4-power-of-two-value
          ctx
          (putnam-1973-a4-add-value ctx x y))
         (putnam-1973-a4-multiply-value
          ctx power-x power-y))
        (implies
         (putnam-1973-a4-binary-value
          (putnam-1973-a4-less ctx) x y)
         (putnam-1973-a4-binary-value
          (putnam-1973-a4-less ctx)
          power-x power-y)))))))

(defun putnam-1973-a4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 9)
   (putnam-1973-a4-real-field-p
    (putnam-1973-a4-carrier ctx)
    (putnam-1973-a4-zero ctx)
    (putnam-1973-a4-one ctx)
    (putnam-1973-a4-add ctx)
    (putnam-1973-a4-multiply ctx)
    (putnam-1973-a4-negate ctx)
    (putnam-1973-a4-inverse ctx)
    (putnam-1973-a4-less ctx))
   (tamep-functionp
    (putnam-1973-a4-power-of-two ctx))
   (putnam-1973-a4-power-of-two-laws-p ctx)))

(defun putnam-1973-a4-root-p (ctx x)
  (and
   (putnam-1973-a4-member-p
    (putnam-1973-a4-carrier ctx) x)
   (equal
    (putnam-1973-a4-subtract-value
     ctx
     (putnam-1973-a4-subtract-value
      ctx
      (putnam-1973-a4-power-of-two-value ctx x)
      (putnam-1973-a4-one ctx))
     (putnam-1973-a4-multiply-value ctx x x))
    (putnam-1973-a4-zero ctx))))

(defun-sk putnam-1973-a4-all-roots-covered-p
    (ctx first second third)
  (forall (x)
    (implies
     (putnam-1973-a4-root-p ctx x)
     (or (equal x first)
         (equal x second)
         (equal x third)))))

(defun-sk putnam-1973-a4-exactly-three-roots-p (ctx)
  (exists (first second third)
    (and
     (putnam-1973-a4-root-p ctx first)
     (putnam-1973-a4-root-p ctx second)
     (putnam-1973-a4-root-p ctx third)
     (not (equal first second))
     (not (equal first third))
     (not (equal second third))
     (putnam-1973-a4-all-roots-covered-p
      ctx first second third))))

(defun putnambench-putnam-1973-a4-statement (ctx)
  (implies
   (putnam-1973-a4-context-p ctx)
   (putnam-1973-a4-exactly-three-roots-p ctx)))

(value-triple :itpeval-statement-checked)
:q
