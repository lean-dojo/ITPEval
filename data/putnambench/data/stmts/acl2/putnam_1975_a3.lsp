;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_a3:
;; the explicit points where x^a + y^b + z^c attains its maximum and minimum
;; on the nonnegative real surface x^b + y^b + z^b = 1 for 0 < a < b < c.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. Positive-base
;; real powers are fixed uniquely by their rational values and continuity in
;; the exponent; the zero-base law covers the positive exponents used below.
;; Thus POWER denotes the source real-power operation on every relevant input.

(defun putnam-1975-a3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1975-a3-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1975-a3-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1975-a3-positive-p (carrier less zero x)
  (and
   (putnam-1975-a3-member-p carrier x)
   (apply$ less (list zero x))))

(defun putnam-1975-a3-nonnegative-p (carrier less zero x)
  (and
   (putnam-1975-a3-member-p carrier x)
   (not (apply$ less (list x zero)))))

(defun-sk putnam-1975-a3-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1975-a3-member-p carrier x)
      (putnam-1975-a3-member-p carrier y)
      (putnam-1975-a3-member-p carrier z))
     (and
      (putnam-1975-a3-member-p
       carrier (putnam-1975-a3-binary add x y))
      (putnam-1975-a3-member-p
       carrier (putnam-1975-a3-binary multiply x y))
      (putnam-1975-a3-member-p
       carrier (putnam-1975-a3-unary negate x))
      (putnam-1975-a3-member-p
       carrier (putnam-1975-a3-unary inverse x))
      (equal
       (putnam-1975-a3-binary
        add (putnam-1975-a3-binary add x y) z)
       (putnam-1975-a3-binary
        add x (putnam-1975-a3-binary add y z)))
      (equal
       (putnam-1975-a3-binary add x y)
       (putnam-1975-a3-binary add y x))
      (equal (putnam-1975-a3-binary add x zero) x)
      (equal
       (putnam-1975-a3-binary
        add x (putnam-1975-a3-unary negate x))
       zero)
      (equal
       (putnam-1975-a3-binary
        multiply (putnam-1975-a3-binary multiply x y) z)
       (putnam-1975-a3-binary
        multiply x (putnam-1975-a3-binary multiply y z)))
      (equal
       (putnam-1975-a3-binary multiply x y)
       (putnam-1975-a3-binary multiply y x))
      (equal (putnam-1975-a3-binary multiply x one) x)
      (equal (putnam-1975-a3-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1975-a3-binary
         multiply x (putnam-1975-a3-unary inverse x))
        one))
      (equal
       (putnam-1975-a3-binary
        multiply x (putnam-1975-a3-binary add y z))
       (putnam-1975-a3-binary
        add
        (putnam-1975-a3-binary multiply x y)
        (putnam-1975-a3-binary multiply x z)))))))

(defun-sk putnam-1975-a3-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1975-a3-member-p carrier x)
      (putnam-1975-a3-member-p carrier y)
      (putnam-1975-a3-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or
       (equal x y)
       (apply$ less (list x y))
       (apply$ less (list y x)))
      (implies
       (and
        (apply$ less (list x y))
        (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$
        less
        (list
         (putnam-1975-a3-binary add x z)
         (putnam-1975-a3-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list zero
              (putnam-1975-a3-binary multiply x y))))))))

(defun-sk putnam-1975-a3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1975-a3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1975-a3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1975-a3-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1975-a3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1975-a3-member-p carrier bound)
     (putnam-1975-a3-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1975-a3-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1975-a3-member-p carrier supremum)
     (putnam-1975-a3-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1975-a3-member-p carrier bound)
       (putnam-1975-a3-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1975-a3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1975-a3-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1975-a3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1975-a3-set-nonempty-p carrier set)
      (putnam-1975-a3-bounded-above-p carrier less set))
     (putnam-1975-a3-has-supremum-p
      carrier less set))))

(defun putnam-1975-a3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1975-a3-member-p carrier zero)
   (putnam-1975-a3-member-p carrier one)
   (not (equal zero one))
   (putnam-1975-a3-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1975-a3-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (putnam-1975-a3-dedekind-complete-p carrier less)))

(defun putnam-1975-a3-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1975-a3-binary
     add one
     (putnam-1975-a3-natural (- n 1) zero one add))))

(defun putnam-1975-a3-integer
    (n zero one add negate)
  (if (< n 0)
      (putnam-1975-a3-unary
       negate
       (putnam-1975-a3-natural (- n) zero one add))
    (putnam-1975-a3-natural n zero one add)))

(defun putnam-1975-a3-natural-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1975-a3-binary
     multiply
     (putnam-1975-a3-natural-power
      base (- exponent 1) one multiply)
     base)))

(defun putnam-1975-a3-integer-power
    (base exponent one multiply inverse)
  (if (< exponent 0)
      (putnam-1975-a3-unary
       inverse
       (putnam-1975-a3-natural-power
        base (- exponent) one multiply))
    (putnam-1975-a3-natural-power
     base exponent one multiply)))

(defun-sk putnam-1975-a3-power-typing-p
    (carrier zero less power)
  (forall (base exponent)
    (implies
     (and
      (putnam-1975-a3-positive-p carrier less zero base)
      (putnam-1975-a3-member-p carrier exponent))
     (putnam-1975-a3-positive-p
      carrier less zero
      (putnam-1975-a3-binary power base exponent)))))

(defun-sk putnam-1975-a3-power-rational-laws-p
    (carrier zero one add multiply negate inverse less power)
  (forall (base numerator denominator)
    (implies
     (and
      (putnam-1975-a3-positive-p carrier less zero base)
      (integerp numerator)
      (posp denominator))
     (equal
      (putnam-1975-a3-natural-power
       (putnam-1975-a3-binary
        power
        base
        (putnam-1975-a3-binary
         multiply
         (putnam-1975-a3-integer
          numerator zero one add negate)
         (putnam-1975-a3-unary
          inverse
          (putnam-1975-a3-natural
           denominator zero one add))))
       denominator one multiply)
      (putnam-1975-a3-integer-power
       base numerator one multiply inverse)))))

(defun putnam-1975-a3-absolute (zero negate less x)
  (if (apply$ less (list x zero))
      (putnam-1975-a3-unary negate x)
    x))

(defun putnam-1975-a3-distance
    (zero add negate less x y)
  (putnam-1975-a3-absolute
   zero negate less
   (putnam-1975-a3-binary
    add x (putnam-1975-a3-unary negate y))))

(defun-sk putnam-1975-a3-power-neighborhood-p
    (carrier zero add negate less power
     base exponent epsilon delta)
  (forall (y)
    (implies
     (and
      (putnam-1975-a3-member-p carrier y)
      (apply$
       less
       (list
        (putnam-1975-a3-distance
         zero add negate less y exponent)
        delta)))
     (apply$
      less
      (list
       (putnam-1975-a3-distance
        zero add negate less
        (putnam-1975-a3-binary power base y)
        (putnam-1975-a3-binary power base exponent))
       epsilon)))))

(defun-sk putnam-1975-a3-power-delta-exists-p
    (carrier zero add negate less power
     base exponent epsilon)
  (exists (delta)
    (and
     (putnam-1975-a3-positive-p carrier less zero delta)
     (putnam-1975-a3-power-neighborhood-p
      carrier zero add negate less power
      base exponent epsilon delta))))

(defun-sk putnam-1975-a3-power-continuous-p
    (carrier zero add negate less power)
  (forall (base exponent epsilon)
    (implies
     (and
      (putnam-1975-a3-positive-p carrier less zero base)
      (putnam-1975-a3-member-p carrier exponent)
      (putnam-1975-a3-positive-p carrier less zero epsilon))
     (putnam-1975-a3-power-delta-exists-p
      carrier zero add negate less power
      base exponent epsilon))))

(defun-sk putnam-1975-a3-zero-base-power-p
    (carrier zero less power)
  (forall (exponent)
    (implies
     (putnam-1975-a3-positive-p carrier less zero exponent)
     (equal
      (putnam-1975-a3-binary power zero exponent)
      zero))))

(defun putnam-1975-a3-real-power-p
    (carrier zero one add multiply negate inverse less power)
  (and
   (tamep-functionp power)
   (putnam-1975-a3-power-typing-p
    carrier zero less power)
   (putnam-1975-a3-power-rational-laws-p
    carrier zero one add multiply negate inverse less power)
   (putnam-1975-a3-power-continuous-p
    carrier zero add negate less power)
   (putnam-1975-a3-zero-base-power-p
    carrier zero less power)))

(defun putnam-1975-a3-add (add x y)
  (putnam-1975-a3-binary add x y))

(defun putnam-1975-a3-negate (negate x)
  (putnam-1975-a3-unary negate x))

(defun putnam-1975-a3-subtract (add negate x y)
  (putnam-1975-a3-add
   add x (putnam-1975-a3-negate negate y)))

(defun putnam-1975-a3-multiply (multiply x y)
  (putnam-1975-a3-binary multiply x y))

(defun putnam-1975-a3-divide (multiply inverse x y)
  (putnam-1975-a3-multiply
   multiply x (putnam-1975-a3-unary inverse y)))

(defun putnam-1975-a3-power (power base exponent)
  (putnam-1975-a3-binary power base exponent))

(defun putnam-1975-a3-less-equal-p (less x y)
  (not (apply$ less (list y x))))

(defun putnam-1975-a3-feasible-p
    (carrier zero one add power less b point)
  (let ((x (nth 0 point))
        (y (nth 1 point))
        (z (nth 2 point)))
    (and
     (putnam-1975-a3-nonnegative-p carrier less zero x)
     (putnam-1975-a3-nonnegative-p carrier less zero y)
     (putnam-1975-a3-nonnegative-p carrier less zero z)
     (equal
      (putnam-1975-a3-add
       add
       (putnam-1975-a3-add
        add
        (putnam-1975-a3-power power x b)
        (putnam-1975-a3-power power y b))
       (putnam-1975-a3-power power z b))
      one))))

(defun putnam-1975-a3-objective
    (add power a b c point)
  (let ((x (nth 0 point))
        (y (nth 1 point))
        (z (nth 2 point)))
    (putnam-1975-a3-add
     add
     (putnam-1975-a3-add
      add
      (putnam-1975-a3-power power x a)
      (putnam-1975-a3-power power y b))
     (putnam-1975-a3-power power z c))))

(defun putnam-1975-a3-maximum-point
    (zero one add multiply negate inverse power a b)
  (let* ((a-over-b
          (putnam-1975-a3-divide multiply inverse a b))
         (b-minus-a
          (putnam-1975-a3-subtract add negate b a))
         (one-over-b-minus-a
          (putnam-1975-a3-divide
           multiply inverse one b-minus-a))
         (x
          (putnam-1975-a3-power
           power a-over-b one-over-b-minus-a))
         (x-to-b
          (putnam-1975-a3-power power x b))
         (one-minus-x-to-b
          (putnam-1975-a3-subtract
           add negate one x-to-b))
         (one-over-b
          (putnam-1975-a3-divide multiply inverse one b))
         (y
          (putnam-1975-a3-power
           power one-minus-x-to-b one-over-b)))
    (list x y zero)))

(defun putnam-1975-a3-minimum-point
    (zero one add multiply negate inverse power b c)
  (let* ((b-over-c
          (putnam-1975-a3-divide multiply inverse b c))
         (c-minus-b
          (putnam-1975-a3-subtract add negate c b))
         (one-over-c-minus-b
          (putnam-1975-a3-divide
           multiply inverse one c-minus-b))
         (z
          (putnam-1975-a3-power
           power b-over-c one-over-c-minus-b))
         (z-to-b
          (putnam-1975-a3-power power z b))
         (one-minus-z-to-b
          (putnam-1975-a3-subtract
           add negate one z-to-b))
         (one-over-b
          (putnam-1975-a3-divide multiply inverse one b))
         (y
          (putnam-1975-a3-power
           power one-minus-z-to-b one-over-b)))
    (list zero y z)))

(defun-sk putnam-1975-a3-global-maximum-p
    (carrier zero one add power less a b c point)
  (forall (x y z)
    (let ((candidate (list x y z)))
      (implies
       (putnam-1975-a3-feasible-p
        carrier zero one add power less b candidate)
       (putnam-1975-a3-less-equal-p
        less
        (putnam-1975-a3-objective
         add power a b c candidate)
        (putnam-1975-a3-objective
         add power a b c point))))))

(defun-sk putnam-1975-a3-global-minimum-p
    (carrier zero one add power less a b c point)
  (forall (x y z)
    (let ((candidate (list x y z)))
      (implies
       (putnam-1975-a3-feasible-p
        carrier zero one add power less b candidate)
       (putnam-1975-a3-less-equal-p
        less
        (putnam-1975-a3-objective
         add power a b c point)
        (putnam-1975-a3-objective
         add power a b c candidate))))))

(defun putnambench-putnam-1975-a3-statement
    (carrier zero one add multiply negate inverse less power a b c)
  (implies
   (and
    (putnam-1975-a3-real-field-p
     carrier zero one add multiply negate inverse less)
    (putnam-1975-a3-real-power-p
     carrier zero one add multiply negate inverse less power)
    (putnam-1975-a3-positive-p carrier less zero a)
    (putnam-1975-a3-member-p carrier b)
    (putnam-1975-a3-member-p carrier c)
    (apply$ less (list a b))
    (apply$ less (list b c)))
   (let ((maximum-point
          (putnam-1975-a3-maximum-point
           zero one add multiply negate inverse power a b))
         (minimum-point
          (putnam-1975-a3-minimum-point
           zero one add multiply negate inverse power b c)))
     (and
      (putnam-1975-a3-feasible-p
       carrier zero one add power less b maximum-point)
      (putnam-1975-a3-global-maximum-p
       carrier zero one add power less a b c maximum-point)
      (putnam-1975-a3-feasible-p
       carrier zero one add power less b minimum-point)
      (putnam-1975-a3-global-minimum-p
       carrier zero one add power less a b c minimum-point)))))

(value-triple :itpeval-statement-checked)
:q
