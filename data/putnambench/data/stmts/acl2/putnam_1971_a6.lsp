;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_a6:
;; a real exponent whose power of every positive integer is an integer must
;; be a nonnegative integer. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. Positive-base
;; real powers are uniquely fixed by their values at rational exponents and
;; continuity in the exponent. Thus the structure arguments below are an
;; explicit presentation of the source real field and its power operation,
;; without restricting the exponent or integer quantifiers to finite data.

(defun putnam-1971-a6-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1971-a6-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1971-a6-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1971-a6-positive-p (carrier less zero x)
  (and
   (putnam-1971-a6-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk putnam-1971-a6-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1971-a6-member-p carrier x)
      (putnam-1971-a6-member-p carrier y)
      (putnam-1971-a6-member-p carrier z))
     (and
      (putnam-1971-a6-member-p
       carrier (putnam-1971-a6-binary add x y))
      (putnam-1971-a6-member-p
       carrier (putnam-1971-a6-binary multiply x y))
      (putnam-1971-a6-member-p
       carrier (putnam-1971-a6-unary negate x))
      (putnam-1971-a6-member-p
       carrier (putnam-1971-a6-unary inverse x))
      (equal
       (putnam-1971-a6-binary
        add (putnam-1971-a6-binary add x y) z)
       (putnam-1971-a6-binary
        add x (putnam-1971-a6-binary add y z)))
      (equal
       (putnam-1971-a6-binary add x y)
       (putnam-1971-a6-binary add y x))
      (equal (putnam-1971-a6-binary add x zero) x)
      (equal
       (putnam-1971-a6-binary
        add x (putnam-1971-a6-unary negate x))
       zero)
      (equal
       (putnam-1971-a6-binary
        multiply (putnam-1971-a6-binary multiply x y) z)
       (putnam-1971-a6-binary
        multiply x (putnam-1971-a6-binary multiply y z)))
      (equal
       (putnam-1971-a6-binary multiply x y)
       (putnam-1971-a6-binary multiply y x))
      (equal (putnam-1971-a6-binary multiply x one) x)
      (equal (putnam-1971-a6-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1971-a6-binary
         multiply x (putnam-1971-a6-unary inverse x))
        one))
      (equal
       (putnam-1971-a6-binary
        multiply x (putnam-1971-a6-binary add y z))
       (putnam-1971-a6-binary
        add
        (putnam-1971-a6-binary multiply x y)
        (putnam-1971-a6-binary multiply x z)))))))

(defun-sk putnam-1971-a6-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1971-a6-member-p carrier x)
      (putnam-1971-a6-member-p carrier y)
      (putnam-1971-a6-member-p carrier z))
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
         (putnam-1971-a6-binary add x z)
         (putnam-1971-a6-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list zero
              (putnam-1971-a6-binary multiply x y))))))))

(defun-sk putnam-1971-a6-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1971-a6-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1971-a6-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1971-a6-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1971-a6-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1971-a6-member-p carrier bound)
     (putnam-1971-a6-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1971-a6-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1971-a6-member-p carrier supremum)
     (putnam-1971-a6-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1971-a6-member-p carrier bound)
       (putnam-1971-a6-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1971-a6-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1971-a6-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1971-a6-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1971-a6-set-nonempty-p carrier set)
      (putnam-1971-a6-bounded-above-p carrier less set))
     (putnam-1971-a6-has-supremum-p
      carrier less set))))

(defun putnam-1971-a6-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1971-a6-member-p carrier zero)
   (putnam-1971-a6-member-p carrier one)
   (not (equal zero one))
   (putnam-1971-a6-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1971-a6-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (putnam-1971-a6-dedekind-complete-p carrier less)))

(defun putnam-1971-a6-natural
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1971-a6-binary
     add one
     (putnam-1971-a6-natural (- n 1) zero one add))))

(defun putnam-1971-a6-integer
    (n zero one add negate)
  (if (< n 0)
      (putnam-1971-a6-unary
       negate
       (putnam-1971-a6-natural (- n) zero one add))
    (putnam-1971-a6-natural n zero one add)))

(defun putnam-1971-a6-natural-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1971-a6-binary
     multiply
     (putnam-1971-a6-natural-power
      base (- exponent 1) one multiply)
     base)))

(defun putnam-1971-a6-integer-power
    (base exponent one multiply inverse)
  (if (< exponent 0)
      (putnam-1971-a6-unary
       inverse
       (putnam-1971-a6-natural-power
        base (- exponent) one multiply))
    (putnam-1971-a6-natural-power
     base exponent one multiply)))

(defun-sk putnam-1971-a6-power-typing-p
    (carrier zero less power)
  (forall (base exponent)
    (implies
     (and
      (putnam-1971-a6-positive-p carrier less zero base)
      (putnam-1971-a6-member-p carrier exponent))
     (putnam-1971-a6-positive-p
      carrier less zero
      (putnam-1971-a6-binary power base exponent)))))

(defun-sk putnam-1971-a6-power-rational-laws-p
    (carrier zero one add multiply negate inverse less power)
  (forall (base numerator denominator)
    (implies
     (and
      (putnam-1971-a6-positive-p carrier less zero base)
      (integerp numerator)
      (posp denominator))
     (equal
      (putnam-1971-a6-natural-power
       (putnam-1971-a6-binary
        power
        base
        (putnam-1971-a6-binary
         multiply
         (putnam-1971-a6-integer
          numerator zero one add negate)
         (putnam-1971-a6-unary
          inverse
          (putnam-1971-a6-natural
           denominator zero one add))))
       denominator one multiply)
      (putnam-1971-a6-integer-power
       base numerator one multiply inverse)))))

(defun putnam-1971-a6-absolute (zero negate less x)
  (if (apply$ less (list x zero))
      (putnam-1971-a6-unary negate x)
    x))

(defun putnam-1971-a6-distance
    (zero add negate less x y)
  (putnam-1971-a6-absolute
   zero negate less
   (putnam-1971-a6-binary
    add x (putnam-1971-a6-unary negate y))))

(defun-sk putnam-1971-a6-power-neighborhood-p
    (carrier zero add negate less power
     base exponent epsilon delta)
  (forall (y)
    (implies
     (and
      (putnam-1971-a6-member-p carrier y)
      (apply$
       less
       (list
        (putnam-1971-a6-distance
         zero add negate less y exponent)
        delta)))
     (apply$
      less
      (list
       (putnam-1971-a6-distance
        zero add negate less
        (putnam-1971-a6-binary power base y)
        (putnam-1971-a6-binary power base exponent))
       epsilon)))))

(defun-sk putnam-1971-a6-power-delta-exists-p
    (carrier zero add negate less power
     base exponent epsilon)
  (exists (delta)
    (and
     (putnam-1971-a6-positive-p carrier less zero delta)
     (putnam-1971-a6-power-neighborhood-p
      carrier zero add negate less power
      base exponent epsilon delta))))

(defun-sk putnam-1971-a6-power-continuous-p
    (carrier zero add negate less power)
  (forall (base exponent epsilon)
    (implies
     (and
      (putnam-1971-a6-positive-p carrier less zero base)
      (putnam-1971-a6-member-p carrier exponent)
      (putnam-1971-a6-positive-p carrier less zero epsilon))
     (putnam-1971-a6-power-delta-exists-p
      carrier zero add negate less power
      base exponent epsilon))))

(defun putnam-1971-a6-real-power-p
    (carrier zero one add multiply negate inverse less power)
  (and
   (tamep-functionp power)
   (putnam-1971-a6-power-typing-p
    carrier zero less power)
   (putnam-1971-a6-power-rational-laws-p
    carrier zero one add multiply negate inverse less power)
   (putnam-1971-a6-power-continuous-p
    carrier zero add negate less power)))

(defun-sk putnam-1971-a6-power-is-integer-p
    (zero one add negate power n c)
  (exists (m)
    (and
     (integerp m)
     (equal
      (putnam-1971-a6-binary
       power
       (putnam-1971-a6-integer n zero one add negate)
       c)
      (putnam-1971-a6-integer
       m zero one add negate)))))

(defun-sk putnam-1971-a6-all-positive-powers-integer-p
    (zero one add negate power c)
  (forall (n)
    (implies
     (and (integerp n)
          (< 0 n))
     (putnam-1971-a6-power-is-integer-p
      zero one add negate power n c))))

(defun-sk putnam-1971-a6-nonnegative-integer-p
    (zero one add negate c)
  (exists (m)
    (and
     (integerp m)
     (<= 0 m)
     (equal
      c
      (putnam-1971-a6-integer
       m zero one add negate)))))

(defun putnambench-putnam-1971-a6-statement
    (carrier zero one add multiply negate inverse less power c)
  (implies
   (and
    (putnam-1971-a6-real-field-p
     carrier zero one add multiply negate inverse less)
    (putnam-1971-a6-real-power-p
     carrier zero one add multiply negate inverse less power)
    (putnam-1971-a6-member-p carrier c)
    (putnam-1971-a6-all-positive-powers-integer-p
     zero one add negate power c))
   (putnam-1971-a6-nonnegative-integer-p
    zero one add negate c)))

(value-triple :itpeval-statement-checked)
:q
