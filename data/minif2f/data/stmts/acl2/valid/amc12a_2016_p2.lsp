;; Statement-only formalization of miniF2F corpus artifact amc12a_2016_p2:
;; a real number x satisfying 10^x * 100^(2*x) = 1000^5 must equal 3,
;; where exponentiation is real exponentiation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. On positive
;; bases, POWER is characterized by its rational values and continuity in the
;; exponent. Thus x ranges over the full real carrier, with no integrality or
;; rationality restriction.

(defun amc2016p2-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun amc2016p2-unary (operation x)
  (apply$ operation (list x)))

(defun amc2016p2-binary (operation x y)
  (apply$ operation (list x y)))

(defun amc2016p2-positive-p (carrier less zero x)
  (and
   (amc2016p2-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk amc2016p2-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (amc2016p2-member-p carrier x)
      (amc2016p2-member-p carrier y)
      (amc2016p2-member-p carrier z))
     (and
      (amc2016p2-member-p carrier (amc2016p2-binary add x y))
      (amc2016p2-member-p carrier (amc2016p2-binary multiply x y))
      (amc2016p2-member-p carrier (amc2016p2-unary negate x))
      (amc2016p2-member-p carrier (amc2016p2-unary inverse x))
      (equal
       (amc2016p2-binary add (amc2016p2-binary add x y) z)
       (amc2016p2-binary add x (amc2016p2-binary add y z)))
      (equal (amc2016p2-binary add x y)
             (amc2016p2-binary add y x))
      (equal (amc2016p2-binary add x zero) x)
      (equal (amc2016p2-binary add x (amc2016p2-unary negate x))
             zero)
      (equal
       (amc2016p2-binary multiply
                         (amc2016p2-binary multiply x y)
                         z)
       (amc2016p2-binary multiply
                         x
                         (amc2016p2-binary multiply y z)))
      (equal (amc2016p2-binary multiply x y)
             (amc2016p2-binary multiply y x))
      (equal (amc2016p2-binary multiply x one) x)
      (equal (amc2016p2-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (amc2016p2-binary multiply x (amc2016p2-unary inverse x))
        one))
      (equal
       (amc2016p2-binary
        multiply x (amc2016p2-binary add y z))
       (amc2016p2-binary
        add
        (amc2016p2-binary multiply x y)
        (amc2016p2-binary multiply x z)))))))

(defun-sk amc2016p2-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (amc2016p2-member-p carrier x)
      (amc2016p2-member-p carrier y)
      (amc2016p2-member-p carrier z))
     (and
      (not (apply$ less (list x x)))
      (or (equal x y)
          (apply$ less (list x y))
          (apply$ less (list y x)))
      (implies
       (and (apply$ less (list x y))
            (apply$ less (list y z)))
       (apply$ less (list x z)))
      (implies
       (apply$ less (list x y))
       (apply$
        less
        (list (amc2016p2-binary add x z)
              (amc2016p2-binary add y z))))
      (implies
       (and (apply$ less (list zero x))
            (apply$ less (list zero y)))
       (apply$
        less
        (list zero (amc2016p2-binary multiply x y))))))))

(defun-sk amc2016p2-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (amc2016p2-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk amc2016p2-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (amc2016p2-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk amc2016p2-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (amc2016p2-member-p carrier bound)
     (amc2016p2-upper-bound-p carrier less set bound))))

(defun-sk amc2016p2-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (amc2016p2-member-p carrier supremum)
     (amc2016p2-upper-bound-p carrier less set supremum)
     (implies
      (and
       (amc2016p2-member-p carrier bound)
       (amc2016p2-upper-bound-p carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk amc2016p2-has-supremum-p (carrier less set)
  (exists (supremum)
    (amc2016p2-supremum-p carrier less set supremum)))

(defun-sk amc2016p2-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (amc2016p2-set-nonempty-p carrier set)
      (amc2016p2-bounded-above-p carrier less set))
     (amc2016p2-has-supremum-p carrier less set))))

(defun amc2016p2-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (amc2016p2-member-p carrier zero)
   (amc2016p2-member-p carrier one)
   (not (equal zero one))
   (amc2016p2-field-laws-p
    carrier zero one add multiply negate inverse)
   (amc2016p2-order-laws-p carrier zero add multiply less)
   (apply$ less (list zero one))
   (amc2016p2-dedekind-complete-p carrier less)))

(defun amc2016p2-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (amc2016p2-binary
     add one
     (amc2016p2-natural (- n 1) zero one add))))

(defun amc2016p2-integer (n zero one add negate)
  (if (< n 0)
      (amc2016p2-unary
       negate
       (amc2016p2-natural (- n) zero one add))
    (amc2016p2-natural n zero one add)))

(defun amc2016p2-natural-power (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (amc2016p2-binary
     multiply
     (amc2016p2-natural-power
      base (- exponent 1) one multiply)
     base)))

(defun amc2016p2-integer-power
    (base exponent one multiply inverse)
  (if (< exponent 0)
      (amc2016p2-unary
       inverse
       (amc2016p2-natural-power
        base (- exponent) one multiply))
    (amc2016p2-natural-power base exponent one multiply)))

(defun-sk amc2016p2-power-typing-p (carrier zero less power)
  (forall (base exponent)
    (implies
     (and
      (amc2016p2-positive-p carrier less zero base)
      (amc2016p2-member-p carrier exponent))
     (amc2016p2-positive-p
      carrier less zero
      (amc2016p2-binary power base exponent)))))

(defun-sk amc2016p2-power-rational-laws-p
    (carrier zero one add multiply negate inverse less power)
  (forall (base numerator denominator)
    (implies
     (and
      (amc2016p2-positive-p carrier less zero base)
      (integerp numerator)
      (posp denominator))
     (equal
      (amc2016p2-natural-power
       (amc2016p2-binary
        power
        base
        (amc2016p2-binary
         multiply
         (amc2016p2-integer numerator zero one add negate)
         (amc2016p2-unary
          inverse
          (amc2016p2-natural denominator zero one add))))
       denominator one multiply)
      (amc2016p2-integer-power
       base numerator one multiply inverse)))))

(defun amc2016p2-absolute (zero negate less x)
  (if (apply$ less (list x zero))
      (amc2016p2-unary negate x)
    x))

(defun amc2016p2-distance (zero add negate less x y)
  (amc2016p2-absolute
   zero negate less
   (amc2016p2-binary add x (amc2016p2-unary negate y))))

(defun-sk amc2016p2-power-neighborhood-p
    (carrier zero add negate less power
     base exponent epsilon delta)
  (forall (y)
    (implies
     (and
      (amc2016p2-member-p carrier y)
      (apply$
       less
       (list
        (amc2016p2-distance zero add negate less y exponent)
        delta)))
     (apply$
      less
      (list
       (amc2016p2-distance
        zero add negate less
        (amc2016p2-binary power base y)
        (amc2016p2-binary power base exponent))
       epsilon)))))

(defun-sk amc2016p2-power-delta-exists-p
    (carrier zero add negate less power
     base exponent epsilon)
  (exists (delta)
    (and
     (amc2016p2-positive-p carrier less zero delta)
     (amc2016p2-power-neighborhood-p
      carrier zero add negate less power
      base exponent epsilon delta))))

(defun-sk amc2016p2-power-continuous-p
    (carrier zero add negate less power)
  (forall (base exponent epsilon)
    (implies
     (and
      (amc2016p2-positive-p carrier less zero base)
      (amc2016p2-member-p carrier exponent)
      (amc2016p2-positive-p carrier less zero epsilon))
     (amc2016p2-power-delta-exists-p
      carrier zero add negate less power
      base exponent epsilon))))

(defun amc2016p2-real-power-p
    (carrier zero one add multiply negate inverse less power)
  (and
   (tamep-functionp power)
   (amc2016p2-power-typing-p carrier zero less power)
   (amc2016p2-power-rational-laws-p
    carrier zero one add multiply negate inverse less power)
   (amc2016p2-power-continuous-p
    carrier zero add negate less power)))

(defun minif2f-amc12a-2016-p2-statement
    (carrier zero one add multiply negate inverse less power x)
  (let ((two (amc2016p2-natural 2 zero one add))
        (three (amc2016p2-natural 3 zero one add))
        (five (amc2016p2-natural 5 zero one add))
        (ten (amc2016p2-natural 10 zero one add))
        (one-hundred (amc2016p2-natural 100 zero one add))
        (one-thousand (amc2016p2-natural 1000 zero one add)))
    (implies
     (and
      (amc2016p2-real-field-p
       carrier zero one add multiply negate inverse less)
      (amc2016p2-real-power-p
       carrier zero one add multiply negate inverse less power)
      (amc2016p2-member-p carrier x)
      (equal
       (amc2016p2-binary
        multiply
        (amc2016p2-binary power ten x)
        (amc2016p2-binary
         power
         one-hundred
         (amc2016p2-binary multiply two x)))
       (amc2016p2-binary power one-thousand five)))
     (equal x three))))

(value-triple :itpeval-statement-checked)
:q
