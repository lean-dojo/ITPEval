;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_a3:
;; classification of the real exponents for which the series with terms
;; (((1/n) / sin(1/n)) - 1)^x converges. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers.  SINE is fixed
;; by convergence of its Taylor series, and positive-base real powers are fixed
;; by their rational values and continuity in the exponent.  The resulting
;; definitions represent the exact source functions rather than rational
;; approximations to them.

(defun putnam-1988-a3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1988-a3-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1988-a3-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1988-a3-positive-p (carrier less zero x)
  (and
   (putnam-1988-a3-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk putnam-1988-a3-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1988-a3-member-p carrier x)
      (putnam-1988-a3-member-p carrier y)
      (putnam-1988-a3-member-p carrier z))
     (and
      (putnam-1988-a3-member-p
       carrier (putnam-1988-a3-binary add x y))
      (putnam-1988-a3-member-p
       carrier (putnam-1988-a3-binary multiply x y))
      (putnam-1988-a3-member-p
       carrier (putnam-1988-a3-unary negate x))
      (putnam-1988-a3-member-p
       carrier (putnam-1988-a3-unary inverse x))
      (equal
       (putnam-1988-a3-binary
        add (putnam-1988-a3-binary add x y) z)
       (putnam-1988-a3-binary
        add x (putnam-1988-a3-binary add y z)))
      (equal
       (putnam-1988-a3-binary add x y)
       (putnam-1988-a3-binary add y x))
      (equal (putnam-1988-a3-binary add x zero) x)
      (equal
       (putnam-1988-a3-binary
        add x (putnam-1988-a3-unary negate x))
       zero)
      (equal
       (putnam-1988-a3-binary
        multiply (putnam-1988-a3-binary multiply x y) z)
       (putnam-1988-a3-binary
        multiply x (putnam-1988-a3-binary multiply y z)))
      (equal
       (putnam-1988-a3-binary multiply x y)
       (putnam-1988-a3-binary multiply y x))
      (equal (putnam-1988-a3-binary multiply x one) x)
      (equal (putnam-1988-a3-unary inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1988-a3-binary
         multiply x (putnam-1988-a3-unary inverse x))
        one))
      (equal
       (putnam-1988-a3-binary
        multiply x (putnam-1988-a3-binary add y z))
       (putnam-1988-a3-binary
        add
        (putnam-1988-a3-binary multiply x y)
        (putnam-1988-a3-binary multiply x z)))))))

(defun-sk putnam-1988-a3-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1988-a3-member-p carrier x)
      (putnam-1988-a3-member-p carrier y)
      (putnam-1988-a3-member-p carrier z))
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
         (putnam-1988-a3-binary add x z)
         (putnam-1988-a3-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list
         zero
         (putnam-1988-a3-binary multiply x y))))))))

(defun-sk putnam-1988-a3-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1988-a3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1988-a3-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1988-a3-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1988-a3-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1988-a3-member-p carrier bound)
     (putnam-1988-a3-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1988-a3-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1988-a3-member-p carrier supremum)
     (putnam-1988-a3-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1988-a3-member-p carrier bound)
       (putnam-1988-a3-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1988-a3-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1988-a3-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1988-a3-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1988-a3-set-nonempty-p carrier set)
      (putnam-1988-a3-bounded-above-p carrier less set))
     (putnam-1988-a3-has-supremum-p
      carrier less set))))

(defun putnam-1988-a3-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1988-a3-member-p carrier zero)
   (putnam-1988-a3-member-p carrier one)
   (not (equal zero one))
   (putnam-1988-a3-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1988-a3-order-laws-p
    carrier zero add multiply less)
   (apply$ less (list zero one))
   (putnam-1988-a3-dedekind-complete-p carrier less)))

(defun putnam-1988-a3-natural (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1988-a3-binary
     add one
     (putnam-1988-a3-natural (- n 1) zero one add))))

(defun putnam-1988-a3-integer
    (n zero one add negate)
  (if (< n 0)
      (putnam-1988-a3-unary
       negate
       (putnam-1988-a3-natural (- n) zero one add))
    (putnam-1988-a3-natural n zero one add)))

(defun putnam-1988-a3-natural-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1988-a3-binary
     multiply
     (putnam-1988-a3-natural-power
      base (- exponent 1) one multiply)
     base)))

(defun putnam-1988-a3-integer-power
    (base exponent one multiply inverse)
  (if (< exponent 0)
      (putnam-1988-a3-unary
       inverse
       (putnam-1988-a3-natural-power
        base (- exponent) one multiply))
    (putnam-1988-a3-natural-power
     base exponent one multiply)))

(defun putnam-1988-a3-rational
    (numerator denominator zero one add multiply negate inverse)
  (putnam-1988-a3-binary
   multiply
   (putnam-1988-a3-integer
    numerator zero one add negate)
   (putnam-1988-a3-unary
    inverse
    (putnam-1988-a3-natural denominator zero one add))))

(defun putnam-1988-a3-absolute (zero negate less x)
  (if (apply$ less (list x zero))
      (putnam-1988-a3-unary negate x)
    x))

(defun putnam-1988-a3-distance
    (zero add negate less x y)
  (putnam-1988-a3-absolute
   zero negate less
   (putnam-1988-a3-binary
    add x (putnam-1988-a3-unary negate y))))

(defun-sk putnam-1988-a3-power-typing-p
    (carrier zero less power)
  (forall (base exponent)
    (implies
     (and
      (putnam-1988-a3-positive-p carrier less zero base)
      (putnam-1988-a3-member-p carrier exponent))
     (putnam-1988-a3-positive-p
      carrier less zero
      (putnam-1988-a3-binary power base exponent)))))

(defun-sk putnam-1988-a3-power-rational-laws-p
    (carrier zero one add multiply negate inverse less power)
  (forall (base numerator denominator)
    (implies
     (and
      (putnam-1988-a3-positive-p carrier less zero base)
      (integerp numerator)
      (posp denominator))
     (equal
      (putnam-1988-a3-natural-power
       (putnam-1988-a3-binary
        power
        base
        (putnam-1988-a3-rational
         numerator denominator
         zero one add multiply negate inverse))
       denominator one multiply)
      (putnam-1988-a3-integer-power
       base numerator one multiply inverse)))))

(defun-sk putnam-1988-a3-power-neighborhood-p
    (carrier zero add negate less power
     base exponent epsilon delta)
  (forall (y)
    (implies
     (and
      (putnam-1988-a3-member-p carrier y)
      (apply$
       less
       (list
        (putnam-1988-a3-distance
         zero add negate less y exponent)
        delta)))
     (apply$
      less
      (list
       (putnam-1988-a3-distance
        zero add negate less
        (putnam-1988-a3-binary power base y)
        (putnam-1988-a3-binary power base exponent))
       epsilon)))))

(defun-sk putnam-1988-a3-power-delta-exists-p
    (carrier zero add negate less power
     base exponent epsilon)
  (exists (delta)
    (and
     (putnam-1988-a3-positive-p carrier less zero delta)
     (putnam-1988-a3-power-neighborhood-p
      carrier zero add negate less power
      base exponent epsilon delta))))

(defun-sk putnam-1988-a3-power-continuous-p
    (carrier zero add negate less power)
  (forall (base exponent epsilon)
    (implies
     (and
      (putnam-1988-a3-positive-p carrier less zero base)
      (putnam-1988-a3-member-p carrier exponent)
      (putnam-1988-a3-positive-p carrier less zero epsilon))
     (putnam-1988-a3-power-delta-exists-p
      carrier zero add negate less power
      base exponent epsilon))))

(defun putnam-1988-a3-real-power-p
    (carrier zero one add multiply negate inverse less power)
  (and
   (tamep-functionp power)
   (putnam-1988-a3-power-typing-p
    carrier zero less power)
   (putnam-1988-a3-power-rational-laws-p
    carrier zero one add multiply negate inverse less power)
   (putnam-1988-a3-power-continuous-p
    carrier zero add negate less power)))

(defun putnam-1988-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1988-a3-factorial (- n 1)))))

(defun putnam-1988-a3-sine-prefix
    (x terms zero one add multiply negate inverse)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let* ((index (- terms 1))
           (exponent (+ (* 2 index) 1))
           (sign
            (if (equal (mod index 2) 0)
                one
              (putnam-1988-a3-unary negate one)))
           (power
            (putnam-1988-a3-natural-power
             x exponent one multiply))
           (factorial
            (putnam-1988-a3-natural
             (putnam-1988-a3-factorial exponent)
             zero one add))
           (term
            (putnam-1988-a3-binary
             multiply
             sign
             (putnam-1988-a3-binary
              multiply
              power
              (putnam-1988-a3-unary inverse factorial)))))
      (putnam-1988-a3-binary
       add
       (putnam-1988-a3-sine-prefix
        x index zero one add multiply negate inverse)
       term))))

(defun-sk putnam-1988-a3-sine-typing-p
    (carrier sine)
  (forall (x)
    (implies
     (putnam-1988-a3-member-p carrier x)
     (putnam-1988-a3-member-p
      carrier (putnam-1988-a3-unary sine x)))))

(defun-sk putnam-1988-a3-sine-tail-p
    (carrier zero one add multiply negate inverse less sine
     x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (apply$
      less
      (list
       (putnam-1988-a3-distance
        zero add negate less
        (putnam-1988-a3-sine-prefix
         x terms zero one add multiply negate inverse)
        (putnam-1988-a3-unary sine x))
       epsilon)))))

(defun-sk putnam-1988-a3-sine-cutoff-exists-p
    (carrier zero one add multiply negate inverse less sine
     x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1988-a3-sine-tail-p
      carrier zero one add multiply negate inverse less sine
      x epsilon cutoff))))

(defun-sk putnam-1988-a3-sine-series-p
    (carrier zero one add multiply negate inverse less sine)
  (forall (x epsilon)
    (implies
     (and
      (putnam-1988-a3-member-p carrier x)
      (putnam-1988-a3-positive-p carrier less zero epsilon))
     (putnam-1988-a3-sine-cutoff-exists-p
      carrier zero one add multiply negate inverse less sine
      x epsilon))))

(defun putnam-1988-a3-real-sine-p
    (carrier zero one add multiply negate inverse less sine)
  (and
   (tamep-functionp sine)
   (putnam-1988-a3-sine-typing-p carrier sine)
   (putnam-1988-a3-sine-series-p
    carrier zero one add multiply negate inverse less sine)))

(defun putnam-1988-a3-source-base
    (n zero one add multiply negate inverse sine)
  (let* ((n-value
          (putnam-1988-a3-natural n zero one add))
         (reciprocal
          (putnam-1988-a3-unary inverse n-value))
         (sine-value
          (putnam-1988-a3-unary sine reciprocal)))
    (putnam-1988-a3-binary
     add
     (putnam-1988-a3-binary
      multiply
      reciprocal
      (putnam-1988-a3-unary inverse sine-value))
     (putnam-1988-a3-unary negate one))))

(defun putnam-1988-a3-source-term
    (n exponent zero one add multiply negate inverse sine power)
  (putnam-1988-a3-binary
   power
   (putnam-1988-a3-source-base
    n zero one add multiply negate inverse sine)
   exponent))

(defun putnam-1988-a3-partial-sum
    (t-index exponent zero one add multiply negate inverse sine power)
  (declare (xargs :measure (nfix t-index)))
  (if (zp t-index)
      zero
    (putnam-1988-a3-binary
     add
     (putnam-1988-a3-partial-sum
      (- t-index 1) exponent
      zero one add multiply negate inverse sine power)
     (putnam-1988-a3-source-term
      t-index exponent
      zero one add multiply negate inverse sine power))))

(defun-sk putnam-1988-a3-convergence-tail-p
    (zero one add multiply negate inverse less sine power
     exponent limit epsilon cutoff)
  (forall (t-index)
    (implies
     (and
      (natp t-index)
      (<= cutoff t-index))
     (apply$
      less
      (list
       (putnam-1988-a3-distance
        zero add negate less
        (putnam-1988-a3-partial-sum
         t-index exponent
         zero one add multiply negate inverse sine power)
        limit)
       epsilon)))))

(defun-sk putnam-1988-a3-convergence-cutoff-exists-p
    (zero one add multiply negate inverse less sine power
     exponent limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1988-a3-convergence-tail-p
      zero one add multiply negate inverse less sine power
      exponent limit epsilon cutoff))))

(defun-sk putnam-1988-a3-limit-p
    (carrier zero one add multiply negate inverse less sine power
     exponent limit)
  (forall (epsilon)
    (implies
     (putnam-1988-a3-positive-p carrier less zero epsilon)
     (putnam-1988-a3-convergence-cutoff-exists-p
      zero one add multiply negate inverse less sine power
      exponent limit epsilon))))

(defun-sk putnam-1988-a3-convergent-p
    (carrier zero one add multiply negate inverse less sine power
     exponent)
  (exists (limit)
    (and
     (putnam-1988-a3-member-p carrier limit)
     (putnam-1988-a3-limit-p
      carrier zero one add multiply negate inverse less sine power
      exponent limit))))

;; Pointwise equivalence for every represented real exponent is exactly the
;; extensional form of the source equality of sets of real exponents.
(defun putnambench-putnam-1988-a3-statement
    (carrier zero one add multiply negate inverse less sine power exponent)
  (implies
   (and
    (putnam-1988-a3-real-field-p
     carrier zero one add multiply negate inverse less)
    (putnam-1988-a3-real-sine-p
     carrier zero one add multiply negate inverse less sine)
    (putnam-1988-a3-real-power-p
     carrier zero one add multiply negate inverse less power)
    (putnam-1988-a3-member-p carrier exponent))
   (iff
    (putnam-1988-a3-convergent-p
     carrier zero one add multiply negate inverse less sine power
     exponent)
    (apply$
     less
     (list
      (putnam-1988-a3-rational
       1 2 zero one add multiply negate inverse)
      exponent)))))

(value-triple :itpeval-statement-checked)
:q
