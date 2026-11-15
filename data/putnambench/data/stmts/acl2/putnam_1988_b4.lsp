;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_b4:
;; a positive real series remains convergent after replacing each term a_n by
;; a_n raised to the exponent n/(n+1). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real numbers are presented as an arbitrary Dedekind-complete ordered
;; field. Sequences, subsets, and operations are tame APPLY$ function objects,
;; so none is replaced by a finite table. For positive x, the value
;; x^(n/(n+1)) is characterized equivalently as the unique positive y such
;; that y^(n+1) = x^n.

(defun p88b4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p88b4-unary (operation x)
  (apply$ operation (list x)))

(defun p88b4-binary (operation x y)
  (apply$ operation (list x y)))

(defun p88b4-positive-p (carrier less zero x)
  (and
   (p88b4-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk p88b4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p88b4-member-p carrier x)
      (p88b4-member-p carrier y)
      (p88b4-member-p carrier z))
     (and
      (p88b4-member-p carrier
                      (p88b4-binary add x y))
      (p88b4-member-p carrier
                      (p88b4-binary multiply x y))
      (p88b4-member-p carrier
                      (p88b4-unary negate x))
      (p88b4-member-p carrier
                      (p88b4-unary inverse x))
      (equal
       (p88b4-binary add (p88b4-binary add x y) z)
       (p88b4-binary add x (p88b4-binary add y z)))
      (equal (p88b4-binary add x y)
             (p88b4-binary add y x))
      (equal (p88b4-binary add x zero) x)
      (equal (p88b4-binary add x (p88b4-unary negate x))
             zero)
      (equal
       (p88b4-binary multiply
                     (p88b4-binary multiply x y)
                     z)
       (p88b4-binary multiply
                     x
                     (p88b4-binary multiply y z)))
      (equal (p88b4-binary multiply x y)
             (p88b4-binary multiply y x))
      (equal (p88b4-binary multiply x one) x)
      (implies
       (equal x zero)
       (equal (p88b4-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p88b4-binary multiply
                      x
                      (p88b4-unary inverse x))
        one))
      (equal
       (p88b4-binary multiply
                     x
                     (p88b4-binary add y z))
       (p88b4-binary
        add
        (p88b4-binary multiply x y)
        (p88b4-binary multiply x z)))))))

(defun-sk p88b4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p88b4-member-p carrier x)
      (p88b4-member-p carrier y)
      (p88b4-member-p carrier z))
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
         (p88b4-binary add x z)
         (p88b4-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list zero
              (p88b4-binary multiply x y))))))))

(defun-sk p88b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p88b4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p88b4-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p88b4-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk p88b4-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p88b4-member-p carrier bound)
     (p88b4-upper-bound-p carrier less set bound))))

(defun-sk p88b4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p88b4-member-p carrier bound)
      (p88b4-upper-bound-p carrier less set bound))
     (not (apply$ less (list bound supremum))))))

(defun p88b4-supremum-p (carrier less set supremum)
  (and
   (p88b4-member-p carrier supremum)
   (p88b4-upper-bound-p carrier less set supremum)
   (p88b4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p88b4-has-supremum-p (carrier less set)
  (exists (supremum)
    (p88b4-supremum-p carrier less set supremum)))

(defun-sk p88b4-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p88b4-set-nonempty-p carrier set)
      (p88b4-bounded-above-p carrier less set))
     (p88b4-has-supremum-p carrier less set))))

(defun p88b4-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p88b4-member-p carrier zero)
   (p88b4-member-p carrier one)
   (not (equal zero one))
   (p88b4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p88b4-order-laws-p
    carrier add multiply zero less)
   (apply$ less (list zero one))
   (p88b4-dedekind-complete-p carrier less)))

(defun p88b4-field-power (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p88b4-binary
     multiply
     base
     (p88b4-field-power
      base (1- exponent) one multiply))))

(defun-sk p88b4-fractional-power-laws-p
    (carrier multiply zero one less fractional-power)
  (forall (x n)
    (implies
     (and
      (p88b4-positive-p carrier less zero x)
      (natp n))
     (let ((y (apply$ fractional-power (list x n))))
       (and
        (p88b4-positive-p carrier less zero y)
        (equal
         (p88b4-field-power
          y (+ n 1) one multiply)
         (p88b4-field-power
          x n one multiply)))))))

(defun p88b4-fractional-power-operation-p
    (carrier multiply zero one less fractional-power)
  (and
   (tamep-functionp fractional-power)
   (p88b4-fractional-power-laws-p
    carrier multiply zero one less fractional-power)))

(defun p88b4-term
    (sequence fractional-power one transformedp n)
  (if transformedp
      (if (zp n)
          one
        (apply$
         fractional-power
         (list (apply$ sequence (list n)) n)))
    (apply$ sequence (list n))))

(defun-sk p88b4-sequence-values-p
    (carrier sequence fractional-power one transformedp)
  (forall (n)
    (implies
     (natp n)
     (p88b4-member-p
      carrier
      (p88b4-term
       sequence fractional-power one transformedp n)))))

(defun-sk p88b4-positive-terms-p
    (carrier less zero sequence fractional-power one transformedp)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= 1 n))
     (p88b4-positive-p
      carrier less zero
      (p88b4-term
       sequence fractional-power one transformedp n)))))

(defun p88b4-partial-sum
    (count sequence fractional-power transformedp
     zero one add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p88b4-binary
     add
     (p88b4-partial-sum
      (1- count)
      sequence fractional-power transformedp
      zero one add)
     (p88b4-term
      sequence fractional-power one transformedp count))))

(defun p88b4-absolute-value (zero negate less x)
  (if (apply$ less (list x zero))
      (p88b4-unary negate x)
    x))

(defun p88b4-distance
    (add negate zero less x y)
  (p88b4-absolute-value
   zero negate less
   (p88b4-binary
    add x (p88b4-unary negate y))))

(defun-sk p88b4-convergence-tail-p
    (sequence fractional-power transformedp
     zero one add negate less limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (apply$
      less
      (list
       (p88b4-distance
        add negate zero less
        (p88b4-partial-sum
         n sequence fractional-power transformedp
         zero one add)
        limit)
       epsilon)))))

(defun-sk p88b4-convergence-cutoff-exists-p
    (sequence fractional-power transformedp
     zero one add negate less limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p88b4-convergence-tail-p
      sequence fractional-power transformedp
      zero one add negate less limit epsilon cutoff))))

(defun-sk p88b4-partial-sums-converge-to-p
    (carrier sequence fractional-power transformedp
     zero one add negate less limit)
  (forall (epsilon)
    (implies
     (p88b4-positive-p carrier less zero epsilon)
     (p88b4-convergence-cutoff-exists-p
      sequence fractional-power transformedp
      zero one add negate less limit epsilon))))

(defun-sk p88b4-series-limit-exists-p
    (carrier sequence fractional-power transformedp
     zero one add negate less)
  (exists (limit)
    (and
     (p88b4-member-p carrier limit)
     (p88b4-partial-sums-converge-to-p
      carrier sequence fractional-power transformedp
      zero one add negate less limit))))

(defun p88b4-positive-convergent-series-p
    (carrier sequence fractional-power transformedp
     zero one add negate less)
  (and
   (tamep-functionp sequence)
   (p88b4-sequence-values-p
    carrier sequence fractional-power one transformedp)
   (p88b4-positive-terms-p
    carrier less zero
    sequence fractional-power one transformedp)
   (p88b4-series-limit-exists-p
    carrier sequence fractional-power transformedp
    zero one add negate less)))

(defun putnambench-putnam-1988-b4-statement
    (real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less sequence fractional-power)
  (implies
   (and
    (p88b4-real-field-p
     real-carrier real-add real-multiply real-negate real-inverse
     real-zero real-one real-less)
    (p88b4-fractional-power-operation-p
     real-carrier real-multiply real-zero real-one real-less
     fractional-power)
    (p88b4-positive-convergent-series-p
     real-carrier sequence fractional-power nil
     real-zero real-one real-add real-negate real-less))
   (p88b4-positive-convergent-series-p
    real-carrier sequence fractional-power t
    real-zero real-one real-add real-negate real-less)))

(value-triple :itpeval-statement-checked)
:q
