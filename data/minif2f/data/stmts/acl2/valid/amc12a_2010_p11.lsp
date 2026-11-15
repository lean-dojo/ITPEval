;; Statement-only formalization of miniF2F corpus artifact amc12a_2010_p11:
;; a positive real base satisfying the given real-exponentiation and
;; base-logarithm equations equals 8/7. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar parameters below present a Dedekind-complete ordered field,
;; hence a copy of the real field. Exponential is defined by convergence of
;; its exact power series, logarithm by the inverse exponential relation, and
;; positive-base real powers by exp(exponent * log(base)). Thus x and b range
;; over arbitrary reals rather than a rational or finite surrogate.

(defun amc12a-2010-p11-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun amc12a-2010-p11-unary (operation value)
  (apply$ operation (list value)))

(defun amc12a-2010-p11-binary (operation left right)
  (apply$ operation (list left right)))

(defun-sk amc12a-2010-p11-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (amc12a-2010-p11-member-p carrier x)
      (amc12a-2010-p11-member-p carrier y)
      (amc12a-2010-p11-member-p carrier z))
     (and
      (amc12a-2010-p11-member-p
       carrier
       (amc12a-2010-p11-binary add x y))
      (amc12a-2010-p11-member-p
       carrier
       (amc12a-2010-p11-binary multiply x y))
      (amc12a-2010-p11-member-p
       carrier
       (amc12a-2010-p11-unary negate x))
      (amc12a-2010-p11-member-p
       carrier
       (amc12a-2010-p11-unary inverse x))
      (equal
       (amc12a-2010-p11-binary
        add
        (amc12a-2010-p11-binary add x y)
        z)
       (amc12a-2010-p11-binary
        add
        x
        (amc12a-2010-p11-binary add y z)))
      (equal
       (amc12a-2010-p11-binary add x y)
       (amc12a-2010-p11-binary add y x))
      (equal
       (amc12a-2010-p11-binary add x zero)
       x)
      (equal
       (amc12a-2010-p11-binary
        add x (amc12a-2010-p11-unary negate x))
       zero)
      (equal
       (amc12a-2010-p11-binary
        multiply
        (amc12a-2010-p11-binary multiply x y)
        z)
       (amc12a-2010-p11-binary
        multiply
        x
        (amc12a-2010-p11-binary multiply y z)))
      (equal
       (amc12a-2010-p11-binary multiply x y)
       (amc12a-2010-p11-binary multiply y x))
      (equal
       (amc12a-2010-p11-binary multiply x one)
       x)
      (implies
       (not (equal x zero))
       (equal
        (amc12a-2010-p11-binary
         multiply x (amc12a-2010-p11-unary inverse x))
        one))
      (implies
       (equal x zero)
       (equal
        (amc12a-2010-p11-unary inverse x)
        zero))
      (equal
       (amc12a-2010-p11-binary
        multiply
        x
        (amc12a-2010-p11-binary add y z))
       (amc12a-2010-p11-binary
        add
        (amc12a-2010-p11-binary multiply x y)
        (amc12a-2010-p11-binary multiply x z)))))))

(defun-sk amc12a-2010-p11-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (amc12a-2010-p11-member-p carrier x)
      (amc12a-2010-p11-member-p carrier y)
      (amc12a-2010-p11-member-p carrier z))
     (and
      (not (amc12a-2010-p11-binary less x x))
      (or
       (equal x y)
       (amc12a-2010-p11-binary less x y)
       (amc12a-2010-p11-binary less y x))
      (implies
       (and
        (amc12a-2010-p11-binary less x y)
        (amc12a-2010-p11-binary less y z))
       (amc12a-2010-p11-binary less x z))
      (implies
       (amc12a-2010-p11-binary less x y)
       (amc12a-2010-p11-binary
        less
        (amc12a-2010-p11-binary add x z)
        (amc12a-2010-p11-binary add y z)))
      (implies
       (and
        (amc12a-2010-p11-binary less zero x)
        (amc12a-2010-p11-binary less zero y))
       (amc12a-2010-p11-binary
        less
        zero
        (amc12a-2010-p11-binary multiply x y)))))))

(defun-sk amc12a-2010-p11-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (amc12a-2010-p11-member-p carrier x))))

(defun-sk amc12a-2010-p11-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (amc12a-2010-p11-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk amc12a-2010-p11-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (amc12a-2010-p11-member-p carrier x)
      (apply$ set (list x)))
     (not (amc12a-2010-p11-binary less bound x)))))

(defun-sk amc12a-2010-p11-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (amc12a-2010-p11-member-p carrier bound)
     (amc12a-2010-p11-upper-bound-p
      carrier less set bound))))

(defun-sk amc12a-2010-p11-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (amc12a-2010-p11-member-p carrier bound)
      (amc12a-2010-p11-upper-bound-p
       carrier less set bound))
     (not
      (amc12a-2010-p11-binary
       less bound supremum)))))

(defun amc12a-2010-p11-supremum-p
    (carrier less set supremum)
  (and
   (amc12a-2010-p11-member-p carrier supremum)
   (amc12a-2010-p11-upper-bound-p
    carrier less set supremum)
   (amc12a-2010-p11-least-upper-bound-p
    carrier less set supremum)))

(defun-sk amc12a-2010-p11-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (amc12a-2010-p11-supremum-p
     carrier less set supremum)))

(defun-sk amc12a-2010-p11-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (amc12a-2010-p11-valid-set-p carrier set)
      (amc12a-2010-p11-set-nonempty-p carrier set)
      (amc12a-2010-p11-bounded-above-p carrier less set))
     (amc12a-2010-p11-has-supremum-p
      carrier less set))))

(defun amc12a-2010-p11-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (amc12a-2010-p11-member-p carrier zero)
   (amc12a-2010-p11-member-p carrier one)
   (not (equal zero one))
   (amc12a-2010-p11-field-laws-p
    carrier add multiply negate inverse zero one)
   (amc12a-2010-p11-order-laws-p
    carrier add multiply zero less)
   (amc12a-2010-p11-binary less zero one)
   (amc12a-2010-p11-dedekind-complete-p
    carrier less)))

(defun amc12a-2010-p11-natural
    (add zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (amc12a-2010-p11-binary
     add
     one
     (amc12a-2010-p11-natural
      add zero one (- n 1)))))

(defun amc12a-2010-p11-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (amc12a-2010-p11-factorial (- n 1)))))

(defun amc12a-2010-p11-power
    (multiply one value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (amc12a-2010-p11-binary
     multiply
     value
     (amc12a-2010-p11-power
      multiply one value (- exponent 1)))))

(defun amc12a-2010-p11-difference
    (add negate left right)
  (amc12a-2010-p11-binary
   add
   left
   (amc12a-2010-p11-unary negate right)))

(defun amc12a-2010-p11-absolute
    (negate zero less value)
  (if (amc12a-2010-p11-binary less value zero)
      (amc12a-2010-p11-unary negate value)
    value))

(defun amc12a-2010-p11-distance
    (add negate zero less left right)
  (amc12a-2010-p11-absolute
   negate
   zero
   less
   (amc12a-2010-p11-difference
    add negate left right)))

(defun amc12a-2010-p11-exp-series-prefix
    (add multiply inverse zero one x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let* ((index (- terms 1))
           (power
            (amc12a-2010-p11-power
             multiply one x index))
           (factorial
            (amc12a-2010-p11-natural
             add zero one
             (amc12a-2010-p11-factorial index)))
           (term
            (amc12a-2010-p11-binary
             multiply
             power
             (amc12a-2010-p11-unary
              inverse factorial))))
      (amc12a-2010-p11-binary
       add
       (amc12a-2010-p11-exp-series-prefix
        add multiply inverse zero one x index)
       term))))

(defun-sk amc12a-2010-p11-exp-tail-p
    (add multiply negate inverse zero one less
     x value epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (amc12a-2010-p11-binary
      less
      (amc12a-2010-p11-distance
       add negate zero less
       (amc12a-2010-p11-exp-series-prefix
        add multiply inverse zero one x terms)
       value)
      epsilon))))

(defun-sk amc12a-2010-p11-exp-cutoff-exists-p
    (add multiply negate inverse zero one less
     x value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (amc12a-2010-p11-exp-tail-p
      add multiply negate inverse zero one less
      x value epsilon cutoff))))

(defun-sk amc12a-2010-p11-exp-converges-p
    (carrier add multiply negate inverse zero one less
     x value)
  (forall (epsilon)
    (implies
     (and
      (amc12a-2010-p11-member-p carrier epsilon)
      (amc12a-2010-p11-binary less zero epsilon))
     (amc12a-2010-p11-exp-cutoff-exists-p
      add multiply negate inverse zero one less
      x value epsilon))))

(defun amc12a-2010-p11-exp-value-p
    (carrier add multiply negate inverse zero one less
     x value)
  (and
   (amc12a-2010-p11-member-p carrier x)
   (amc12a-2010-p11-member-p carrier value)
   (amc12a-2010-p11-exp-converges-p
    carrier add multiply negate inverse zero one less
    x value)))

(defun-sk amc12a-2010-p11-real-power-value-p
    (carrier add multiply negate inverse zero one less
     base exponent value)
  (exists (log-base)
    (and
     (amc12a-2010-p11-member-p carrier base)
     (amc12a-2010-p11-member-p carrier exponent)
     (amc12a-2010-p11-member-p carrier value)
     (amc12a-2010-p11-binary less zero base)
     (amc12a-2010-p11-exp-value-p
      carrier add multiply negate inverse zero one less
      log-base base)
     (amc12a-2010-p11-exp-value-p
      carrier add multiply negate inverse zero one less
      (amc12a-2010-p11-binary
       multiply exponent log-base)
      value))))

(defun-sk amc12a-2010-p11-logb-value-p
    (carrier add multiply negate inverse zero one less
     base argument value)
  (exists (log-argument log-base)
    (and
     (amc12a-2010-p11-member-p carrier base)
     (amc12a-2010-p11-member-p carrier argument)
     (amc12a-2010-p11-member-p carrier value)
     (amc12a-2010-p11-binary less zero base)
     (amc12a-2010-p11-binary less zero argument)
     (amc12a-2010-p11-exp-value-p
      carrier add multiply negate inverse zero one less
      log-argument argument)
     (amc12a-2010-p11-exp-value-p
      carrier add multiply negate inverse zero one less
      log-base base)
     (equal
      value
      (amc12a-2010-p11-binary
       multiply
       log-argument
       (amc12a-2010-p11-unary inverse log-base))))))

(defun-sk amc12a-2010-p11-source-hypotheses-p
    (carrier add multiply negate inverse zero one less
     x b seven eight seven-to-seven)
  (exists (left-power right-power logarithm)
    (and
     (amc12a-2010-p11-real-power-value-p
      carrier add multiply negate inverse zero one less
      seven
      (amc12a-2010-p11-binary add x seven)
      left-power)
     (amc12a-2010-p11-real-power-value-p
      carrier add multiply negate inverse zero one less
      eight x right-power)
     (equal left-power right-power)
     (amc12a-2010-p11-logb-value-p
      carrier add multiply negate inverse zero one less
      b seven-to-seven logarithm)
     (equal x logarithm))))

(defun amc12a-2010-p11-statement
    (carrier add multiply negate inverse zero one less x b)
  (let* ((seven
          (amc12a-2010-p11-natural add zero one 7))
         (eight
          (amc12a-2010-p11-natural add zero one 8))
         (seven-to-seven
          (amc12a-2010-p11-power
           multiply one seven 7))
         (eight-over-seven
          (amc12a-2010-p11-binary
           multiply
           eight
           (amc12a-2010-p11-unary inverse seven))))
    (implies
     (and
      (amc12a-2010-p11-real-field-p
       carrier add multiply negate inverse zero one less)
      (amc12a-2010-p11-member-p carrier x)
      (amc12a-2010-p11-member-p carrier b)
      (amc12a-2010-p11-binary less zero b)
      (amc12a-2010-p11-source-hypotheses-p
       carrier add multiply negate inverse zero one less
       x b seven eight seven-to-seven))
     (equal b eight-over-seven))))

(value-triple :itpeval-statement-checked)
:q
