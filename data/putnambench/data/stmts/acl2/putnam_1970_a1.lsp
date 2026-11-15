;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_a1:
;; for positive real a and b, the power series of exp(a*x)*cos(b*x) has
;; either no zero coefficients or infinitely many zero coefficients. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The arguments of the final predicate present the complete ordered field of
;; reals and its exponential and cosine functions. Completeness characterizes
;; the ordered field up to its unique order-preserving isomorphism with R, and
;; the globally convergent power series below uniquely characterize exp and
;; cos. APPLY$ function objects retain the arbitrary coefficient function
;; p : N -> R; it is not replaced by a finite table or a rational subdomain.

(defun putnam-1970-a1-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun putnam-1970-a1-unary (operation x)
  (apply$ operation (list x)))

(defun putnam-1970-a1-binary (operation x y)
  (apply$ operation (list x y)))

(defun putnam-1970-a1-positive-p (carrier less zero x)
  (and
   (putnam-1970-a1-member-p carrier x)
   (apply$ less (list zero x))))

(defun-sk putnam-1970-a1-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-1970-a1-member-p carrier x)
      (putnam-1970-a1-member-p carrier y)
      (putnam-1970-a1-member-p carrier z))
     (and
      (putnam-1970-a1-member-p
       carrier (putnam-1970-a1-binary add x y))
      (putnam-1970-a1-member-p
       carrier (putnam-1970-a1-binary multiply x y))
      (putnam-1970-a1-member-p
       carrier (putnam-1970-a1-unary negate x))
      (putnam-1970-a1-member-p
       carrier (putnam-1970-a1-unary inverse x))
      (equal
       (putnam-1970-a1-binary
        add (putnam-1970-a1-binary add x y) z)
       (putnam-1970-a1-binary
        add x (putnam-1970-a1-binary add y z)))
      (equal
       (putnam-1970-a1-binary add x y)
       (putnam-1970-a1-binary add y x))
      (equal (putnam-1970-a1-binary add x zero) x)
      (equal
       (putnam-1970-a1-binary
        add x (putnam-1970-a1-unary negate x))
       zero)
      (equal
       (putnam-1970-a1-binary
        multiply (putnam-1970-a1-binary multiply x y) z)
       (putnam-1970-a1-binary
        multiply x (putnam-1970-a1-binary multiply y z)))
      (equal
       (putnam-1970-a1-binary multiply x y)
       (putnam-1970-a1-binary multiply y x))
      (equal (putnam-1970-a1-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (putnam-1970-a1-binary
         multiply x (putnam-1970-a1-unary inverse x))
        one))
      (equal
       (putnam-1970-a1-binary
        multiply x (putnam-1970-a1-binary add y z))
       (putnam-1970-a1-binary
        add
        (putnam-1970-a1-binary multiply x y)
        (putnam-1970-a1-binary multiply x z)))))))

(defun-sk putnam-1970-a1-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (putnam-1970-a1-member-p carrier x)
      (putnam-1970-a1-member-p carrier y)
      (putnam-1970-a1-member-p carrier z))
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
         (putnam-1970-a1-binary add x z)
         (putnam-1970-a1-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list
         zero
         (putnam-1970-a1-binary multiply x y))))))))

(defun-sk putnam-1970-a1-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1970-a1-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1970-a1-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1970-a1-member-p carrier x)
      (apply$ set (list x)))
     (not (apply$ less (list bound x))))))

(defun-sk putnam-1970-a1-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1970-a1-member-p carrier bound)
     (putnam-1970-a1-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1970-a1-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1970-a1-member-p carrier supremum)
     (putnam-1970-a1-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1970-a1-member-p carrier bound)
       (putnam-1970-a1-upper-bound-p
        carrier less set bound))
      (not (apply$ less (list bound supremum)))))))

(defun-sk putnam-1970-a1-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1970-a1-supremum-p
     carrier less set supremum)))

(defun-sk putnam-1970-a1-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1970-a1-set-nonempty-p carrier set)
      (putnam-1970-a1-bounded-above-p carrier less set))
     (putnam-1970-a1-has-supremum-p
      carrier less set))))

(defun putnam-1970-a1-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1970-a1-member-p carrier zero)
   (putnam-1970-a1-member-p carrier one)
   (not (equal zero one))
   (putnam-1970-a1-field-laws-p
    carrier add multiply negate inverse zero one)
   (putnam-1970-a1-order-laws-p
    carrier add multiply zero less)
   (apply$ less (list zero one))
   (putnam-1970-a1-dedekind-complete-p
    carrier less)))

(defun putnam-1970-a1-power (multiply one x exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1970-a1-binary
     multiply
     x
     (putnam-1970-a1-power
      multiply one x (- exponent 1)))))

(defun putnam-1970-a1-natural-value (add zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1970-a1-binary
     add
     one
     (putnam-1970-a1-natural-value
      add zero one (- n 1)))))

(defun putnam-1970-a1-factorial-value
    (add multiply zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (putnam-1970-a1-binary
     multiply
     (putnam-1970-a1-natural-value
      add zero one n)
     (putnam-1970-a1-factorial-value
      add multiply zero one (- n 1)))))

(defun putnam-1970-a1-exp-term
    (add multiply inverse zero one x n)
  (putnam-1970-a1-binary
   multiply
   (putnam-1970-a1-power multiply one x n)
   (putnam-1970-a1-unary
    inverse
    (putnam-1970-a1-factorial-value
     add multiply zero one n))))

(defun putnam-1970-a1-exp-prefix
    (add multiply inverse zero one x count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (- count 1)))
      (putnam-1970-a1-binary
       add
       (putnam-1970-a1-exp-prefix
        add multiply inverse zero one x index)
       (putnam-1970-a1-exp-term
        add multiply inverse zero one x index)))))

(defun putnam-1970-a1-cos-term
    (add multiply negate inverse zero one x n)
  (let* ((degree (* 2 n))
         (unsigned
          (putnam-1970-a1-binary
           multiply
           (putnam-1970-a1-power
            multiply one x degree)
           (putnam-1970-a1-unary
            inverse
            (putnam-1970-a1-factorial-value
             add multiply zero one degree)))))
    (if (evenp n)
        unsigned
      (putnam-1970-a1-unary negate unsigned))))

(defun putnam-1970-a1-cos-prefix
    (add multiply negate inverse zero one x count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (- count 1)))
      (putnam-1970-a1-binary
       add
       (putnam-1970-a1-cos-prefix
        add multiply negate inverse zero one x index)
       (putnam-1970-a1-cos-term
        add multiply negate inverse zero one x index)))))

(defun putnam-1970-a1-close-p
    (add multiply negate less left right epsilon)
  (let ((difference
         (putnam-1970-a1-binary
          add left (putnam-1970-a1-unary negate right))))
    (apply$
     less
     (list
      (putnam-1970-a1-binary
       multiply difference difference)
      (putnam-1970-a1-binary
       multiply epsilon epsilon)))))

(defun-sk putnam-1970-a1-exp-tail-p
    (add multiply negate inverse zero one less
     exponential x epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (putnam-1970-a1-close-p
      add multiply negate less
      (putnam-1970-a1-exp-prefix
       add multiply inverse zero one x count)
      (putnam-1970-a1-unary exponential x)
      epsilon))))

(defun-sk putnam-1970-a1-exp-cutoff-exists-p
    (add multiply negate inverse zero one less
     exponential x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1970-a1-exp-tail-p
      add multiply negate inverse zero one less
      exponential x epsilon cutoff))))

(defun-sk putnam-1970-a1-exp-series-p
    (carrier add multiply negate inverse zero one less exponential)
  (forall (x epsilon)
    (implies
     (and
      (putnam-1970-a1-member-p carrier x)
      (putnam-1970-a1-positive-p
       carrier less zero epsilon))
     (and
      (putnam-1970-a1-member-p
       carrier (putnam-1970-a1-unary exponential x))
      (putnam-1970-a1-exp-cutoff-exists-p
       add multiply negate inverse zero one less
       exponential x epsilon)))))

(defun-sk putnam-1970-a1-cos-tail-p
    (add multiply negate inverse zero one less
     cosine x epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (putnam-1970-a1-close-p
      add multiply negate less
      (putnam-1970-a1-cos-prefix
       add multiply negate inverse zero one x count)
      (putnam-1970-a1-unary cosine x)
      epsilon))))

(defun-sk putnam-1970-a1-cos-cutoff-exists-p
    (add multiply negate inverse zero one less
     cosine x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1970-a1-cos-tail-p
      add multiply negate inverse zero one less
      cosine x epsilon cutoff))))

(defun-sk putnam-1970-a1-cos-series-p
    (carrier add multiply negate inverse zero one less cosine)
  (forall (x epsilon)
    (implies
     (and
      (putnam-1970-a1-member-p carrier x)
      (putnam-1970-a1-positive-p
       carrier less zero epsilon))
     (and
      (putnam-1970-a1-member-p
       carrier (putnam-1970-a1-unary cosine x))
      (putnam-1970-a1-cos-cutoff-exists-p
       add multiply negate inverse zero one less
       cosine x epsilon)))))

(defun putnam-1970-a1-exp-cos-p
    (carrier add multiply negate inverse zero one less
     exponential cosine)
  (and
   (tamep-functionp exponential)
   (tamep-functionp cosine)
   (putnam-1970-a1-exp-series-p
    carrier add multiply negate inverse zero one less
    exponential)
   (putnam-1970-a1-cos-series-p
    carrier add multiply negate inverse zero one less
    cosine)))

(defun-sk putnam-1970-a1-coefficient-values-p
    (carrier coefficients)
  (forall (n)
    (implies
     (natp n)
     (putnam-1970-a1-member-p
      carrier (apply$ coefficients (list n))))))

(defun putnam-1970-a1-power-series-prefix
    (coefficients add multiply zero one x count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (- count 1)))
      (putnam-1970-a1-binary
       add
       (putnam-1970-a1-power-series-prefix
        coefficients add multiply zero one x index)
       (putnam-1970-a1-binary
        multiply
        (apply$ coefficients (list index))
        (putnam-1970-a1-power
         multiply one x index))))))

(defun-sk putnam-1970-a1-power-series-tail-p
    (coefficients add multiply negate zero one less
     x target epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (putnam-1970-a1-close-p
      add multiply negate less
      (putnam-1970-a1-power-series-prefix
       coefficients add multiply zero one x count)
      target
      epsilon))))

(defun-sk putnam-1970-a1-power-series-cutoff-exists-p
    (coefficients add multiply negate zero one less
     x target epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1970-a1-power-series-tail-p
      coefficients add multiply negate zero one less
      x target epsilon cutoff))))

(defun-sk putnam-1970-a1-power-series-converges-p
    (carrier coefficients add multiply negate zero one less
     x target)
  (forall (epsilon)
    (implies
     (putnam-1970-a1-positive-p
      carrier less zero epsilon)
     (putnam-1970-a1-power-series-cutoff-exists-p
      coefficients add multiply negate zero one less
      x target epsilon))))

(defun putnam-1970-a1-target-value
    (multiply exponential cosine a b x)
  (putnam-1970-a1-binary
   multiply
   (putnam-1970-a1-unary
    exponential
    (putnam-1970-a1-binary multiply a x))
   (putnam-1970-a1-unary
    cosine
    (putnam-1970-a1-binary multiply b x))))

(defun-sk putnam-1970-a1-local-expansion-all-x-p
    (carrier coefficients add multiply negate zero one less
     exponential cosine a b radius)
  (forall (x)
    (implies
     (and
      (putnam-1970-a1-member-p carrier x)
      (apply$
       less
       (list
        (putnam-1970-a1-unary negate radius)
        x))
      (apply$ less (list x radius)))
     (putnam-1970-a1-power-series-converges-p
      carrier coefficients add multiply negate zero one less
      x
      (putnam-1970-a1-target-value
       multiply exponential cosine a b x)))))

(defun-sk putnam-1970-a1-local-expansion-p
    (carrier coefficients add multiply negate zero one less
     exponential cosine a b)
  (exists (radius)
    (and
     (putnam-1970-a1-positive-p
      carrier less zero radius)
     (putnam-1970-a1-local-expansion-all-x-p
      carrier coefficients add multiply negate zero one less
      exponential cosine a b radius))))

(defun-sk putnam-1970-a1-zero-set-empty-p
    (coefficients zero)
  (forall (n)
    (implies
     (natp n)
     (not (equal
           (apply$ coefficients (list n))
           zero)))))

(defun-sk putnam-1970-a1-zero-above-exists-p
    (coefficients zero threshold)
  (exists (n)
    (and
     (natp n)
     (< threshold n)
     (equal
      (apply$ coefficients (list n))
      zero))))

(defun-sk putnam-1970-a1-zero-set-infinite-p
    (coefficients zero)
  (forall (threshold)
    (implies
     (natp threshold)
     (putnam-1970-a1-zero-above-exists-p
      coefficients zero threshold))))

(defun putnambench-putnam-1970-a1-statement
    (a b coefficients
     carrier add multiply negate inverse zero one less
     exponential cosine)
  (implies
   (and
    (putnam-1970-a1-real-field-p
     carrier add multiply negate inverse zero one less)
    (putnam-1970-a1-exp-cos-p
     carrier add multiply negate inverse zero one less
     exponential cosine)
    (putnam-1970-a1-positive-p carrier less zero a)
    (putnam-1970-a1-positive-p carrier less zero b)
    (tamep-functionp coefficients)
    (putnam-1970-a1-coefficient-values-p
     carrier coefficients)
    (putnam-1970-a1-local-expansion-p
     carrier coefficients add multiply negate zero one less
     exponential cosine a b))
   (or
    (putnam-1970-a1-zero-set-empty-p
     coefficients zero)
    (putnam-1970-a1-zero-set-infinite-p
     coefficients zero))))

(value-triple :itpeval-statement-checked)
:q
