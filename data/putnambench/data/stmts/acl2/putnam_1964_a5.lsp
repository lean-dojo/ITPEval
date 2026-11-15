;; Statement-only formalization of PutnamBench corpus artifact putnam_1964_a5:
;; one real constant uniformly bounds the series of prefix-sum ratios for
;; every positive real sequence with convergent reciprocal series. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the Dedekind-complete ordered field of real
;; numbers. A tame APPLY$ object presents an arbitrary natural-indexed real
;; sequence. Both infinite sums are defined by epsilon convergence of their
;; finite partial sums, and all limit and bound witnesses remain internal.

(defun p1964a5-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p1964a5-unary (operation x)
  (apply$ operation (list x)))

(defun p1964a5-binary (operation x y)
  (apply$ operation (list x y)))

(defun p1964a5-subtract (add negate x y)
  (p1964a5-binary add x (p1964a5-unary negate y)))

(defun p1964a5-less-equal-p (less x y)
  (not (apply$ less (list y x))))

(defun p1964a5-absolute (less negate zero x)
  (if (apply$ less (list x zero))
      (p1964a5-unary negate x)
    x))

(defun-sk p1964a5-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p1964a5-member-p carrier x)
      (p1964a5-member-p carrier y)
      (p1964a5-member-p carrier z))
     (and
      (p1964a5-member-p
       carrier (p1964a5-binary add x y))
      (p1964a5-member-p
       carrier (p1964a5-binary multiply x y))
      (p1964a5-member-p carrier (p1964a5-unary negate x))
      (implies
       (not (equal x zero))
       (p1964a5-member-p carrier (p1964a5-unary inverse x)))
      (equal
       (p1964a5-binary add (p1964a5-binary add x y) z)
       (p1964a5-binary add x (p1964a5-binary add y z)))
      (equal
       (p1964a5-binary add x y)
       (p1964a5-binary add y x))
      (equal (p1964a5-binary add x zero) x)
      (equal
       (p1964a5-binary add x (p1964a5-unary negate x))
       zero)
      (equal
       (p1964a5-binary
        multiply (p1964a5-binary multiply x y) z)
       (p1964a5-binary
        multiply x (p1964a5-binary multiply y z)))
      (equal
       (p1964a5-binary multiply x y)
       (p1964a5-binary multiply y x))
      (equal (p1964a5-binary multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1964a5-binary
         multiply x (p1964a5-unary inverse x))
        one))
      (equal
       (p1964a5-binary
        multiply x (p1964a5-binary add y z))
       (p1964a5-binary
        add
        (p1964a5-binary multiply x y)
        (p1964a5-binary multiply x z)))))))

(defun-sk p1964a5-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p1964a5-member-p carrier x)
      (p1964a5-member-p carrier y)
      (p1964a5-member-p carrier z))
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
         (p1964a5-binary add x z)
         (p1964a5-binary add y z))))
      (implies
       (and
        (apply$ less (list zero x))
        (apply$ less (list zero y)))
       (apply$
        less
        (list
         zero
         (p1964a5-binary multiply x y))))))))

(defun-sk p1964a5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p1964a5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p1964a5-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p1964a5-member-p carrier x)
      (apply$ set (list x)))
     (p1964a5-less-equal-p less x bound))))

(defun-sk p1964a5-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p1964a5-member-p carrier bound)
     (p1964a5-upper-bound-p carrier less set bound))))

(defun-sk p1964a5-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p1964a5-member-p carrier supremum)
     (p1964a5-upper-bound-p carrier less set supremum)
     (implies
      (and
       (p1964a5-member-p carrier bound)
       (p1964a5-upper-bound-p carrier less set bound))
      (p1964a5-less-equal-p less supremum bound)))))

(defun-sk p1964a5-has-supremum-p (carrier less set)
  (exists (supremum)
    (p1964a5-supremum-p carrier less set supremum)))

(defun-sk p1964a5-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p1964a5-set-nonempty-p carrier set)
      (p1964a5-bounded-above-p carrier less set))
     (p1964a5-has-supremum-p carrier less set))))

(defun p1964a5-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p1964a5-member-p carrier zero)
   (p1964a5-member-p carrier one)
   (not (equal zero one))
   (p1964a5-field-laws-p
    carrier zero one add multiply negate inverse)
   (p1964a5-order-laws-p carrier zero add multiply less)
   (apply$ less (list zero one))
   (p1964a5-dedekind-complete-p carrier less)))

(defun-sk p1964a5-natural-real-sequence-p (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (p1964a5-member-p
      carrier (apply$ sequence (list n))))))

(defun-sk p1964a5-positive-sequence-p (zero less sequence)
  (forall (n)
    (implies
     (natp n)
     (apply$
      less
      (list zero (apply$ sequence (list n)))))))

(defun p1964a5-natural-value (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1964a5-binary
     add
     one
     (p1964a5-natural-value (- n 1) zero one add))))

(defun p1964a5-prefix-sum (count sequence zero add)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p1964a5-binary
     add
     (p1964a5-prefix-sum (- count 1) sequence zero add)
     (apply$ sequence (list (- count 1))))))

(defun p1964a5-reciprocal-term
    (sequence n one multiply inverse)
  (p1964a5-binary
   multiply
   one
   (p1964a5-unary
    inverse (apply$ sequence (list n)))))

(defun p1964a5-left-term
    (sequence n zero one add multiply inverse)
  (p1964a5-binary
   multiply
   (p1964a5-natural-value (+ n 1) zero one add)
   (p1964a5-unary
    inverse
    (p1964a5-prefix-sum (+ n 1) sequence zero add))))

(defun p1964a5-reciprocal-partial-sum
    (count sequence zero one add multiply inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p1964a5-binary
     add
     (p1964a5-reciprocal-partial-sum
      (- count 1) sequence zero one add multiply inverse)
     (p1964a5-reciprocal-term
      sequence (- count 1) one multiply inverse))))

(defun p1964a5-left-partial-sum
    (count sequence zero one add multiply inverse)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p1964a5-binary
     add
     (p1964a5-left-partial-sum
      (- count 1) sequence zero one add multiply inverse)
     (p1964a5-left-term
      sequence (- count 1) zero one add multiply inverse))))

(defun p1964a5-series-partial-sum
    (kind count sequence zero one add multiply inverse)
  (if (equal kind :reciprocal)
      (p1964a5-reciprocal-partial-sum
       count sequence zero one add multiply inverse)
    (p1964a5-left-partial-sum
     count sequence zero one add multiply inverse)))

(defun-sk p1964a5-series-tail-p
    (kind sequence zero one add multiply negate inverse less
     limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (apply$
      less
      (list
       (p1964a5-absolute
        less negate zero
        (p1964a5-subtract
         add negate
         (p1964a5-series-partial-sum
          kind count sequence
          zero one add multiply inverse)
         limit))
       epsilon)))))

(defun-sk p1964a5-series-cutoff-exists-p
    (kind sequence zero one add multiply negate inverse less
     limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1964a5-series-tail-p
      kind sequence zero one add multiply negate inverse less
      limit epsilon cutoff))))

(defun-sk p1964a5-series-converges-to-p
    (carrier kind sequence zero one add multiply negate inverse
     less limit)
  (forall (epsilon)
    (implies
     (and
      (p1964a5-member-p carrier epsilon)
      (apply$ less (list zero epsilon)))
     (p1964a5-series-cutoff-exists-p
      kind sequence zero one add multiply negate inverse less
      limit epsilon))))

(defun-sk p1964a5-reciprocal-series-converges-p
    (carrier sequence zero one add multiply negate inverse less)
  (exists (limit)
    (and
     (p1964a5-member-p carrier limit)
     (p1964a5-series-converges-to-p
      carrier :reciprocal sequence
      zero one add multiply negate inverse less limit))))

(defun p1964a5-qualifying-sequence-p
    (carrier sequence zero one add multiply negate inverse less)
  (and
   (tamep-functionp sequence)
   (p1964a5-natural-real-sequence-p carrier sequence)
   (p1964a5-positive-sequence-p zero less sequence)
   (p1964a5-reciprocal-series-converges-p
    carrier sequence
    zero one add multiply negate inverse less)))

(defun-sk p1964a5-bound-witnesses-exist-p
    (carrier sequence zero one add multiply negate inverse less k)
  (exists (left-limit reciprocal-limit)
    (and
     (p1964a5-member-p carrier left-limit)
     (p1964a5-member-p carrier reciprocal-limit)
     (p1964a5-series-converges-to-p
      carrier :left sequence
      zero one add multiply negate inverse less left-limit)
     (p1964a5-series-converges-to-p
      carrier :reciprocal sequence
      zero one add multiply negate inverse less reciprocal-limit)
     (p1964a5-less-equal-p
      less
      left-limit
      (p1964a5-binary multiply k reciprocal-limit)))))

(defun-sk p1964a5-uniform-bound-at-k-p
    (carrier zero one add multiply negate inverse less k)
  (forall (sequence)
    (implies
     (p1964a5-qualifying-sequence-p
      carrier sequence
      zero one add multiply negate inverse less)
     (p1964a5-bound-witnesses-exist-p
      carrier sequence
      zero one add multiply negate inverse less k))))

(defun-sk p1964a5-uniform-bound-exists-p
    (carrier zero one add multiply negate inverse less)
  (exists (k)
    (and
     (p1964a5-member-p carrier k)
     (p1964a5-uniform-bound-at-k-p
      carrier zero one add multiply negate inverse less k))))

(defun putnambench-putnam-1964-a5-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
  (implies
   (p1964a5-real-field-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less)
   (p1964a5-uniform-bound-exists-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less)))

(value-triple :itpeval-statement-checked)
:q
