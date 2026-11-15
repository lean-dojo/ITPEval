;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_b1:
;; the recursively defined real sequence x(0)=1 and
;; x(n+1)=log(exp(x(n))-x(n)) has series sum exp(1)-1.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The arguments of the final predicate present a Dedekind-complete ordered
;; field, hence a copy of the real field. Tame APPLY$ objects retain arbitrary
;; real values, subsets, operations, and sequences, while DEFUN-SK supplies
;; the unbounded first-order quantifiers. Exponential is fixed by its exact
;; power series. Logarithm is the total real logarithm: zero maps to zero, and
;; every nonzero input maps to the inverse-exponential value of its absolute
;; value. Thus no rational approximation or finite sequence model is used.

(defun p2016b1-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p2016b1-unary (operation value)
  (apply$ operation (list value)))

(defun p2016b1-binary (operation left right)
  (apply$ operation (list left right)))

(defun-sk p2016b1-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p2016b1-member-p carrier x)
      (p2016b1-member-p carrier y)
      (p2016b1-member-p carrier z))
     (let* ((xy-add (p2016b1-binary add x y))
            (yz-add (p2016b1-binary add y z))
            (xy-multiply (p2016b1-binary multiply x y))
            (yz-multiply (p2016b1-binary multiply y z))
            (negative-x (p2016b1-unary negate x))
            (inverse-x (p2016b1-unary inverse x)))
       (and
        (p2016b1-member-p carrier xy-add)
        (p2016b1-member-p carrier xy-multiply)
        (p2016b1-member-p carrier negative-x)
        (p2016b1-member-p carrier inverse-x)
        (equal
         (p2016b1-binary add xy-add z)
         (p2016b1-binary add x yz-add))
        (equal xy-add (p2016b1-binary add y x))
        (equal (p2016b1-binary add x zero) x)
        (equal (p2016b1-binary add x negative-x) zero)
        (equal
         (p2016b1-binary multiply xy-multiply z)
         (p2016b1-binary multiply x yz-multiply))
        (equal xy-multiply (p2016b1-binary multiply y x))
        (equal (p2016b1-binary multiply x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p2016b1-binary multiply x inverse-x)
          one))
        (equal
         (p2016b1-binary multiply x yz-add)
         (p2016b1-binary
          add
          (p2016b1-binary multiply x y)
          (p2016b1-binary multiply x z))))))))

(defun-sk p2016b1-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p2016b1-member-p carrier x)
      (p2016b1-member-p carrier y)
      (p2016b1-member-p carrier z))
     (and
      (not (p2016b1-binary less x x))
      (or
       (equal x y)
       (p2016b1-binary less x y)
       (p2016b1-binary less y x))
      (implies
       (and
        (p2016b1-binary less x y)
        (p2016b1-binary less y z))
       (p2016b1-binary less x z))
      (implies
       (p2016b1-binary less x y)
       (p2016b1-binary
        less
        (p2016b1-binary add x z)
        (p2016b1-binary add y z)))
      (implies
       (and
        (p2016b1-binary less zero x)
        (p2016b1-binary less zero y))
       (p2016b1-binary
        less
        zero
        (p2016b1-binary multiply x y)))))))

(defun-sk p2016b1-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p2016b1-member-p carrier x))))

(defun-sk p2016b1-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p2016b1-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p2016b1-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p2016b1-member-p carrier x)
      (apply$ set (list x)))
     (not (p2016b1-binary less bound x)))))

(defun-sk p2016b1-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (p2016b1-member-p carrier bound)
     (p2016b1-upper-bound-p
      carrier less set bound))))

(defun-sk p2016b1-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (p2016b1-member-p carrier supremum)
     (p2016b1-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (p2016b1-member-p carrier bound)
       (p2016b1-upper-bound-p
        carrier less set bound))
      (not
       (p2016b1-binary less bound supremum))))))

(defun-sk p2016b1-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (p2016b1-least-upper-bound-p
     carrier less set supremum)))

(defun-sk p2016b1-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p2016b1-valid-set-p carrier set)
      (p2016b1-set-nonempty-p carrier set)
      (p2016b1-bounded-above-p carrier less set))
     (p2016b1-has-supremum-p
      carrier less set))))

(defun p2016b1-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p2016b1-member-p carrier zero)
   (p2016b1-member-p carrier one)
   (not (equal zero one))
   (p2016b1-field-laws-p
    carrier zero one add multiply negate inverse)
   (p2016b1-order-laws-p
    carrier zero add multiply less)
   (p2016b1-binary less zero one)
   (p2016b1-dedekind-complete-p carrier less)))

(defun p2016b1-r-add (add left right)
  (p2016b1-binary add left right))

(defun p2016b1-r-multiply (multiply left right)
  (p2016b1-binary multiply left right))

(defun p2016b1-r-negate (negate value)
  (p2016b1-unary negate value))

(defun p2016b1-r-inverse (inverse value)
  (p2016b1-unary inverse value))

(defun p2016b1-r-subtract (add negate left right)
  (p2016b1-r-add
   add left (p2016b1-r-negate negate right)))

(defun p2016b1-r-divide
    (multiply inverse numerator denominator)
  (p2016b1-r-multiply
   multiply
   numerator
   (p2016b1-r-inverse inverse denominator)))

(defun p2016b1-r-absolute-value
    (zero negate less value)
  (if (p2016b1-binary less value zero)
      (p2016b1-r-negate negate value)
    value))

(defun p2016b1-r-nat (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p2016b1-r-add
     add
     one
     (p2016b1-r-nat (1- n) zero one add))))

(defun p2016b1-r-power (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p2016b1-r-multiply
     multiply
     base
     (p2016b1-r-power
      base (1- exponent) one multiply))))

(defun p2016b1-r-factorial
    (n zero one add multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (p2016b1-r-multiply
     multiply
     (p2016b1-r-nat n zero one add)
     (p2016b1-r-factorial
      (1- n) zero one add multiply))))

(defun p2016b1-exp-prefix
    (x terms zero one add multiply inverse)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let ((index (1- terms)))
      (p2016b1-r-add
       add
       (p2016b1-exp-prefix
        x index zero one add multiply inverse)
       (p2016b1-r-divide
        multiply
        inverse
        (p2016b1-r-power x index one multiply)
        (p2016b1-r-factorial
         index zero one add multiply))))))

(defun-sk p2016b1-exp-tail-p
    (zero one add multiply negate inverse less
     x limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p2016b1-binary
      less
      (p2016b1-r-absolute-value
       zero
       negate
       less
       (p2016b1-r-subtract
        add
        negate
        (p2016b1-exp-prefix
         x terms zero one add multiply inverse)
        limit))
      epsilon))))

(defun-sk p2016b1-exp-cutoff-exists-p
    (zero one add multiply negate inverse less
     x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p2016b1-exp-tail-p
      zero one add multiply negate inverse less
      x limit epsilon cutoff))))

(defun-sk p2016b1-exp-value-p
    (carrier zero one add multiply negate inverse less
     x limit)
  (forall (epsilon)
    (and
     (p2016b1-member-p carrier limit)
     (implies
      (and
       (p2016b1-member-p carrier epsilon)
       (p2016b1-binary less zero epsilon))
      (p2016b1-exp-cutoff-exists-p
       zero one add multiply negate inverse less
       x limit epsilon)))))

(defun-sk p2016b1-exp-operation-values-p
    (carrier zero one add multiply negate inverse less
     exponential)
  (forall (x)
    (implies
     (p2016b1-member-p carrier x)
     (p2016b1-exp-value-p
      carrier zero one add multiply negate inverse less
      x (p2016b1-unary exponential x)))))

(defun p2016b1-exp-operation-p
    (carrier zero one add multiply negate inverse less
     exponential)
  (and
   (tamep-functionp exponential)
   (p2016b1-exp-operation-values-p
    carrier zero one add multiply negate inverse less
    exponential)))

(defun-sk p2016b1-log-operation-values-p
    (carrier zero negate less exponential logarithm)
  (forall (x)
    (implies
     (p2016b1-member-p carrier x)
     (let ((log-x (p2016b1-unary logarithm x)))
       (and
        (p2016b1-member-p carrier log-x)
        (if (equal x zero)
            (equal log-x zero)
          (equal
           (p2016b1-unary exponential log-x)
           (p2016b1-r-absolute-value
            zero negate less x))))))))

(defun-sk p2016b1-log-exp-values-p
    (carrier exponential logarithm)
  (forall (x)
    (implies
     (p2016b1-member-p carrier x)
     (equal
      (p2016b1-unary
       logarithm
       (p2016b1-unary exponential x))
      x))))

(defun p2016b1-log-operation-p
    (carrier zero negate less exponential logarithm)
  (and
   (tamep-functionp logarithm)
   (p2016b1-log-operation-values-p
    carrier zero negate less exponential logarithm)
   (p2016b1-log-exp-values-p
    carrier exponential logarithm)))

(defun-sk p2016b1-sequence-values-p
    (carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (p2016b1-member-p
      carrier
      (p2016b1-unary sequence n)))))

(defun p2016b1-sequence-p (carrier sequence)
  (and
   (tamep-functionp sequence)
   (p2016b1-sequence-values-p carrier sequence)))

(defun-sk p2016b1-recurrence-p
    (sequence add negate exponential logarithm)
  (forall (n)
    (implies
     (natp n)
     (equal
      (p2016b1-unary sequence (+ n 1))
      (p2016b1-unary
       logarithm
       (p2016b1-r-subtract
        add
        negate
        (p2016b1-unary
         exponential
         (p2016b1-unary sequence n))
        (p2016b1-unary sequence n)))))))

(defun p2016b1-series-prefix
    (terms sequence zero add)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let ((index (1- terms)))
      (p2016b1-r-add
       add
       (p2016b1-series-prefix
        index sequence zero add)
       (p2016b1-unary sequence index)))))

(defun-sk p2016b1-series-tail-p
    (sequence zero add negate less
     limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p2016b1-binary
      less
      (p2016b1-r-absolute-value
       zero
       negate
       less
       (p2016b1-r-subtract
        add
        negate
        (p2016b1-series-prefix
         terms sequence zero add)
        limit))
      epsilon))))

(defun-sk p2016b1-series-cutoff-exists-p
    (sequence zero add negate less
     limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p2016b1-series-tail-p
      sequence zero add negate less
      limit epsilon cutoff))))

(defun-sk p2016b1-series-converges-to-p
    (carrier sequence zero add negate less limit)
  (forall (epsilon)
    (and
     (p2016b1-member-p carrier limit)
     (implies
      (and
       (p2016b1-member-p carrier epsilon)
       (p2016b1-binary less zero epsilon))
      (p2016b1-series-cutoff-exists-p
       sequence zero add negate less
       limit epsilon)))))

(defun p2016b1-solution
    (one add negate exponential)
  (p2016b1-r-subtract
   add
   negate
   (p2016b1-unary exponential one)
   one))

(defun putnambench-putnam-2016-b1-statement
    (carrier zero one add multiply negate inverse less
     exponential logarithm sequence)
  (implies
   (and
    (p2016b1-real-field-p
     carrier zero one add multiply negate inverse less)
    (p2016b1-exp-operation-p
     carrier zero one add multiply negate inverse less
     exponential)
    (p2016b1-log-operation-p
     carrier zero negate less exponential logarithm)
    (p2016b1-sequence-p carrier sequence)
    (equal (p2016b1-unary sequence 0) one)
    (p2016b1-recurrence-p
     sequence add negate exponential logarithm))
   (p2016b1-series-converges-to-p
    carrier
    sequence
    zero
    add
    negate
    less
    (p2016b1-solution
     one add negate exponential))))

(value-triple :itpeval-statement-checked)
:q
