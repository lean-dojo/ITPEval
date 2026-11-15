;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_b6:
;; the number of unordered collections of factorial-valued coins summing to
;; n! satisfies the stated two-sided real exponential bounds for some constant
;; independent of n. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The final predicate presents a Dedekind-complete ordered field, hence a
;; copy of the real field. The exponential is fixed by its exact power series,
;; and logarithm is its inverse on the positive reals, so P07B6-R-POWR is the
;; usual positive-base real power. The recursive coin count is definitionally
;; the number of multisets of denominations 1!,...,n! whose sum is n!.

(defun p07b6-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p07b6-unary (operation value)
  (apply$ operation (list value)))

(defun p07b6-binary (operation left right)
  (apply$ operation (list left right)))

(defun-sk p07b6-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (p07b6-member-p carrier x)
      (p07b6-member-p carrier y)
      (p07b6-member-p carrier z))
     (let* ((xy-add (p07b6-binary add x y))
            (yz-add (p07b6-binary add y z))
            (xy-multiply (p07b6-binary multiply x y))
            (yz-multiply (p07b6-binary multiply y z))
            (negative-x (p07b6-unary negate x))
            (inverse-x (p07b6-unary inverse x)))
       (and
        (p07b6-member-p carrier xy-add)
        (p07b6-member-p carrier xy-multiply)
        (p07b6-member-p carrier negative-x)
        (p07b6-member-p carrier inverse-x)
        (equal
         (p07b6-binary add xy-add z)
         (p07b6-binary add x yz-add))
        (equal xy-add (p07b6-binary add y x))
        (equal (p07b6-binary add x zero) x)
        (equal (p07b6-binary add x negative-x) zero)
        (equal
         (p07b6-binary multiply xy-multiply z)
         (p07b6-binary multiply x yz-multiply))
        (equal xy-multiply (p07b6-binary multiply y x))
        (equal (p07b6-binary multiply x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal (p07b6-binary multiply x inverse-x) one))
        (equal
         (p07b6-binary multiply x yz-add)
         (p07b6-binary
          add
          (p07b6-binary multiply x y)
          (p07b6-binary multiply x z))))))))

(defun-sk p07b6-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (p07b6-member-p carrier x)
      (p07b6-member-p carrier y)
      (p07b6-member-p carrier z))
     (and
      (not (p07b6-binary less x x))
      (or
       (equal x y)
       (p07b6-binary less x y)
       (p07b6-binary less y x))
      (implies
       (and
        (p07b6-binary less x y)
        (p07b6-binary less y z))
       (p07b6-binary less x z))
      (implies
       (p07b6-binary less x y)
       (p07b6-binary
        less
        (p07b6-binary add x z)
        (p07b6-binary add y z)))
      (implies
       (and
        (p07b6-binary less zero x)
        (p07b6-binary less zero y))
       (p07b6-binary
        less
        zero
        (p07b6-binary multiply x y)))))))

(defun-sk p07b6-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p07b6-member-p carrier x))))

(defun-sk p07b6-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p07b6-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p07b6-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p07b6-member-p carrier x)
      (apply$ set (list x)))
     (not (p07b6-binary less bound x)))))

(defun-sk p07b6-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p07b6-member-p carrier bound)
     (p07b6-upper-bound-p carrier less set bound))))

(defun-sk p07b6-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (p07b6-member-p carrier supremum)
     (p07b6-upper-bound-p carrier less set supremum)
     (implies
      (and
       (p07b6-member-p carrier bound)
       (p07b6-upper-bound-p carrier less set bound))
      (not (p07b6-binary less bound supremum))))))

(defun-sk p07b6-has-supremum-p (carrier less set)
  (exists (supremum)
    (p07b6-least-upper-bound-p
     carrier less set supremum)))

(defun-sk p07b6-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p07b6-valid-set-p carrier set)
      (p07b6-set-nonempty-p carrier set)
      (p07b6-bounded-above-p carrier less set))
     (p07b6-has-supremum-p carrier less set))))

(defun p07b6-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p07b6-member-p carrier zero)
   (p07b6-member-p carrier one)
   (not (equal zero one))
   (p07b6-field-laws-p
    carrier zero one add multiply negate inverse)
   (p07b6-order-laws-p
    carrier zero add multiply less)
   (p07b6-binary less zero one)
   (p07b6-dedekind-complete-p carrier less)))

(defun p07b6-r-add (add left right)
  (p07b6-binary add left right))

(defun p07b6-r-multiply (multiply left right)
  (p07b6-binary multiply left right))

(defun p07b6-r-negate (negate value)
  (p07b6-unary negate value))

(defun p07b6-r-inverse (inverse value)
  (p07b6-unary inverse value))

(defun p07b6-r-subtract (add negate left right)
  (p07b6-r-add add left (p07b6-r-negate negate right)))

(defun p07b6-r-divide
    (multiply inverse numerator denominator)
  (p07b6-r-multiply
   multiply numerator (p07b6-r-inverse inverse denominator)))

(defun p07b6-r-absolute-value (zero negate less value)
  (if (p07b6-binary less value zero)
      (p07b6-r-negate negate value)
    value))

(defun p07b6-r-nat (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p07b6-r-add
     add one (p07b6-r-nat (1- n) zero one add))))

(defun p07b6-r-power (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p07b6-r-multiply
     multiply
     base
     (p07b6-r-power base (1- exponent) one multiply))))

(defun p07b6-r-factorial
    (n zero one add multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (p07b6-r-multiply
     multiply
     (p07b6-r-nat n zero one add)
     (p07b6-r-factorial
      (1- n) zero one add multiply))))

(defun p07b6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (p07b6-factorial (1- n)))))

(defun p07b6-coin-count (amount maximum-index)
  (declare
   (xargs
    :measure
    (make-ord
     1
     (+ 1 (nfix maximum-index))
     (nfix amount))
    :well-founded-relation o<))
  (if (and (natp amount) (natp maximum-index))
      (cond
       ((zp amount) 1)
       ((zp maximum-index) 0)
       (t
        (let ((coin (p07b6-factorial maximum-index)))
          (+
           (p07b6-coin-count amount (1- maximum-index))
           (if (<= coin amount)
               (p07b6-coin-count
                (- amount coin) maximum-index)
             0)))))
    0))

(defun p07b6-f (n)
  (if (natp n)
      (p07b6-coin-count (p07b6-factorial n) n)
    0))

(defun p07b6-exp-prefix
    (x terms zero one add multiply inverse)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let ((index (1- terms)))
      (p07b6-r-add
       add
       (p07b6-exp-prefix
        x index zero one add multiply inverse)
       (p07b6-r-divide
        multiply
        inverse
        (p07b6-r-power x index one multiply)
        (p07b6-r-factorial
         index zero one add multiply))))))

(defun-sk p07b6-exp-tail-p
    (zero one add multiply negate inverse less
     x limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p07b6-binary
      less
      (p07b6-r-absolute-value
       zero
       negate
       less
       (p07b6-r-subtract
        add
        negate
        (p07b6-exp-prefix
         x terms zero one add multiply inverse)
        limit))
      epsilon))))

(defun-sk p07b6-exp-cutoff-exists-p
    (zero one add multiply negate inverse less
     x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p07b6-exp-tail-p
      zero one add multiply negate inverse less
      x limit epsilon cutoff))))

(defun-sk p07b6-exp-value-p
    (carrier zero one add multiply negate inverse less
     x limit)
  (forall (epsilon)
    (and
     (p07b6-member-p carrier limit)
     (implies
      (and
       (p07b6-member-p carrier epsilon)
       (p07b6-binary less zero epsilon))
      (p07b6-exp-cutoff-exists-p
       zero one add multiply negate inverse less
       x limit epsilon)))))

(defun-sk p07b6-exp-operation-values-p
    (carrier zero one add multiply negate inverse less
     exponential)
  (forall (x)
    (implies
     (p07b6-member-p carrier x)
     (p07b6-exp-value-p
      carrier zero one add multiply negate inverse less
      x (p07b6-unary exponential x)))))

(defun p07b6-exp-operation-p
    (carrier zero one add multiply negate inverse less
     exponential)
  (and
   (tamep-functionp exponential)
   (p07b6-exp-operation-values-p
    carrier zero one add multiply negate inverse less
    exponential)))

(defun-sk p07b6-log-operation-values-p
    (carrier zero less exponential logarithm)
  (forall (x)
    (implies
     (p07b6-member-p carrier x)
     (let ((log-x (p07b6-unary logarithm x)))
       (and
        (p07b6-member-p carrier log-x)
        (if (p07b6-binary less zero x)
            (equal (p07b6-unary exponential log-x) x)
          (equal log-x zero)))))))

(defun p07b6-log-operation-p
    (carrier zero less exponential logarithm)
  (and
   (tamep-functionp logarithm)
   (p07b6-log-operation-values-p
    carrier zero less exponential logarithm)))

(defun p07b6-r-powr
    (base exponent multiply exponential logarithm)
  (p07b6-unary
   exponential
   (p07b6-r-multiply
    multiply
    exponent
    (p07b6-unary logarithm base))))

(defun p07b6-bounds-at-n-p
    (n constant zero one add multiply negate inverse less
     exponential logarithm)
  (let* ((real-n (p07b6-r-nat n zero one add))
         (real-two (p07b6-r-nat 2 zero one add))
         (real-four (p07b6-r-nat 4 zero one add))
         (n-squared
          (p07b6-r-multiply multiply real-n real-n))
         (half-n-squared
          (p07b6-r-divide
           multiply inverse n-squared real-two))
         (constant-times-n
          (p07b6-r-multiply multiply constant real-n))
         (lower-exponent
          (p07b6-r-subtract
           add negate half-n-squared constant-times-n))
         (upper-exponent
          (p07b6-r-add add half-n-squared constant-times-n))
         (negative-quarter-n-squared
          (p07b6-r-divide
           multiply
           inverse
           (p07b6-r-negate negate n-squared)
           real-four))
         (decay
          (p07b6-unary exponential negative-quarter-n-squared))
         (lower-bound
          (p07b6-r-multiply
           multiply
           (p07b6-r-powr
            real-n lower-exponent
            multiply exponential logarithm)
           decay))
         (upper-bound
          (p07b6-r-multiply
           multiply
           (p07b6-r-powr
            real-n upper-exponent
            multiply exponential logarithm)
           decay))
         (real-count
          (p07b6-r-nat (p07b6-f n) zero one add)))
    (and
     (not (p07b6-binary less real-count lower-bound))
     (not (p07b6-binary less upper-bound real-count)))))

(defun-sk p07b6-bounds-for-all-n-p
    (constant zero one add multiply negate inverse less
     exponential logarithm)
  (forall (n)
    (implies
     (and (natp n) (<= 2 n))
     (p07b6-bounds-at-n-p
      n constant zero one add multiply negate inverse less
      exponential logarithm))))

(defun-sk p07b6-bound-constant-exists-p
    (carrier zero one add multiply negate inverse less
     exponential logarithm)
  (exists (constant)
    (and
     (p07b6-member-p carrier constant)
     (p07b6-bounds-for-all-n-p
      constant zero one add multiply negate inverse less
      exponential logarithm))))

(defun putnambench-putnam-2007-b6-statement
    (carrier zero one add multiply negate inverse less
     exponential logarithm)
  (implies
   (and
    (p07b6-real-field-p
     carrier zero one add multiply negate inverse less)
    (p07b6-exp-operation-p
     carrier zero one add multiply negate inverse less
     exponential)
    (p07b6-log-operation-p
     carrier zero less exponential logarithm))
   (p07b6-bound-constant-exists-p
    carrier zero one add multiply negate inverse less
    exponential logarithm)))

(value-triple :itpeval-statement-checked)
:q
