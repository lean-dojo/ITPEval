;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_a5:
;; differentiable real functions satisfying a positive-coefficient linear
;; differential system and tending to zero at positive infinity are linearly
;; dependent. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar parameters describe a Dedekind-complete ordered field, hence a
;; presentation of the real field. The derivative and limit predicates below
;; are their epsilon-delta definitions. Tame APPLY$ function objects represent
;; the arbitrary trajectories, coefficient matrices, and dependence vectors.

(defun putnam-1995-a5-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun putnam-1995-a5-unary (operation value)
  (apply$ operation (list value)))

(defun putnam-1995-a5-binary (operation left right)
  (apply$ operation (list left right)))

(defun-sk putnam-1995-a5-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1995-a5-member-p carrier x)
      (putnam-1995-a5-member-p carrier y)
      (putnam-1995-a5-member-p carrier z))
     (let* ((xy-add
             (putnam-1995-a5-binary add x y))
            (yz-add
             (putnam-1995-a5-binary add y z))
            (xy-multiply
             (putnam-1995-a5-binary multiply x y))
            (yz-multiply
             (putnam-1995-a5-binary multiply y z))
            (negative-x
             (putnam-1995-a5-unary negate x))
            (inverse-x
             (putnam-1995-a5-unary inverse x)))
       (and
        (putnam-1995-a5-member-p carrier xy-add)
        (putnam-1995-a5-member-p carrier xy-multiply)
        (putnam-1995-a5-member-p carrier negative-x)
        (putnam-1995-a5-member-p carrier inverse-x)
        (equal
         (putnam-1995-a5-binary add xy-add z)
         (putnam-1995-a5-binary add x yz-add))
        (equal xy-add
               (putnam-1995-a5-binary add y x))
        (equal
         (putnam-1995-a5-binary add x zero)
         x)
        (equal
         (putnam-1995-a5-binary add x negative-x)
         zero)
        (equal
         (putnam-1995-a5-binary multiply xy-multiply z)
         (putnam-1995-a5-binary multiply x yz-multiply))
        (equal
         xy-multiply
         (putnam-1995-a5-binary multiply y x))
        (equal
         (putnam-1995-a5-binary multiply x one)
         x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1995-a5-binary multiply x inverse-x)
          one))
        (equal
         (putnam-1995-a5-binary multiply x yz-add)
         (putnam-1995-a5-binary
          add
          (putnam-1995-a5-binary multiply x y)
          (putnam-1995-a5-binary multiply x z))))))))

(defun-sk putnam-1995-a5-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1995-a5-member-p carrier x)
      (putnam-1995-a5-member-p carrier y)
      (putnam-1995-a5-member-p carrier z))
     (and
      (not (putnam-1995-a5-binary less x x))
      (or
       (equal x y)
       (putnam-1995-a5-binary less x y)
       (putnam-1995-a5-binary less y x))
      (implies
       (and
        (putnam-1995-a5-binary less x y)
        (putnam-1995-a5-binary less y z))
       (putnam-1995-a5-binary less x z))
      (implies
       (putnam-1995-a5-binary less x y)
       (putnam-1995-a5-binary
        less
        (putnam-1995-a5-binary add x z)
        (putnam-1995-a5-binary add y z)))
      (implies
       (and
        (putnam-1995-a5-binary less zero x)
        (putnam-1995-a5-binary less zero y))
       (putnam-1995-a5-binary
        less
        zero
        (putnam-1995-a5-binary multiply x y)))))))

(defun-sk putnam-1995-a5-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1995-a5-member-p carrier x))))

(defun-sk putnam-1995-a5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1995-a5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1995-a5-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1995-a5-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1995-a5-binary less bound x)))))

(defun-sk putnam-1995-a5-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1995-a5-member-p carrier bound)
     (putnam-1995-a5-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1995-a5-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1995-a5-member-p carrier supremum)
     (putnam-1995-a5-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1995-a5-member-p carrier bound)
       (putnam-1995-a5-upper-bound-p
        carrier less set bound))
      (not
       (putnam-1995-a5-binary
        less bound supremum))))))

(defun-sk putnam-1995-a5-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1995-a5-least-upper-bound-p
     carrier less set supremum)))

(defun-sk putnam-1995-a5-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1995-a5-valid-set-p carrier set)
      (putnam-1995-a5-set-nonempty-p carrier set)
      (putnam-1995-a5-bounded-above-p
       carrier less set))
     (putnam-1995-a5-has-supremum-p
      carrier less set))))

(defun putnam-1995-a5-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1995-a5-member-p carrier zero)
   (putnam-1995-a5-member-p carrier one)
   (not (equal zero one))
   (putnam-1995-a5-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1995-a5-order-laws-p
    carrier zero add multiply less)
   (putnam-1995-a5-binary less zero one)
   (putnam-1995-a5-dedekind-complete-p
    carrier less)))

(defun putnam-1995-a5-r-add (add left right)
  (putnam-1995-a5-binary add left right))

(defun putnam-1995-a5-r-multiply (multiply left right)
  (putnam-1995-a5-binary multiply left right))

(defun putnam-1995-a5-r-negate (negate value)
  (putnam-1995-a5-unary negate value))

(defun putnam-1995-a5-r-subtract (add negate left right)
  (putnam-1995-a5-r-add
   add left (putnam-1995-a5-r-negate negate right)))

(defun putnam-1995-a5-r-less-p (less left right)
  (if (putnam-1995-a5-binary less left right) t nil))

(defun putnam-1995-a5-r-less-equal-p (less left right)
  (not (putnam-1995-a5-r-less-p less right left)))

(defun putnam-1995-a5-r-absolute-value
    (zero negate less value)
  (if (putnam-1995-a5-r-less-p less value zero)
      (putnam-1995-a5-r-negate negate value)
    value))

(defun putnam-1995-a5-positive-real-p
    (carrier zero less value)
  (and
   (putnam-1995-a5-member-p carrier value)
   (putnam-1995-a5-r-less-p less zero value)))

(defun putnam-1995-a5-index-p (n index)
  (and
   (natp index)
   (< index n)))

(defun putnam-1995-a5-x-value (trajectory index time)
  (apply$ trajectory (list index time)))

(defun putnam-1995-a5-a-value
    (coefficients row column)
  (apply$ coefficients (list row column)))

(defun putnam-1995-a5-b-value
    (dependence-vector index)
  (apply$ dependence-vector (list index)))

(defun-sk putnam-1995-a5-trajectory-typed-p
    (carrier n trajectory)
  (forall (index time)
    (implies
     (and
      (putnam-1995-a5-index-p n index)
      (putnam-1995-a5-member-p carrier time))
     (putnam-1995-a5-member-p
      carrier
      (putnam-1995-a5-x-value
       trajectory index time)))))

(defun-sk putnam-1995-a5-coefficients-typed-p
    (carrier n coefficients)
  (forall (row column)
    (implies
     (and
      (putnam-1995-a5-index-p n row)
      (putnam-1995-a5-index-p n column))
     (putnam-1995-a5-member-p
      carrier
      (putnam-1995-a5-a-value
       coefficients row column)))))

(defun-sk putnam-1995-a5-positive-coefficients-p
    (zero less n coefficients)
  (forall (row column)
    (implies
     (and
      (putnam-1995-a5-index-p n row)
      (putnam-1995-a5-index-p n column))
     (putnam-1995-a5-r-less-p
      less
      zero
      (putnam-1995-a5-a-value
       coefficients row column)))))

(defun putnam-1995-a5-system-sum
    (zero add multiply coefficients trajectory
     row time column count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1995-a5-r-add
     add
     (putnam-1995-a5-r-multiply
      multiply
      (putnam-1995-a5-a-value
       coefficients row column)
      (putnam-1995-a5-x-value
       trajectory column time))
     (putnam-1995-a5-system-sum
      zero add multiply coefficients trajectory
      row time (+ 1 column) (- count 1)))))

;; The error form
;; |x(y)-x(t)-d*(y-t)| <= epsilon*|y-t|
;; is equivalent to the usual one-variable derivative definition.

(defun-sk putnam-1995-a5-derivative-neighborhood-p
    (carrier zero add multiply negate less
     trajectory index point derivative epsilon radius)
  (forall (nearby)
    (implies
     (and
      (putnam-1995-a5-member-p carrier nearby)
      (putnam-1995-a5-r-less-p
       less
       (putnam-1995-a5-r-absolute-value
        zero
        negate
        less
        (putnam-1995-a5-r-subtract
         add negate nearby point))
       radius))
     (putnam-1995-a5-r-less-equal-p
      less
      (putnam-1995-a5-r-absolute-value
       zero
       negate
       less
       (putnam-1995-a5-r-subtract
        add
        negate
        (putnam-1995-a5-r-subtract
         add
         negate
         (putnam-1995-a5-x-value
          trajectory index nearby)
         (putnam-1995-a5-x-value
          trajectory index point))
        (putnam-1995-a5-r-multiply
         multiply
         derivative
         (putnam-1995-a5-r-subtract
          add negate nearby point))))
      (putnam-1995-a5-r-multiply
       multiply
       epsilon
       (putnam-1995-a5-r-absolute-value
        zero
        negate
        less
        (putnam-1995-a5-r-subtract
         add negate nearby point)))))))

(defun-sk putnam-1995-a5-derivative-radius-exists-p
    (carrier zero add multiply negate less
     trajectory index point derivative epsilon)
  (exists (radius)
    (and
     (putnam-1995-a5-positive-real-p
      carrier zero less radius)
     (putnam-1995-a5-derivative-neighborhood-p
      carrier zero add multiply negate less
      trajectory index point derivative epsilon radius))))

(defun-sk putnam-1995-a5-has-derivative-at-p
    (carrier zero add multiply negate less
     trajectory index point derivative)
  (forall (epsilon)
    (implies
     (putnam-1995-a5-positive-real-p
      carrier zero less epsilon)
     (and
      (putnam-1995-a5-member-p carrier point)
      (putnam-1995-a5-member-p carrier derivative)
      (putnam-1995-a5-derivative-radius-exists-p
       carrier zero add multiply negate less
       trajectory index point derivative epsilon)))))

(defun-sk putnam-1995-a5-satisfies-system-p
    (carrier zero add multiply negate less
     n trajectory coefficients)
  (forall (index time)
    (implies
     (and
      (putnam-1995-a5-index-p n index)
      (putnam-1995-a5-member-p carrier time))
     (putnam-1995-a5-has-derivative-at-p
      carrier zero add multiply negate less
      trajectory
      index
      time
      (putnam-1995-a5-system-sum
       zero add multiply coefficients trajectory
       index time 0 n)))))

(defun-sk putnam-1995-a5-limit-tail-p
    (carrier zero add negate less
     trajectory index epsilon threshold)
  (forall (time)
    (implies
     (and
      (putnam-1995-a5-member-p carrier time)
      (putnam-1995-a5-r-less-equal-p
       less threshold time))
     (putnam-1995-a5-r-less-p
      less
      (putnam-1995-a5-r-absolute-value
       zero
       negate
       less
       (putnam-1995-a5-r-subtract
        add
        negate
        (putnam-1995-a5-x-value
         trajectory index time)
        zero))
      epsilon))))

(defun-sk putnam-1995-a5-limit-threshold-exists-p
    (carrier zero add negate less
     trajectory index epsilon)
  (exists (threshold)
    (and
     (putnam-1995-a5-member-p carrier threshold)
     (putnam-1995-a5-limit-tail-p
      carrier zero add negate less
      trajectory index epsilon threshold))))

(defun-sk putnam-1995-a5-tends-to-zero-p
    (carrier zero add negate less n trajectory)
  (forall (index epsilon)
    (implies
     (and
      (putnam-1995-a5-index-p n index)
      (putnam-1995-a5-positive-real-p
       carrier zero less epsilon))
     (putnam-1995-a5-limit-threshold-exists-p
      carrier zero add negate less
      trajectory index epsilon))))

(defun-sk putnam-1995-a5-dependence-vector-typed-p
    (carrier n dependence-vector)
  (forall (index)
    (implies
     (putnam-1995-a5-index-p n index)
     (putnam-1995-a5-member-p
      carrier
      (putnam-1995-a5-b-value
       dependence-vector index)))))

(defun putnam-1995-a5-linear-combination-sum
    (zero add multiply dependence-vector trajectory
     time index count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (putnam-1995-a5-r-add
     add
     (putnam-1995-a5-r-multiply
      multiply
      (putnam-1995-a5-b-value
       dependence-vector index)
      (putnam-1995-a5-x-value
       trajectory index time))
     (putnam-1995-a5-linear-combination-sum
      zero add multiply dependence-vector trajectory
      time (+ 1 index) (- count 1)))))

(defun-sk putnam-1995-a5-linear-combination-zero-p
    (carrier zero add multiply n
     dependence-vector trajectory)
  (forall (time)
    (implies
     (putnam-1995-a5-member-p carrier time)
     (equal
      (putnam-1995-a5-linear-combination-sum
       zero add multiply dependence-vector trajectory
       time 0 n)
      zero))))

(defun-sk putnam-1995-a5-dependence-vector-nonzero-p
    (zero n dependence-vector)
  (exists (index)
    (and
     (putnam-1995-a5-index-p n index)
     (not
      (equal
       (putnam-1995-a5-b-value
        dependence-vector index)
       zero)))))

(defun-sk putnam-1995-a5-linearly-dependent-p
    (carrier zero add multiply n trajectory)
  (exists (dependence-vector)
    (and
     (tamep-functionp dependence-vector)
     (putnam-1995-a5-dependence-vector-typed-p
      carrier n dependence-vector)
     (putnam-1995-a5-linear-combination-zero-p
      carrier zero add multiply n
      dependence-vector trajectory)
     (putnam-1995-a5-dependence-vector-nonzero-p
      zero n dependence-vector))))

(defun-sk putnam-1995-a5-all-systems-p
    (carrier zero add multiply negate less)
  (forall (n trajectory coefficients)
    (implies
     (and
      (natp n)
      (< 0 n)
      (tamep-functionp trajectory)
      (tamep-functionp coefficients)
      (putnam-1995-a5-trajectory-typed-p
       carrier n trajectory)
      (putnam-1995-a5-coefficients-typed-p
       carrier n coefficients)
      (putnam-1995-a5-positive-coefficients-p
       zero less n coefficients)
      (putnam-1995-a5-satisfies-system-p
       carrier zero add multiply negate less
       n trajectory coefficients)
      (putnam-1995-a5-tends-to-zero-p
       carrier zero add negate less n trajectory))
     (putnam-1995-a5-linearly-dependent-p
      carrier zero add multiply n trajectory))))

(defun putnambench-putnam-1995-a5-statement
    (carrier zero one add multiply negate inverse less)
  (implies
   (putnam-1995-a5-real-field-p
    carrier zero one add multiply negate inverse less)
   (putnam-1995-a5-all-systems-p
    carrier zero add multiply negate less)))

(value-triple :itpeval-statement-checked)
:q
