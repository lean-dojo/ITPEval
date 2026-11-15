;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_a5:
;; existence of a positive real alpha such that floor(alpha^n)-n is even for
;; every positive natural number n. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The arguments of the final predicate present a Dedekind-complete ordered
;; field, hence a copy of the real field. Operations and carrier membership are
;; represented by the repository's tame APPLY$ function objects, while every
;; source quantifier, including the existential quantifier over alpha, remains
;; inside DEFUN-SK predicates.

(defun putnam-1983-a5-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun putnam-1983-a5-unary (operation value)
  (apply$ operation (list value)))

(defun putnam-1983-a5-binary (operation left right)
  (apply$ operation (list left right)))

(defun-sk putnam-1983-a5-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1983-a5-member-p carrier x)
      (putnam-1983-a5-member-p carrier y)
      (putnam-1983-a5-member-p carrier z))
     (let* ((xy-add
             (putnam-1983-a5-binary add x y))
            (yz-add
             (putnam-1983-a5-binary add y z))
            (xy-multiply
             (putnam-1983-a5-binary multiply x y))
            (yz-multiply
             (putnam-1983-a5-binary multiply y z))
            (negative-x
             (putnam-1983-a5-unary negate x))
            (inverse-x
             (putnam-1983-a5-unary inverse x)))
       (and
        (putnam-1983-a5-member-p carrier xy-add)
        (putnam-1983-a5-member-p carrier xy-multiply)
        (putnam-1983-a5-member-p carrier negative-x)
        (putnam-1983-a5-member-p carrier inverse-x)
        (equal
         (putnam-1983-a5-binary add xy-add z)
         (putnam-1983-a5-binary add x yz-add))
        (equal
         xy-add
         (putnam-1983-a5-binary add y x))
        (equal
         (putnam-1983-a5-binary add x zero)
         x)
        (equal
         (putnam-1983-a5-binary add x negative-x)
         zero)
        (equal
         (putnam-1983-a5-binary multiply xy-multiply z)
         (putnam-1983-a5-binary multiply x yz-multiply))
        (equal
         xy-multiply
         (putnam-1983-a5-binary multiply y x))
        (equal
         (putnam-1983-a5-binary multiply x one)
         x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1983-a5-binary multiply x inverse-x)
          one))
        (equal
         (putnam-1983-a5-binary multiply x yz-add)
         (putnam-1983-a5-binary
          add
          (putnam-1983-a5-binary multiply x y)
          (putnam-1983-a5-binary multiply x z))))))))

(defun-sk putnam-1983-a5-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1983-a5-member-p carrier x)
      (putnam-1983-a5-member-p carrier y)
      (putnam-1983-a5-member-p carrier z))
     (and
      (not (putnam-1983-a5-binary less x x))
      (or
       (equal x y)
       (putnam-1983-a5-binary less x y)
       (putnam-1983-a5-binary less y x))
      (implies
       (and
        (putnam-1983-a5-binary less x y)
        (putnam-1983-a5-binary less y z))
       (putnam-1983-a5-binary less x z))
      (implies
       (putnam-1983-a5-binary less x y)
       (putnam-1983-a5-binary
        less
        (putnam-1983-a5-binary add x z)
        (putnam-1983-a5-binary add y z)))
      (implies
       (and
        (putnam-1983-a5-binary less zero x)
        (putnam-1983-a5-binary less zero y))
       (putnam-1983-a5-binary
        less
        zero
        (putnam-1983-a5-binary multiply x y)))))))

(defun-sk putnam-1983-a5-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1983-a5-member-p carrier x))))

(defun-sk putnam-1983-a5-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1983-a5-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1983-a5-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1983-a5-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1983-a5-binary less bound x)))))

(defun-sk putnam-1983-a5-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1983-a5-member-p carrier bound)
     (putnam-1983-a5-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1983-a5-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1983-a5-member-p carrier supremum)
     (putnam-1983-a5-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1983-a5-member-p carrier bound)
       (putnam-1983-a5-upper-bound-p
        carrier less set bound))
      (not
       (putnam-1983-a5-binary
        less bound supremum))))))

(defun-sk putnam-1983-a5-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1983-a5-least-upper-bound-p
     carrier less set supremum)))

(defun-sk putnam-1983-a5-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1983-a5-valid-set-p carrier set)
      (putnam-1983-a5-set-nonempty-p carrier set)
      (putnam-1983-a5-bounded-above-p
       carrier less set))
     (putnam-1983-a5-has-supremum-p
      carrier less set))))

(defun putnam-1983-a5-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1983-a5-member-p carrier zero)
   (putnam-1983-a5-member-p carrier one)
   (not (equal zero one))
   (putnam-1983-a5-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1983-a5-order-laws-p
    carrier zero add multiply less)
   (putnam-1983-a5-binary less zero one)
   (putnam-1983-a5-dedekind-complete-p
    carrier less)))

(defun putnam-1983-a5-natural-value
    (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1983-a5-binary
     add
     one
     (putnam-1983-a5-natural-value
      (1- n) zero one add))))

(defun putnam-1983-a5-integer-value
    (integer zero one add negate)
  (if (and (integerp integer)
           (< integer 0))
      (putnam-1983-a5-unary
       negate
       (putnam-1983-a5-natural-value
        (- integer) zero one add))
    (putnam-1983-a5-natural-value
     (nfix integer) zero one add)))

(defun putnam-1983-a5-power
    (base exponent one multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1983-a5-binary
     multiply
     base
     (putnam-1983-a5-power
      base (1- exponent) one multiply))))

(defun putnam-1983-a5-less-equal-p (less left right)
  (not (putnam-1983-a5-binary less right left)))

;; K is floor(X) exactly when the embedded integer K is at most X and X is
;; strictly below the embedded integer K+1.
(defun putnam-1983-a5-floor-value-p
    (x k zero one add negate less)
  (and
   (integerp k)
   (let ((embedded-k
          (putnam-1983-a5-integer-value
           k zero one add negate))
         (embedded-successor
          (putnam-1983-a5-integer-value
           (+ k 1) zero one add negate)))
     (and
      (putnam-1983-a5-less-equal-p
       less embedded-k x)
      (putnam-1983-a5-binary
       less x embedded-successor)))))

(defun-sk putnam-1983-a5-floor-parity-at-n-p
    (alpha n zero one add multiply negate less)
  (exists (k)
    (and
     (putnam-1983-a5-floor-value-p
      (putnam-1983-a5-power alpha n one multiply)
      k zero one add negate less)
     (equal (mod (- k n) 2) 0))))

(defun-sk putnam-1983-a5-alpha-property-p
    (alpha zero one add multiply negate less)
  (forall (n)
    (implies
     (and
      (natp n)
      (< 0 n))
     (putnam-1983-a5-floor-parity-at-n-p
      alpha n zero one add multiply negate less))))

(defun-sk putnam-1983-a5-exists-alpha-p
    (carrier zero one add multiply negate less)
  (exists (alpha)
    (and
     (putnam-1983-a5-member-p carrier alpha)
     (putnam-1983-a5-binary less zero alpha)
     (putnam-1983-a5-alpha-property-p
      alpha zero one add multiply negate less))))

;; The structural antecedent is ACL2's untyped presentation of the source's
;; fixed real-number type. For every such presentation, the conclusion is
;; exactly the source existential statement, with no witness exposed as an
;; external parameter and no formula for its floors assumed.
(defun putnambench-putnam-1983-a5-statement
    (carrier zero one add multiply negate inverse less)
  (implies
   (putnam-1983-a5-real-field-p
    carrier zero one add multiply negate inverse less)
   (putnam-1983-a5-exists-alpha-p
    carrier zero one add multiply negate less)))

(value-triple :itpeval-statement-checked)
:q
