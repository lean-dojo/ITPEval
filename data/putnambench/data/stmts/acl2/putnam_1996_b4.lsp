;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_b4:
;; no real 2 by 2 matrix has matrix sine, defined by its exact power series,
;; equal to the matrix with rows (1, 1996) and (0, 1). This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The arguments of the final predicate present a Dedekind-complete ordered
;; field, hence a copy of the real field. Tame APPLY$ objects retain arbitrary
;; carrier elements and subsets, while DEFUN-SK supplies unbounded first-order
;; quantification. A 2 by 2 matrix is represented by its four entries.

(defun putnam-1996-b4-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun putnam-1996-b4-unary (operation value)
  (apply$ operation (list value)))

(defun putnam-1996-b4-binary (operation left right)
  (apply$ operation (list left right)))

(defun-sk putnam-1996-b4-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (putnam-1996-b4-member-p carrier x)
      (putnam-1996-b4-member-p carrier y)
      (putnam-1996-b4-member-p carrier z))
     (let* ((xy-add
             (putnam-1996-b4-binary add x y))
            (yz-add
             (putnam-1996-b4-binary add y z))
            (xy-multiply
             (putnam-1996-b4-binary multiply x y))
            (yz-multiply
             (putnam-1996-b4-binary multiply y z))
            (negative-x
             (putnam-1996-b4-unary negate x))
            (inverse-x
             (putnam-1996-b4-unary inverse x)))
       (and
        (putnam-1996-b4-member-p carrier xy-add)
        (putnam-1996-b4-member-p carrier xy-multiply)
        (putnam-1996-b4-member-p carrier negative-x)
        (putnam-1996-b4-member-p carrier inverse-x)
        (equal
         (putnam-1996-b4-binary add xy-add z)
         (putnam-1996-b4-binary add x yz-add))
        (equal xy-add
               (putnam-1996-b4-binary add y x))
        (equal
         (putnam-1996-b4-binary add x zero)
         x)
        (equal
         (putnam-1996-b4-binary add x negative-x)
         zero)
        (equal
         (putnam-1996-b4-binary multiply xy-multiply z)
         (putnam-1996-b4-binary multiply x yz-multiply))
        (equal
         xy-multiply
         (putnam-1996-b4-binary multiply y x))
        (equal
         (putnam-1996-b4-binary multiply x one)
         x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1996-b4-binary multiply x inverse-x)
          one))
        (equal
         (putnam-1996-b4-binary multiply x yz-add)
         (putnam-1996-b4-binary
          add
          (putnam-1996-b4-binary multiply x y)
          (putnam-1996-b4-binary multiply x z))))))))

(defun-sk putnam-1996-b4-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (putnam-1996-b4-member-p carrier x)
      (putnam-1996-b4-member-p carrier y)
      (putnam-1996-b4-member-p carrier z))
     (and
      (not (putnam-1996-b4-binary less x x))
      (or
       (equal x y)
       (putnam-1996-b4-binary less x y)
       (putnam-1996-b4-binary less y x))
      (implies
       (and
        (putnam-1996-b4-binary less x y)
        (putnam-1996-b4-binary less y z))
       (putnam-1996-b4-binary less x z))
      (implies
       (putnam-1996-b4-binary less x y)
       (putnam-1996-b4-binary
        less
        (putnam-1996-b4-binary add x z)
        (putnam-1996-b4-binary add y z)))
      (implies
       (and
        (putnam-1996-b4-binary less zero x)
        (putnam-1996-b4-binary less zero y))
       (putnam-1996-b4-binary
        less
        zero
        (putnam-1996-b4-binary multiply x y)))))))

(defun-sk putnam-1996-b4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (putnam-1996-b4-member-p carrier x))))

(defun-sk putnam-1996-b4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (putnam-1996-b4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk putnam-1996-b4-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (putnam-1996-b4-member-p carrier x)
      (apply$ set (list x)))
     (not
      (putnam-1996-b4-binary less bound x)))))

(defun-sk putnam-1996-b4-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (putnam-1996-b4-member-p carrier bound)
     (putnam-1996-b4-upper-bound-p
      carrier less set bound))))

(defun-sk putnam-1996-b4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (putnam-1996-b4-member-p carrier supremum)
     (putnam-1996-b4-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (putnam-1996-b4-member-p carrier bound)
       (putnam-1996-b4-upper-bound-p
        carrier less set bound))
      (not
       (putnam-1996-b4-binary
        less bound supremum))))))

(defun-sk putnam-1996-b4-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (putnam-1996-b4-least-upper-bound-p
     carrier less set supremum)))

(defun-sk putnam-1996-b4-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1996-b4-valid-set-p carrier set)
      (putnam-1996-b4-set-nonempty-p carrier set)
      (putnam-1996-b4-bounded-above-p
       carrier less set))
     (putnam-1996-b4-has-supremum-p
      carrier less set))))

(defun putnam-1996-b4-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (putnam-1996-b4-member-p carrier zero)
   (putnam-1996-b4-member-p carrier one)
   (not (equal zero one))
   (putnam-1996-b4-field-laws-p
    carrier zero one add multiply negate inverse)
   (putnam-1996-b4-order-laws-p
    carrier zero add multiply less)
   (putnam-1996-b4-binary less zero one)
   (putnam-1996-b4-dedekind-complete-p
    carrier less)))

(defun putnam-1996-b4-r-add (add left right)
  (putnam-1996-b4-binary add left right))

(defun putnam-1996-b4-r-multiply (multiply left right)
  (putnam-1996-b4-binary multiply left right))

(defun putnam-1996-b4-r-negate (negate value)
  (putnam-1996-b4-unary negate value))

(defun putnam-1996-b4-r-absolute-value
    (zero negate less value)
  (if (putnam-1996-b4-binary less value zero)
      (putnam-1996-b4-r-negate negate value)
    value))

(defun putnam-1996-b4-r-nat (n zero one add)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (putnam-1996-b4-r-add
     add
     one
     (putnam-1996-b4-r-nat
      (1- n) zero one add))))

(defun putnam-1996-b4-r-factorial
    (n zero one add multiply)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (putnam-1996-b4-r-multiply
     multiply
     (putnam-1996-b4-r-nat n zero one add)
     (putnam-1996-b4-r-factorial
      (1- n) zero one add multiply))))

(defun putnam-1996-b4-matrix-p (carrier matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) 4)
   (putnam-1996-b4-member-p carrier (nth 0 matrix))
   (putnam-1996-b4-member-p carrier (nth 1 matrix))
   (putnam-1996-b4-member-p carrier (nth 2 matrix))
   (putnam-1996-b4-member-p carrier (nth 3 matrix))))

(defun putnam-1996-b4-matrix-add (add left right)
  (list
   (putnam-1996-b4-r-add
    add (nth 0 left) (nth 0 right))
   (putnam-1996-b4-r-add
    add (nth 1 left) (nth 1 right))
   (putnam-1996-b4-r-add
    add (nth 2 left) (nth 2 right))
   (putnam-1996-b4-r-add
    add (nth 3 left) (nth 3 right))))

(defun putnam-1996-b4-matrix-scale
    (multiply scalar matrix)
  (list
   (putnam-1996-b4-r-multiply
    multiply scalar (nth 0 matrix))
   (putnam-1996-b4-r-multiply
    multiply scalar (nth 1 matrix))
   (putnam-1996-b4-r-multiply
    multiply scalar (nth 2 matrix))
   (putnam-1996-b4-r-multiply
    multiply scalar (nth 3 matrix))))

(defun putnam-1996-b4-matrix-multiply
    (add multiply left right)
  (list
   (putnam-1996-b4-r-add
    add
    (putnam-1996-b4-r-multiply
     multiply (nth 0 left) (nth 0 right))
    (putnam-1996-b4-r-multiply
     multiply (nth 1 left) (nth 2 right)))
   (putnam-1996-b4-r-add
    add
    (putnam-1996-b4-r-multiply
     multiply (nth 0 left) (nth 1 right))
    (putnam-1996-b4-r-multiply
     multiply (nth 1 left) (nth 3 right)))
   (putnam-1996-b4-r-add
    add
    (putnam-1996-b4-r-multiply
     multiply (nth 2 left) (nth 0 right))
    (putnam-1996-b4-r-multiply
     multiply (nth 3 left) (nth 2 right)))
   (putnam-1996-b4-r-add
    add
    (putnam-1996-b4-r-multiply
     multiply (nth 2 left) (nth 1 right))
    (putnam-1996-b4-r-multiply
     multiply (nth 3 left) (nth 3 right)))))

(defun putnam-1996-b4-matrix-power
    (matrix exponent zero one add multiply)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list one zero zero one)
    (putnam-1996-b4-matrix-multiply
     add
     multiply
     matrix
     (putnam-1996-b4-matrix-power
      matrix (1- exponent) zero one add multiply))))

(defun putnam-1996-b4-sine-term
    (index matrix zero one add multiply negate inverse)
  (let* ((exponent (+ (* 2 index) 1))
         (denominator
          (putnam-1996-b4-r-factorial
           exponent zero one add multiply))
         (sign
          (if (equal (mod index 2) 0)
              one
            (putnam-1996-b4-r-negate negate one)))
         (coefficient
          (putnam-1996-b4-r-multiply
           multiply
           sign
           (putnam-1996-b4-unary inverse denominator))))
    (putnam-1996-b4-matrix-scale
     multiply
     coefficient
     (putnam-1996-b4-matrix-power
      matrix exponent zero one add multiply))))

(defun putnam-1996-b4-sine-prefix
    (terms matrix zero one add multiply negate inverse)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (list zero zero zero zero)
    (let ((index (1- terms)))
      (putnam-1996-b4-matrix-add
       add
       (putnam-1996-b4-sine-prefix
        index matrix zero one add multiply negate inverse)
       (putnam-1996-b4-sine-term
        index matrix zero one add multiply negate inverse)))))

(defun-sk putnam-1996-b4-sine-entry-tail-p
    (zero one add multiply negate inverse less
     matrix entry limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (putnam-1996-b4-binary
      less
      (putnam-1996-b4-r-absolute-value
       zero
       negate
       less
       (putnam-1996-b4-r-add
        add
        (nth
         entry
         (putnam-1996-b4-sine-prefix
          terms matrix zero one add multiply negate inverse))
        (putnam-1996-b4-r-negate negate limit)))
      epsilon))))

(defun-sk putnam-1996-b4-sine-entry-cutoff-exists-p
    (zero one add multiply negate inverse less
     matrix entry limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1996-b4-sine-entry-tail-p
      zero one add multiply negate inverse less
      matrix entry limit epsilon cutoff))))

(defun-sk putnam-1996-b4-sine-entry-converges-p
    (carrier zero one add multiply negate inverse less
     matrix entry limit)
  (forall (epsilon)
    (implies
     (and
      (putnam-1996-b4-member-p carrier epsilon)
      (putnam-1996-b4-binary less zero epsilon))
     (putnam-1996-b4-sine-entry-cutoff-exists-p
      zero one add multiply negate inverse less
      matrix entry limit epsilon))))

(defun-sk putnam-1996-b4-counterexample-p
    (carrier zero one add multiply negate inverse less)
  (exists (matrix)
    (and
     (putnam-1996-b4-matrix-p carrier matrix)
     (putnam-1996-b4-sine-entry-converges-p
      carrier zero one add multiply negate inverse less
      matrix 0 one)
     (putnam-1996-b4-sine-entry-converges-p
      carrier zero one add multiply negate inverse less
      matrix
      1
      (putnam-1996-b4-r-nat 1996 zero one add))
     (putnam-1996-b4-sine-entry-converges-p
      carrier zero one add multiply negate inverse less
      matrix 2 zero)
     (putnam-1996-b4-sine-entry-converges-p
      carrier zero one add multiply negate inverse less
      matrix 3 one))))

(defun putnam-1996-b4-statement
    (carrier zero one add multiply negate inverse less)
  (implies
   (putnam-1996-b4-real-field-p
    carrier zero one add multiply negate inverse less)
   (not
    (putnam-1996-b4-counterexample-p
     carrier zero one add multiply negate inverse less))))

(value-triple :itpeval-statement-checked)
:q
