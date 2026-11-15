;; Statement-only formalization of PutnamBench corpus artifact putnam_1963_b6:
;; arbitrary nonempty subsets of real Euclidean spaces of dimensions one
;; through three stabilize after two iterations of adjoining every closed
;; segment between current points. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no first-class function space, so conservative generic symbols
;; represent the real scalar operations and the arbitrary sequence of set
;; membership predicates. The ordered-field laws used by real affine
;; geometry are explicit hypotheses of the statement. Points are genuine
;; d-tuples of scalars, while P63B6-A-MEMBER-P remains an arbitrary predicate;
;; no finite carrier, point enumeration, rational restriction, or external
;; segment witness is introduced.

(defstub p63b6-scalar-p (x) t)
(defstub p63b6-add (x y) t)
(defstub p63b6-multiply (x y) t)
(defstub p63b6-negate (x) t)
(defstub p63b6-inverse (x) t)
(defstub p63b6-less (x y) t)
(defstub p63b6-a-member (n point) t)

(defun p63b6-scalar-member-p (x)
  (if (p63b6-scalar-p x) t nil))

(defun p63b6-less-p (x y)
  (if (p63b6-less x y) t nil))

(defun p63b6-less-equal-p (x y)
  (or (equal x y)
      (p63b6-less-p x y)))

(defun p63b6-a-member-p (n point)
  (if (p63b6-a-member n point) t nil))

(defun-sk p63b6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p63b6-scalar-member-p x)
      (p63b6-scalar-member-p y)
      (p63b6-scalar-member-p z))
     (and
      (p63b6-scalar-member-p (p63b6-add x y))
      (p63b6-scalar-member-p (p63b6-multiply x y))
      (p63b6-scalar-member-p (p63b6-negate x))
      (p63b6-scalar-member-p (p63b6-inverse x))
      (equal
       (p63b6-add (p63b6-add x y) z)
       (p63b6-add x (p63b6-add y z)))
      (equal (p63b6-add x y)
             (p63b6-add y x))
      (equal (p63b6-add x zero) x)
      (equal (p63b6-add x (p63b6-negate x))
             zero)
      (equal
       (p63b6-multiply (p63b6-multiply x y) z)
       (p63b6-multiply x (p63b6-multiply y z)))
      (equal (p63b6-multiply x y)
             (p63b6-multiply y x))
      (equal (p63b6-multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p63b6-multiply x (p63b6-inverse x))
        one))
      (equal
       (p63b6-multiply x (p63b6-add y z))
       (p63b6-add
        (p63b6-multiply x y)
        (p63b6-multiply x z)))))))

(defun-sk p63b6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p63b6-scalar-member-p x)
      (p63b6-scalar-member-p y)
      (p63b6-scalar-member-p z))
     (and
      (not (p63b6-less-p x x))
      (or
       (equal x y)
       (p63b6-less-p x y)
       (p63b6-less-p y x))
      (implies
       (and
        (p63b6-less-p x y)
        (p63b6-less-p y z))
       (p63b6-less-p x z))
      (implies
       (p63b6-less-p x y)
       (p63b6-less-p
        (p63b6-add x z)
        (p63b6-add y z)))
      (implies
       (and
        (p63b6-less-p zero x)
        (p63b6-less-p zero y))
       (p63b6-less-p
        zero
        (p63b6-multiply x y)))))))

(defun p63b6-real-coordinate-context-p (zero one)
  (and
   (p63b6-scalar-member-p zero)
   (p63b6-scalar-member-p one)
   (not (equal zero one))
   (p63b6-field-laws-p zero one)
   (p63b6-order-laws-p zero)
   (p63b6-less-p zero one)))

(defun p63b6-point-p (point dimension)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      (equal point nil)
    (and
     (consp point)
     (p63b6-scalar-member-p (car point))
     (p63b6-point-p (cdr point) (- dimension 1)))))

(defun p63b6-affine-coordinate
    (one coefficient left right)
  (p63b6-add
   (p63b6-multiply
    (p63b6-add one (p63b6-negate coefficient))
    left)
   (p63b6-multiply coefficient right)))

(defun-sk p63b6-affine-point-p
    (dimension one point left right coefficient)
  (forall (coordinate)
    (implies
     (and
      (natp coordinate)
      (< coordinate dimension))
     (equal
      (nth coordinate point)
      (p63b6-affine-coordinate
       one
       coefficient
       (nth coordinate left)
       (nth coordinate right))))))

(defun-sk p63b6-segment-step-member-p
    (dimension zero one previous-index point)
  (exists (left right coefficient)
    (and
     (p63b6-point-p left dimension)
     (p63b6-point-p right dimension)
     (p63b6-a-member-p previous-index left)
     (p63b6-a-member-p previous-index right)
     (p63b6-scalar-member-p coefficient)
     (p63b6-less-equal-p zero coefficient)
     (p63b6-less-equal-p coefficient one)
     (p63b6-affine-point-p
      dimension one point left right coefficient))))

(defun-sk p63b6-set-sequence-typed-p (dimension)
  (forall (n point)
    (implies
     (and
      (natp n)
      (p63b6-a-member-p n point))
     (p63b6-point-p point dimension))))

(defun-sk p63b6-initial-set-nonempty-p (dimension)
  (exists (point)
    (and
     (p63b6-point-p point dimension)
     (p63b6-a-member-p 0 point))))

(defun-sk p63b6-recurrence-p (dimension zero one)
  (forall (n point)
    (implies
     (and
      (natp n)
      (< 0 n)
      (p63b6-point-p point dimension))
     (iff
      (p63b6-a-member-p n point)
      (p63b6-segment-step-member-p
       dimension zero one (- n 1) point)))))

(defun-sk p63b6-stabilizes-from-two-p (dimension)
  (forall (n point)
    (implies
     (and
      (natp n)
      (<= 2 n)
      (p63b6-point-p point dimension))
     (iff
      (p63b6-a-member-p n point)
      (p63b6-a-member-p (+ n 1) point)))))

(defun-sk putnambench-putnam-1963-b6-statement ()
  (forall (dimension zero one)
    (implies
     (and
      (natp dimension)
      (<= 1 dimension)
      (<= dimension 3)
      (p63b6-real-coordinate-context-p zero one)
      (p63b6-set-sequence-typed-p dimension)
      (p63b6-initial-set-nonempty-p dimension)
      (p63b6-recurrence-p dimension zero one))
     (p63b6-stabilizes-from-two-p dimension))))

(value-triple :itpeval-statement-checked)
:q
