;; Statement-only formalization of PutnamBench artifact putnam_1963_b2:
;; the numbers 2^m*3^n, for integer m and n, are dense in the positive
;; real numbers. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols present an arbitrary Archimedean ordered
;; field. Every such field has a unique order-preserving embedding into the
;; reals, and every 2^m*3^n belongs to its prime field. Hence density in the
;; reals implies the formula below in every presented field by pulling the
;; rational witness back through that embedding. Conversely, specializing
;; the presented field to the reals gives the source statement. Thus this
;; Archimedean-field formulation and the source real-density statement imply
;; each other.
;;
;; The epsilon formula is definitionally the metric characterization of
;; x belonging to the closure of {2^m*3^n}. Both x and epsilon range over the
;; full field carrier, while m and n remain unbounded internal integer
;; witnesses. The structural premise is satisfiable (the rational field is
;; one model) and does not assume any part of the density conclusion.

(defstub p1963b2-scalar-p (x) t)
(defstub p1963b2-add-op (x y) t)
(defstub p1963b2-multiply-op (x y) t)
(defstub p1963b2-negate-op (x) t)
(defstub p1963b2-inverse-op (x) t)
(defstub p1963b2-less-op (x y) t)

(defun p1963b2-add (x y)
  (p1963b2-add-op x y))

(defun p1963b2-multiply (x y)
  (p1963b2-multiply-op x y))

(defun p1963b2-negate (x)
  (p1963b2-negate-op x))

(defun p1963b2-inverse (x)
  (p1963b2-inverse-op x))

(defun p1963b2-subtract (x y)
  (p1963b2-add x (p1963b2-negate y)))

(defun p1963b2-less (x y)
  (if (p1963b2-less-op x y) t nil))

(defun p1963b2-absolute-value (x zero)
  (if (p1963b2-less x zero)
      (p1963b2-negate x)
    x))

(defun-sk p1963b2-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1963b2-scalar-p x)
      (p1963b2-scalar-p y)
      (p1963b2-scalar-p z))
     (and
      (p1963b2-scalar-p (p1963b2-add x y))
      (p1963b2-scalar-p (p1963b2-multiply x y))
      (p1963b2-scalar-p (p1963b2-negate x))
      (implies
       (not (equal x zero))
       (p1963b2-scalar-p (p1963b2-inverse x)))
      (equal
       (p1963b2-add (p1963b2-add x y) z)
       (p1963b2-add x (p1963b2-add y z)))
      (equal
       (p1963b2-add x y)
       (p1963b2-add y x))
      (equal (p1963b2-add x zero) x)
      (equal
       (p1963b2-add x (p1963b2-negate x))
       zero)
      (equal
       (p1963b2-multiply
        (p1963b2-multiply x y) z)
       (p1963b2-multiply
        x (p1963b2-multiply y z)))
      (equal
       (p1963b2-multiply x y)
       (p1963b2-multiply y x))
      (equal (p1963b2-multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p1963b2-multiply
         x (p1963b2-inverse x))
        one))
      (equal
       (p1963b2-multiply x (p1963b2-add y z))
       (p1963b2-add
        (p1963b2-multiply x y)
        (p1963b2-multiply x z)))))))

(defun-sk p1963b2-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1963b2-scalar-p x)
      (p1963b2-scalar-p y)
      (p1963b2-scalar-p z))
     (and
      (not (p1963b2-less x x))
      (or
       (equal x y)
       (p1963b2-less x y)
       (p1963b2-less y x))
      (implies
       (and
        (p1963b2-less x y)
        (p1963b2-less y z))
       (p1963b2-less x z))
      (implies
       (p1963b2-less x y)
       (p1963b2-less
        (p1963b2-add x z)
        (p1963b2-add y z)))
      (implies
       (and
        (p1963b2-less zero x)
        (p1963b2-less zero y))
       (p1963b2-less
        zero (p1963b2-multiply x y)))))))

(defun p1963b2-natural-cast (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1963b2-add
     one
     (p1963b2-natural-cast (- n 1) zero one))))

(defun-sk p1963b2-archimedean-bound-exists-p
    (x zero one)
  (exists (n)
    (and
     (natp n)
     (p1963b2-less
      x (p1963b2-natural-cast n zero one)))))

(defun-sk p1963b2-archimedean-p (zero one)
  (forall (x)
    (implies
     (p1963b2-scalar-p x)
     (p1963b2-archimedean-bound-exists-p
      x zero one))))

(defun p1963b2-archimedean-ordered-field-p
    (zero one)
  (and
   (p1963b2-scalar-p zero)
   (p1963b2-scalar-p one)
   (not (equal zero one))
   (p1963b2-less zero one)
   (p1963b2-field-laws-p zero one)
   (p1963b2-order-laws-p zero)
   (p1963b2-archimedean-p zero one)))

(defun p1963b2-two (one)
  (p1963b2-add one one))

(defun p1963b2-three (one)
  (p1963b2-add (p1963b2-two one) one))

(defun p1963b2-natural-power (base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p1963b2-multiply
     base
     (p1963b2-natural-power
      base (- exponent 1) one))))

(defun p1963b2-integer-power (base exponent one)
  (if (< exponent 0)
      (p1963b2-inverse
       (p1963b2-natural-power
        base (- exponent) one))
    (p1963b2-natural-power base exponent one)))

(defun p1963b2-group-element (m n one)
  (p1963b2-multiply
   (p1963b2-integer-power
    (p1963b2-two one) m one)
   (p1963b2-integer-power
    (p1963b2-three one) n one)))

(defun-sk p1963b2-nearby-group-element-exists-p
    (x epsilon zero one)
  (exists (m n)
    (and
     (integerp m)
     (integerp n)
     (p1963b2-less
      (p1963b2-absolute-value
       (p1963b2-subtract
        (p1963b2-group-element m n one)
        x)
       zero)
      epsilon))))

(defun-sk p1963b2-positive-field-in-closure-p
    (zero one)
  (forall (x epsilon)
    (implies
     (and
      (p1963b2-scalar-p x)
      (p1963b2-less zero x)
      (p1963b2-scalar-p epsilon)
      (p1963b2-less zero epsilon))
     (p1963b2-nearby-group-element-exists-p
      x epsilon zero one))))

(defun putnambench-putnam-1963-b2-statement
    (zero one)
  (implies
   (p1963b2-archimedean-ordered-field-p zero one)
   (p1963b2-positive-field-in-closure-p zero one)))

(value-triple :itpeval-statement-checked)
:q
