;; Statement-only formalization of PutnamBench corpus artifact putnam_1970_b5:
;; a real function is continuous exactly when every natural-number clamp
;; composed with it is continuous. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols present an arbitrary scalar function on an
;; Archimedean linearly ordered additive group. This is the exact structure
;; used by the statement; neither completeness nor an APPLY$ function-object
;; encoding is needed.

(defstub p1970b5-scalar-p (x) t)
(defstub p1970b5-add (x y) t)
(defstub p1970b5-negate (x) t)
(defstub p1970b5-less (x y) t)
(defstub p1970b5-function (x) t)
(defstub p1970b5-archimedean-bound (x) t)

(defun p1970b5-member-p (x)
  (if (p1970b5-scalar-p x) t nil))

(defun p1970b5-less-p (x y)
  (if (p1970b5-less x y) t nil))

(defun p1970b5-less-equal-p (x y)
  (not (p1970b5-less-p y x)))

(defun p1970b5-subtract (x y)
  (p1970b5-add x (p1970b5-negate y)))

(defun p1970b5-absolute-value (zero x)
  (if (p1970b5-less-p x zero)
      (p1970b5-negate x)
    x))

(defun p1970b5-distance (zero x y)
  (p1970b5-absolute-value
   zero
   (p1970b5-subtract x y)))

(defun p1970b5-positive-p (zero x)
  (and
   (p1970b5-member-p x)
   (p1970b5-less-p zero x)))

(defun-sk p1970b5-additive-group-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1970b5-member-p x)
      (p1970b5-member-p y)
      (p1970b5-member-p z))
     (and
      (p1970b5-member-p (p1970b5-add x y))
      (p1970b5-member-p (p1970b5-negate x))
      (equal
       (p1970b5-add (p1970b5-add x y) z)
       (p1970b5-add x (p1970b5-add y z)))
      (equal
       (p1970b5-add x y)
       (p1970b5-add y x))
      (equal
       (p1970b5-add x zero)
       x)
      (equal
       (p1970b5-add x (p1970b5-negate x))
       zero)))))

(defun-sk p1970b5-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p1970b5-member-p x)
      (p1970b5-member-p y)
      (p1970b5-member-p z))
     (and
      (not (p1970b5-less-p x x))
      (or
       (equal x y)
       (p1970b5-less-p x y)
       (p1970b5-less-p y x))
      (implies
       (and
        (p1970b5-less-p x y)
        (p1970b5-less-p y z))
       (p1970b5-less-p x z))
      (implies
       (p1970b5-less-p x y)
       (p1970b5-less-p
        (p1970b5-add x z)
        (p1970b5-add y z)))))))

(defun p1970b5-natural-value (zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1970b5-add
     one
     (p1970b5-natural-value zero one (- n 1)))))

(defun-sk p1970b5-archimedean-law-p (zero one)
  (forall (x)
    (implies
     (p1970b5-member-p x)
     (and
      (natp (p1970b5-archimedean-bound x))
      (p1970b5-less-p
       x
       (p1970b5-natural-value
        zero one
        (p1970b5-archimedean-bound x)))))))

(defun p1970b5-archimedean-ordered-group-p (zero one)
  (and
   (p1970b5-member-p zero)
   (p1970b5-member-p one)
   (not (equal zero one))
   (p1970b5-additive-group-laws-p zero)
   (p1970b5-order-laws-p)
   (p1970b5-less-p zero one)
   (p1970b5-archimedean-law-p zero one)))

(defun-sk p1970b5-function-typed-p ()
  (forall (x)
    (implies
     (p1970b5-member-p x)
     (p1970b5-member-p
      (p1970b5-function x)))))

(defun p1970b5-ramp-value (zero one n x)
  (let* ((bound
          (p1970b5-natural-value zero one n))
         (negative-bound
          (p1970b5-negate bound)))
    (if (p1970b5-less-equal-p x negative-bound)
        negative-bound
      (if (p1970b5-less-equal-p x bound)
          x
        bound))))

(defun p1970b5-observed-value (kind zero one n x)
  (if (equal kind :source)
      (p1970b5-function x)
    (p1970b5-ramp-value
     zero one n
     (p1970b5-function x))))

(defun-sk p1970b5-continuity-neighborhood-p
    (kind zero one n x epsilon delta)
  (forall (y)
    (implies
     (and
      (p1970b5-member-p y)
      (p1970b5-less-p
       (p1970b5-distance zero y x)
       delta))
     (p1970b5-less-p
      (p1970b5-distance
       zero
       (p1970b5-observed-value
        kind zero one n y)
       (p1970b5-observed-value
        kind zero one n x))
      epsilon))))

(defun-sk p1970b5-continuity-radius-exists-p
    (kind zero one n x epsilon)
  (exists (delta)
    (and
     (p1970b5-positive-p zero delta)
     (p1970b5-continuity-neighborhood-p
      kind zero one n x epsilon delta))))

(defun-sk p1970b5-continuous-p
    (kind zero one n)
  (forall (x epsilon)
    (implies
     (and
      (p1970b5-member-p x)
      (p1970b5-positive-p zero epsilon))
     (p1970b5-continuity-radius-exists-p
      kind zero one n x epsilon))))

(defun-sk p1970b5-all-ramp-compositions-continuous-p
    (zero one)
  (forall (n)
    (implies
     (natp n)
     (p1970b5-continuous-p
      :ramp zero one n))))

(defun putnambench-putnam-1970-b5-statement
    (zero one)
  (implies
   (and
    (p1970b5-archimedean-ordered-group-p
     zero one)
    (p1970b5-function-typed-p))
   (iff
    (p1970b5-continuous-p
     :source zero one 0)
    (p1970b5-all-ramp-compositions-continuous-p
     zero one))))

(value-triple :itpeval-statement-checked)
:q
