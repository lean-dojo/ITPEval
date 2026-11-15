;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_b6:
;; infinitely many integer affine maps preserve triangular-number membership
;; on every positive integer in both directions. This file contains no proof.

(in-package "ACL2")

;; For a nonnegative integer z, any nonnegative m satisfying
;; 2*z=m*(m+1) has m<=z unless z=0, when m=0. Thus this finite search is
;; exactly the source existential definition of triangular numbers.
(defun putnam-1988-b6-triangular-through-p (z candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (integerp z)
           (<= 0 z)
           (natp candidate))
      (or
       (equal (* 2 z)
              (* candidate (+ candidate 1)))
       (and
        (not (zp candidate))
        (putnam-1988-b6-triangular-through-p
         z (- candidate 1))))
    nil))

(defun putnam-1988-b6-triangular-p (z)
  (and
   (integerp z)
   (<= 0 z)
   (putnam-1988-b6-triangular-through-p z (nfix z))))

;; This predicate retains the source's arbitrary integer pair and unbounded
;; universal quantifier over all positive integer inputs.
(defun-sk putnam-1988-b6-preserves-triangular-p (a b)
  (forall (input)
    (implies
     (and
      (integerp input)
      (< 0 input))
     (equal
      (putnam-1988-b6-triangular-p
       (+ (* a input) b))
      (putnam-1988-b6-triangular-p input)))))

(defun putnam-1988-b6-qualifying-pair-p (a b)
  (and
   (integerp a)
   (integerp b)
   (putnam-1988-b6-preserves-triangular-p a b)))

;; A subset of Z x Z is infinite exactly when its values of |a|+|b| are
;; unbounded, since every such bounded set of integer pairs is finite.
;; DEFUN-SK keeps the qualifying pair existentially quantified inside the
;; statement rather than exposing a chosen solution family.
(defun-sk putnam-1988-b6-pair-above-bound-exists-p (bound)
  (exists (a b)
    (and
     (putnam-1988-b6-qualifying-pair-p a b)
     (< bound (+ (abs a) (abs b))))))

(defun putnambench-putnam-1988-b6-statement (bound)
  (implies
   (natp bound)
   (putnam-1988-b6-pair-above-bound-exists-p bound)))

(value-triple :itpeval-statement-checked)
:q
