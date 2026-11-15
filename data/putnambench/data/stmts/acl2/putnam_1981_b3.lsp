;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_b3:
;; the natural numbers n for which every prime divisor of n^2+3 already
;; divides k^2+3 for some natural k with k^2<n are unbounded. This file
;; contains no proof.

(in-package "ACL2")

(defun putnam-1981-b3-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1981-b3-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1981-b3-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1981-b3-no-divisor-through-p
    p (- p 1))))

;; The witness k remains an internal existentially quantified natural.
(defun-sk putnam-1981-b3-small-witness-exists-p (p m)
  (exists (k)
    (and
     (natp k)
     (< (* k k) m)
     (equal
      (mod (+ (* k k) 3) p)
      0))))

;; This is the source predicate P, expanded definitionally. Quantifying over
;; all ACL2 objects with the prime predicate in the antecedent is exactly
;; quantification over natural primes.
(defun-sk putnam-1981-b3-qualifying-p (m)
  (forall (p)
    (implies
     (and
      (putnam-1981-b3-prime-p p)
      (equal
       (mod (+ (* m m) 3) p)
       0))
     (putnam-1981-b3-small-witness-exists-p
      p m))))

;; The source conclusion is genuinely unbounded: for each natural n, the
;; witness m is existentially quantified with no prescribed upper bound.
(defun-sk putnam-1981-b3-larger-qualifying-exists-p (n)
  (exists (m)
    (and
     (natp m)
     (< n m)
     (putnam-1981-b3-qualifying-p m))))

(defun-sk putnambench-putnam-1981-b3-statement ()
  (forall (n)
    (implies
     (natp n)
     (putnam-1981-b3-larger-qualifying-exists-p
      n))))

(value-triple :itpeval-statement-checked)
:q
