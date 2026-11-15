;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_a5:
;; the coprime-residue power sum modulo 2021 is divisible by 2021 exactly
;; when its natural exponent is divisible by neither 42 nor 46. This file
;; contains no proof.

(in-package "ACL2")

(defun putnam-2021-a5-gcd (a b)
  (declare (xargs :measure (+ (nfix a) (nfix b))))
  (if (and (natp a) (natp b))
      (cond
       ((zp a) b)
       ((zp b) a)
       ((< a b)
        (putnam-2021-a5-gcd a (- b a)))
       (t
        (putnam-2021-a5-gcd (- a b) b)))
    0))

;; This recursively enumerates exactly the natural numbers n with
;; 1 <= n <= 2021 and gcd(n,2021)=1. The endpoint 2021 contributes nothing,
;; so it also agrees with the ordinal enumeration 0,...,2020 in the Rocq
;; source.
(defun putnam-2021-a5-power-sum-through (j upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+ (putnam-2021-a5-power-sum-through j (- upper 1))
       (if (equal (putnam-2021-a5-gcd upper 2021) 1)
           (expt upper j)
         0))))

(defun putnam-2021-a5-solution-member-p (j)
  (and
   (natp j)
   (not (equal (mod j 42) 0))
   (not (equal (mod j 46) 0))))

;; The source assumptions uniquely determine A and S, so both are
;; definitionally eliminated by the exact finite sum above. Equality of the
;; two Boolean predicates is the source biconditional.
(defun putnambench-putnam-2021-a5-statement (j)
  (implies
   (natp j)
   (equal
    (equal
     (mod (putnam-2021-a5-power-sum-through j 2021)
          2021)
     0)
    (putnam-2021-a5-solution-member-p j))))

(value-triple :itpeval-statement-checked)
:q
