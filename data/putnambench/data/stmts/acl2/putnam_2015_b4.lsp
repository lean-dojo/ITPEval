;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_b4:
;; the sum of 2^a/(3^b*5^c) over positive integer triangle side triples has
;; reduced rational value 17/21. This file contains no proof.

(in-package "ACL2")

(defun putnam-2015-b4-triangle-term (a b c)
  (if (and (posp a)
           (posp b)
           (posp c)
           (< a (+ b c))
           (< b (+ c a))
           (< c (+ a b)))
      (/ (expt 2 a)
         (* (expt 3 b)
            (expt 5 c)))
    0))

(defun putnam-2015-b4-sum-c (a b c)
  (declare (xargs :measure (nfix c)))
  (if (zp c)
      0
    (+ (putnam-2015-b4-triangle-term a b c)
       (putnam-2015-b4-sum-c a b (- c 1)))))

(defun putnam-2015-b4-sum-b (a b maximum)
  (declare (xargs :measure (nfix b)))
  (if (zp b)
      0
    (+ (putnam-2015-b4-sum-c a b maximum)
       (putnam-2015-b4-sum-b a (- b 1) maximum))))

(defun putnam-2015-b4-sum-a (a maximum)
  (declare (xargs :measure (nfix a)))
  (if (zp a)
      0
    (+ (putnam-2015-b4-sum-b a maximum maximum)
       (putnam-2015-b4-sum-a (- a 1) maximum))))

;; This is the exact rational sum over 1 <= a,b,c < n, matching the cubic
;; partial sums used by the Rocq source and a cofinal family of finite subsets
;; for the nonnegative infinite sums in the Lean and Isabelle sources.
(defun putnam-2015-b4-partial-sum (n)
  (if (and (natp n)
           (< 0 n))
      (putnam-2015-b4-sum-a (- n 1) (- n 1))
    0))

(defun-sk putnam-2015-b4-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (<
      (abs
       (- (putnam-2015-b4-partial-sum n)
          (/ 17 21)))
      epsilon))))

(defun-sk putnam-2015-b4-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2015-b4-tail-p epsilon cutoff))))

;; Positive rational tolerances are cofinal among positive real tolerances.
(defun-sk putnambench-putnam-2015-b4-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2015-b4-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
