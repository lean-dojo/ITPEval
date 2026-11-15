;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_b1:
;; the positive integers with a unique base-10 over-expansion using digits
;; from 0 through 10 are exactly those whose ordinary decimal expansion has
;; no zero digit. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Write an over-expansion least-significant digit first. A valid expansion of
;; positive N is either the one-term list (N), possible exactly for N<=10, or
;; D followed by a valid expansion of M>0, where N=D+10*M and 0<=D<=10.
;; If R=N mod 10 and Q=floor(N/10), the latter case has D=R and M=Q, plus
;; the disjoint alternative D=10 and M=Q-1 exactly when R=0 and Q>1.
;; Consequently this recursion counts every source digit list exactly once.
;; The fuel N+1 exceeds the depth of every recursive quotient branch, so it
;; only supplies an ACL2 termination measure and does not bound the domain.

(defun putnam-2014-b1-overexpansion-count-aux (fuel n)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel)
          (not (natp n))
          (zp n))
      0
    (let* ((quotient (floor n 10))
           (remainder (mod n 10))
           (one-term-count
            (if (<= n 10) 1 0))
           (ordinary-low-digit-count
            (if (< 0 quotient)
                (putnam-2014-b1-overexpansion-count-aux
                 (- fuel 1) quotient)
              0))
           (digit-ten-count
            (if (and (equal remainder 0)
                     (< 1 quotient))
                (putnam-2014-b1-overexpansion-count-aux
                 (- fuel 1) (- quotient 1))
              0)))
      (+ one-term-count
         ordinary-low-digit-count
         digit-ten-count))))

(defun putnam-2014-b1-overexpansion-count (n)
  (if (natp n)
      (putnam-2014-b1-overexpansion-count-aux
       (+ n 1) n)
    0))

(defun putnam-2014-b1-no-zero-decimal-digits-aux (fuel n)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel)
          (zp n))
      t
    (and
     (not (equal (mod n 10) 0))
     (putnam-2014-b1-no-zero-decimal-digits-aux
      (- fuel 1) (floor n 10)))))

(defun putnam-2014-b1-no-zero-decimal-digits-p (n)
  (and
   (natp n)
   (< 0 n)
   (putnam-2014-b1-no-zero-decimal-digits-aux
    (+ n 1) n)))

;; The source hypothesis defines S pointwise as the positive naturals having
;; exactly one over-expansion, while the annotated solution defines membership
;; as positivity with no zero decimal digit. Universal closure over N makes
;; this Boolean equivalence exactly their extensional set equality.

(defun putnambench-putnam-2014-b1-statement (n)
  (implies
   (natp n)
   (equal
    (and
     (< 0 n)
     (equal
      (putnam-2014-b1-overexpansion-count n)
      1))
    (putnam-2014-b1-no-zero-decimal-digits-p n))))

(value-triple :itpeval-statement-checked)
:q
