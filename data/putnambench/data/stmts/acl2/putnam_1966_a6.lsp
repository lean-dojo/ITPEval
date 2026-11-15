;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1966_a6: convergence to 3 of the finite nested-radical sequence
;; determined by a(n,n)=n and a(n,m)=m*sqrt(1+a(n,m+1)).
;; This file contains no proof.

(in-package "ACL2")

;; The source recurrence uniquely determines a(n,m) whenever
;; 1 <= m <= n, so a(n,1) can be eliminated definitionally.  If X(n,m)
;; denotes that value and R is rational, then positivity makes
;;
;;   X(n,m) < R
;;
;; equivalent, for m<n and R>0, to
;;
;;   X(n,m+1) < R^2/m^2 - 1.
;;
;; Repeating this equivalence reaches X(n,n)=n.  Thus this predicate compares
;; the actual real nested radical with a rational bound without representing
;; the radical by a rational approximation.
(defun putnam-1966-a6-value-less-than-bound-p
    (m remaining bound)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (< m bound)
    (and
     (posp m)
     (< 0 bound)
     (putnam-1966-a6-value-less-than-bound-p
      (+ m 1)
      (- remaining 1)
      (- (/ (* bound bound) (* m m)) 1)))))

;; This is the converse strict comparison R < X(n,m), reduced by the same
;; reversible squaring.  A nonpositive bound is automatically below the
;; positive nested radical.
(defun putnam-1966-a6-bound-less-than-value-p
    (m remaining bound)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (< bound m)
    (if (not (posp m))
        nil
      (if (<= bound 0)
          t
        (putnam-1966-a6-bound-less-than-value-p
         (+ m 1)
         (- remaining 1)
         (- (/ (* bound bound) (* m m)) 1))))))

(defun putnam-1966-a6-within-epsilon-p (n epsilon)
  (and
   (natp n)
   (<= 1 n)
   (putnam-1966-a6-bound-less-than-value-p
    1 (- n 1) (- 3 epsilon))
   (putnam-1966-a6-value-less-than-bound-p
    1 (- n 1) (+ 3 epsilon))))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; The three DEFUN-SK predicates preserve the source limit's quantifier order:
;; for every positive tolerance there exists a positive natural cutoff, and
;; every natural index at or above that cutoff lies in the exact interval.
(defun-sk putnam-1966-a6-tail-within-epsilon-p
    (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (putnam-1966-a6-within-epsilon-p n epsilon))))

(defun-sk putnam-1966-a6-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1966-a6-tail-within-epsilon-p
      epsilon cutoff))))

(defun-sk putnambench-putnam-1966-a6-statement ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1966-a6-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
