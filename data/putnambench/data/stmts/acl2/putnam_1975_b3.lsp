;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_b3:
;; the supremum 1/k! of the normalized kth elementary symmetric sum over
;; positive finite real tuples. This file contains no proof.

(in-package "ACL2")

;; Lists encode finite multisets, since the elementary symmetric sum below is
;; invariant under permutation. Restricting their entries to positive
;; rationals is bidirectionally exact for this supremum statement. A strict
;; real counterexample to the upper bound persists under a sufficiently close
;; positive rational perturbation, while rational thresholds are cofinal below
;; 1/k!. Thus the rational universal and approximation clauses hold exactly
;; when their real counterparts do.

(defun putnam-1975-b3-positive-rational-list-p (values)
  (if (consp values)
      (and (rationalp (car values))
           (< 0 (car values))
           (putnam-1975-b3-positive-rational-list-p
            (cdr values)))
    (equal values nil)))

(defun putnam-1975-b3-tuple-p (k values)
  (and (natp k)
       (true-listp values)
       (<= k (len values))
       (putnam-1975-b3-positive-rational-list-p values)))

;; s_k(x :: xs) = s_k(xs) + x*s_(k-1)(xs), with s_0 = 1.
(defun putnam-1975-b3-esymm (k values)
  (declare (xargs :measure (len values)))
  (if (not (natp k))
      0
    (if (zp k)
        1
      (if (consp values)
          (+ (putnam-1975-b3-esymm k (cdr values))
             (* (car values)
                (putnam-1975-b3-esymm
                 (- k 1) (cdr values))))
        0))))

(defun putnam-1975-b3-factorial (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (* k (putnam-1975-b3-factorial (- k 1)))))

(defun putnam-1975-b3-solution (k)
  (if (natp k)
      (/ 1 (putnam-1975-b3-factorial k))
    0))

(defun putnam-1975-b3-ratio (k values)
  (/ (putnam-1975-b3-esymm k values)
     (expt (putnam-1975-b3-esymm 1 values) k)))

(defun-sk putnam-1975-b3-upper-bound-p (k)
  (forall (values)
    (implies
     (putnam-1975-b3-tuple-p k values)
     (<= (putnam-1975-b3-ratio k values)
         (putnam-1975-b3-solution k)))))

(defun-sk putnam-1975-b3-ratio-above-exists-p (k m)
  (exists (values)
    (and
     (putnam-1975-b3-tuple-p k values)
     (> (putnam-1975-b3-ratio k values) m))))

(defun-sk putnam-1975-b3-lower-approximation-p (k)
  (forall (m)
    (implies
     (and
      (rationalp m)
      (< m (putnam-1975-b3-solution k)))
     (putnam-1975-b3-ratio-above-exists-p k m))))

(defun putnambench-putnam-1975-b3-statement (k)
  (implies
   (and (natp k)
        (< 0 k))
   (and
    (putnam-1975-b3-upper-bound-p k)
    (putnam-1975-b3-lower-approximation-p k))))

(value-triple :itpeval-statement-checked)
:q
