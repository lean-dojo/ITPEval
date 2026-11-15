;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_a2:
;; the infinite series with kth term
;; 6^k/((3^(k+1)-2^(k+1))*(3^k-2^k)), starting at k=1, sums to
;; the rational number 2. This file contains no proof.

(in-package "ACL2")

(defun putnam-1984-a2-series-term (k)
  (if (posp k)
      (/ (expt 6 k)
         (* (- (expt 3 (+ k 1))
               (expt 2 (+ k 1)))
            (- (expt 3 k)
               (expt 2 k))))
    0))

;; This is the exact rational sum over 1 <= k <= TERMS. The Rocq source
;; starts at k=0, where its totalized real division makes the extra term zero.
(defun putnam-1984-a2-series-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (putnam-1984-a2-series-prefix (- terms 1))
       (putnam-1984-a2-series-term terms))))

(defun putnam-1984-a2-solution ()
  2)

;; Positive rational tolerances are cofinal among positive real tolerances,
;; so this is the epsilon definition of the source infinite-series equality.
(defun-sk putnam-1984-a2-tail-p (epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (< (abs
         (- (putnam-1984-a2-series-prefix terms)
            (putnam-1984-a2-solution)))
        epsilon))))

(defun-sk putnam-1984-a2-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1984-a2-tail-p epsilon cutoff))))

(defun putnambench-putnam-1984-a2-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1984-a2-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
