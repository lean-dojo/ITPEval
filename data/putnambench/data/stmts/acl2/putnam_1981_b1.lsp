;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_b1:
;; the normalized double sum of 5*h^4 - 18*h^2*k^2 + 5*k^4 over
;; 1 <= h,k <= n converges to -1. This file contains no proof.

(in-package "ACL2")

(defun putnam-1981-b1-row-sum (h k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      0
    (+ (- (+ (* 5 (expt h 4))
             (* 5 (expt k 4)))
          (* 18 (expt h 2) (expt k 2)))
       (putnam-1981-b1-row-sum h (- k 1)))))

(defun putnam-1981-b1-double-sum-aux (remaining n)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+ (putnam-1981-b1-row-sum remaining n)
       (putnam-1981-b1-double-sum-aux
        (- remaining 1) n))))

(defun putnam-1981-b1-double-sum (n)
  (if (natp n)
      (putnam-1981-b1-double-sum-aux n n)
    0))

(defun putnam-1981-b1-sequence (n)
  (if (posp n)
      (/ (putnam-1981-b1-double-sum n)
         (expt n 5))
    0))

(defun putnam-1981-b1-solution ()
  -1)

;; Positive rational tolerances are cofinal among positive real tolerances,
;; so this is the epsilon definition of the source real-sequence limit.
(defun-sk putnam-1981-b1-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (< (abs
         (- (putnam-1981-b1-sequence n)
            (putnam-1981-b1-solution)))
        epsilon))))

(defun-sk putnam-1981-b1-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1981-b1-tail-p epsilon cutoff))))

(defun putnambench-putnam-1981-b1-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1981-b1-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
