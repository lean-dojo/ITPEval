;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_b1:
;; the infinite product of (n^3-1)/(n^3+1) from n=2 converges to 2/3.
;; This file contains no proof.

(in-package "ACL2")

;; For natural N, this is exactly the product over 2 <= n <= N.  It is 1
;; when N < 2, matching the empty-product convention in the source statements.
(defun putnam-1977-b1-product-prefix (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (< n 2))
      1
    (* (putnam-1977-b1-product-prefix (- n 1))
       (/ (- (expt n 3) 1)
          (+ (expt n 3) 1)))))

(defun putnam-1977-b1-solution ()
  (/ 2 3))

;; Positive rational tolerances are cofinal among positive real tolerances.
;; Natural prefix indices are cofinal in Lean's integer indices, so this is
;; the epsilon definition of the same limit without adding a convergence rate.
(defun-sk putnam-1977-b1-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (< (abs
         (- (putnam-1977-b1-product-prefix n)
            (putnam-1977-b1-solution)))
        epsilon))))

(defun-sk putnam-1977-b1-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-1977-b1-tail-p epsilon cutoff))))

(defun putnambench-putnam-1977-b1-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1977-b1-cutoff-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
