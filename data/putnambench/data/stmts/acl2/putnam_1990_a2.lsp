;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_a2:
;; existence of a sequence of differences of nonnegative integer cube roots
;; converging to the real number sqrt(2). This file contains no proof.

(in-package "ACL2")

;; A real number lies in the closure of the set of cube-root differences
;; exactly when every positive rational epsilon contains such a difference.
;; From a convergent source sequence this follows by taking a sufficiently
;; late term. Conversely, choosing a term within 1/(k+1) for each k gives the
;; source sequence. Thus this closure formulation preserves the source's
;; internal existential sequence without exposing it as a statement argument.
;;
;; The existential witness consists of n, m, a positive rational precision,
;; and rational lower brackets for cube-root(n), cube-root(m), and sqrt(2).
;; Each root lies within 1/precision of its bracket. Monotonicity of square
;; and cube on the nonnegative reals then bounds the combined error by
;; 3/precision.
(defun putnam-1990-a2-approximation-witness-p
    (epsilon n m precision n-root m-root two-root)
  (let* ((delta (/ precision))
         (n-root-upper (+ n-root delta))
         (m-root-upper (+ m-root delta))
         (two-root-upper (+ two-root delta)))
    (and
     (natp n)
     (natp m)
     (posp precision)
     (rationalp n-root)
     (<= 0 n-root)
     (rationalp m-root)
     (<= 0 m-root)
     (rationalp two-root)
     (<= 0 two-root)
     (<= (expt n-root 3) n)
     (< n (expt n-root-upper 3))
     (<= (expt m-root 3) m)
     (< m (expt m-root-upper 3))
     (<= (expt two-root 2) 2)
     (< 2 (expt two-root-upper 2))
     (< (+ (abs (- (- n-root m-root) two-root))
           (* 3 delta))
        epsilon))))

;; DEFUN-SK supplies the source-level existential witnesses internally; the
;; statement predicate exposes only the universally quantified tolerance.
(defun-sk putnam-1990-a2-approximation-exists-p (epsilon)
  (exists (n m precision n-root m-root two-root)
    (putnam-1990-a2-approximation-witness-p
     epsilon n m precision n-root m-root two-root)))

(defun putnambench-putnam-1990-a2-statement (epsilon)
  (implies
   (and (rationalp epsilon)
        (< 0 epsilon))
   (putnam-1990-a2-approximation-exists-p epsilon)))

(value-triple :itpeval-statement-checked)
:q
