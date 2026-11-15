;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_b5:
;; whether the exponential of the infinite real series formed from binary
;; digit counts is rational. This file contains no proof.

(in-package "ACL2")

;; For natural N, all nonzero binary digits have indices below N. This helper
;; sums those digits while recursing on the explicit digit count.
(defun putnam-1981-b5-binary-one-count-through (n digit-count)
  (declare (xargs :measure (nfix digit-count)))
  (if (zp digit-count)
      0
    (let ((index (- digit-count 1)))
      (+ (mod (floor n (expt 2 index)) 2)
         (putnam-1981-b5-binary-one-count-through
          n index)))))

;; The number B(N) of ones in the base-two expansion of N.
(defun putnam-1981-b5-binary-one-count (n)
  (putnam-1981-b5-binary-one-count-through n (nfix n)))

;; The exact rational partial sum
;;
;;   sum_(n=1)^terms B(n)/(n*(n+1)).
(defun putnam-1981-b5-series-prefix (terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (+ (putnam-1981-b5-series-prefix (- terms 1))
       (/ (putnam-1981-b5-binary-one-count terms)
          (* terms (+ terms 1))))))

(defun putnam-1981-b5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-1981-b5-factorial (- n 1)))))

;; The first TERMS terms of the defining power series for exp(X).
(defun putnam-1981-b5-exp-series-prefix (x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((index (- terms 1)))
      (+ (putnam-1981-b5-exp-series-prefix x index)
         (/ (expt x index)
            (putnam-1981-b5-factorial index))))))

;; The rational sequence obtained by applying increasingly long exponential
;; power-series prefixes to increasingly long source-series prefixes.
;; This diagonal sequence converges to
;;
;;   exp(sum_(n=1)^infinity B(n)/(n*(n+1))).
(defun putnam-1981-b5-exp-name-value (index)
  (putnam-1981-b5-exp-series-prefix
   (putnam-1981-b5-series-prefix (nfix index))
   (+ 1 (nfix index))))

(defun-sk putnam-1981-b5-exp-limit-tail-p
    (q epsilon cutoff)
  (forall (index)
    (implies
     (and (natp index)
          (<= cutoff index))
     (< (abs (- (putnam-1981-b5-exp-name-value index)
                q))
        epsilon))))

(defun-sk putnam-1981-b5-exp-limit-cutoff-exists-p
    (q epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (putnam-1981-b5-exp-limit-tail-p
          q epsilon cutoff))))

;; Equality of the represented real exponential with the rational Q.
(defun-sk putnam-1981-b5-exp-limit-p (q)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1981-b5-exp-limit-cutoff-exists-p
      q epsilon))))

;; The rational witness remains internal, as in the source existential.
(defun-sk putnam-1981-b5-exp-is-rational-p ()
  (exists (q)
    (and (rationalp q)
         (putnam-1981-b5-exp-limit-p q))))

(defun putnam-1981-b5-solution ()
  t)

;; The rational Cauchy name above denotes the same real exponential as the
;; source expression: rational partial sums name the source series, and the
;; exponential power series is continuous. Thus this is a definitional
;; Cauchy-name rendering of the source biconditional, not a rational-domain
;; restriction or a precomputed limit identity.
(defun putnambench-putnam-1981-b5-statement ()
  (iff (putnam-1981-b5-exp-is-rational-p)
       (putnam-1981-b5-solution)))

(value-triple :itpeval-statement-checked)
:q
