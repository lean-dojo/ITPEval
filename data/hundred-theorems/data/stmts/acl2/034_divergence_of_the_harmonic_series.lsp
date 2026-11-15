;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__034, "Divergence of the Harmonic Series": the
;; positive-integer reciprocal partial sums 1 + 1/2 + ... + 1/n grow without
;; bound. Exact rational partial sums encode the real claim. This file contains
;; no proof.

(in-package "ACL2")

(defun hundred-theorems-034-harmonic-prefix (terms)
  (if (zp terms)
      0
    (+ (hundred-theorems-034-harmonic-prefix (- terms 1))
       (/ 1 terms))))

;; Quantifier order for the final predicate:
;;   for every rational bound, there exists a natural cutoff; every natural
;;   term count at least that cutoff has a harmonic prefix at least the bound.
(defun-sk hundred-theorems-034-harmonic-tail-above-bound-p
    (bound cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= cutoff terms))
     (<= bound
         (hundred-theorems-034-harmonic-prefix terms)))))

(defun-sk hundred-theorems-034-harmonic-cutoff-exists-p (bound)
  (exists (cutoff)
    (and
     (natp cutoff)
     (hundred-theorems-034-harmonic-tail-above-bound-p
      bound cutoff))))

(defun-sk hundred-theorems-034-divergence-of-the-harmonic-series-statement ()
  (forall (bound)
    (implies
     (rationalp bound)
     (hundred-theorems-034-harmonic-cutoff-exists-p bound))))

(value-triple :itpeval-statement-checked)
:q
