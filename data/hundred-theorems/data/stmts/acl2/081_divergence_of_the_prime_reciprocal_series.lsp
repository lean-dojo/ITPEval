;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__081, "Divergence of the Prime Reciprocal Series":
;; the exact rational sums of reciprocals of primes are eventually above every
;; rational bound. Monotonicity and rational cofinality make this equivalent
;; to divergence of the corresponding real series. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-081-has-divisor-at-most-p (n divisor)
  (if (or (not (natp n))
          (not (natp divisor))
          (< divisor 2))
      nil
    (or (equal (mod n divisor) 0)
        (hundred-theorems-081-has-divisor-at-most-p
         n
         (- divisor 1)))))

(defun hundred-theorems-081-prime-p (n)
  (and (natp n)
       (<= 2 n)
       (not
        (hundred-theorems-081-has-divisor-at-most-p
         n
         (- n 1)))))

(defun hundred-theorems-081-prime-reciprocal-prefix (terms)
  (if (zp terms)
      0
    (+ (hundred-theorems-081-prime-reciprocal-prefix
        (- terms 1))
       (if (hundred-theorems-081-prime-p terms)
           (/ 1 terms)
         0))))

;; Quantifier order for the final predicate:
;;   for every rational bound, there exists a natural cutoff; every natural
;;   term count at least that cutoff has prime-reciprocal prefix at least the
;;   bound.
(defun-sk hundred-theorems-081-eventually-above-bound-p
    (bound cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= cutoff terms))
     (<= bound
         (hundred-theorems-081-prime-reciprocal-prefix terms)))))

(defun-sk hundred-theorems-081-cutoff-exists-p (bound)
  (exists (cutoff)
    (and
     (natp cutoff)
     (hundred-theorems-081-eventually-above-bound-p
      bound cutoff))))

(defun-sk hundred-theorems-081-divergence-of-the-prime-reciprocal-series-statement
    ()
  (forall (bound)
    (implies
     (rationalp bound)
     (hundred-theorems-081-cutoff-exists-p bound))))

(value-triple :itpeval-statement-checked)
:q
