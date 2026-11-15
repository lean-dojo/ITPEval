;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_b6:
;; every positive strictly increasing real sequence with a_n/n tending to zero
;; has infinitely many strict midpoint-concavity indices. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; This conservative generic symbol supplies a rational regular Cauchy name
;; for a_n at every natural n.  It is an arbitrary function symbol, not an
;; APPLY$ code or a finite table.  Every real sequence admits such a name, and
;; every name satisfying PUTNAM-2001-B6-REGULAR-NAME-P determines a unique real
;; sequence, so this presentation is bidirectionally equivalent to quantifying
;; over all functions from the naturals to the reals.
;;
;; Strict inequalities are expressed by positive rational margins valid at
;; every precision.  The limit cutoff and the unbounded good-index witness are
;; existentially quantified inside DEFUN-SK predicates.  For each fixed n,
;; only finitely many midpoint gaps occur, so separate positive margins for
;; those gaps are equivalent to the source's strict inequalities.

(defstub putnam-2001-b6-a-approx (n epsilon) t)

(defun putnam-2001-b6-positive-rational-p (x)
  (and
   (rationalp x)
   (< 0 x)))

(defun-sk putnam-2001-b6-regular-name-p ()
  (forall (n epsilon eta)
    (implies
     (and
      (natp n)
      (putnam-2001-b6-positive-rational-p epsilon)
      (putnam-2001-b6-positive-rational-p eta))
     (let ((left
            (putnam-2001-b6-a-approx n epsilon))
           (right
            (putnam-2001-b6-a-approx n eta)))
       (and
        (rationalp left)
        (rationalp right)
        (<= (abs (- left right))
            (+ epsilon eta)))))))

;; MARGIN <= a_n, expressed through every regular-name approximation.

(defun-sk putnam-2001-b6-positive-margin-p (n margin)
  (forall (epsilon)
    (implies
     (putnam-2001-b6-positive-rational-p epsilon)
     (<=
      margin
      (+ (putnam-2001-b6-a-approx n epsilon)
         epsilon)))))

(defun-sk putnam-2001-b6-positive-value-p (n)
  (exists (margin)
    (and
     (putnam-2001-b6-positive-rational-p margin)
     (putnam-2001-b6-positive-margin-p n margin))))

;; MARGIN <= a_(n+1)-a_n.

(defun-sk putnam-2001-b6-increase-margin-p (n margin)
  (forall (epsilon)
    (implies
     (putnam-2001-b6-positive-rational-p epsilon)
     (<=
      margin
      (+
       (-
        (putnam-2001-b6-a-approx (+ n 1) epsilon)
        (putnam-2001-b6-a-approx n epsilon))
       (* 2 epsilon))))))

(defun-sk putnam-2001-b6-increase-positive-p (n)
  (exists (margin)
    (and
     (putnam-2001-b6-positive-rational-p margin)
     (putnam-2001-b6-increase-margin-p n margin))))

(defun-sk putnam-2001-b6-positive-increasing-p ()
  (forall (n)
    (implies
     (posp n)
     (and
      (putnam-2001-b6-positive-value-p n)
      (putnam-2001-b6-increase-positive-p n)))))

;; At name precision PRECISION*(n+1), division by n+1 introduces at most
;; PRECISION approximation error.  Requiring the exact quotient to be at most
;; EPSILON eventually, for every positive rational EPSILON, is equivalent
;; after rescaling EPSILON to convergence to zero.

(defun-sk putnam-2001-b6-limit-tail-p
    (epsilon cutoff)
  (forall (n precision)
    (implies
     (and
      (natp n)
      (<= cutoff n)
      (putnam-2001-b6-positive-rational-p precision))
     (let* ((denominator (+ n 1))
            (name-precision (* precision denominator))
            (sample
             (putnam-2001-b6-a-approx
              denominator name-precision)))
       (and
        (rationalp sample)
        (<=
         (abs (/ sample denominator))
         (+ epsilon precision)))))))

(defun-sk putnam-2001-b6-limit-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2001-b6-limit-tail-p
      epsilon cutoff))))

(defun-sk putnam-2001-b6-limit-zero-p ()
  (forall (epsilon)
    (implies
     (putnam-2001-b6-positive-rational-p epsilon)
     (putnam-2001-b6-limit-cutoff-exists-p
      epsilon))))

;; MARGIN <= 2*a_n-a_(n-i)-a_(n+i).

(defun-sk putnam-2001-b6-midpoint-margin-p
    (n i margin)
  (forall (epsilon)
    (implies
     (putnam-2001-b6-positive-rational-p epsilon)
     (<=
      margin
      (+
       (-
        (-
         (* 2
            (putnam-2001-b6-a-approx n epsilon))
         (putnam-2001-b6-a-approx
          (- n i) epsilon))
        (putnam-2001-b6-a-approx
         (+ n i) epsilon))
       (* 4 epsilon))))))

(defun-sk putnam-2001-b6-midpoint-gap-positive-p
    (n i)
  (exists (margin)
    (and
     (putnam-2001-b6-positive-rational-p margin)
     (putnam-2001-b6-midpoint-margin-p
      n i margin))))

(defun-sk putnam-2001-b6-good-index-p (n)
  (forall (i)
    (implies
     (and
      (natp i)
      (<= 1 i)
      (<= i (- n 1)))
     (putnam-2001-b6-midpoint-gap-positive-p
      n i))))

(defun-sk putnam-2001-b6-good-index-above-p (m)
  (exists (n)
    (and
     (posp n)
     (< m n)
     (putnam-2001-b6-good-index-p n))))

;; An infinite subset of the naturals is equivalently unbounded.

(defun-sk putnam-2001-b6-unbounded-good-indices-p ()
  (forall (m)
    (implies
     (natp m)
     (putnam-2001-b6-good-index-above-p m))))

;; The benchmark's catalogued answer is True, so the source equivalence with
;; that answer reduces to the universally generic implication below.

(defun putnambench-putnam-2001-b6-statement ()
  (implies
   (and
    (putnam-2001-b6-regular-name-p)
    (putnam-2001-b6-positive-increasing-p)
    (putnam-2001-b6-limit-zero-p))
   (putnam-2001-b6-unbounded-good-indices-p)))

(value-triple :itpeval-statement-checked)
:q
