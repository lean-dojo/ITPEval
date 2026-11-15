;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__005, "The Prime Number Theorem": the number of
;; primes at most n is asymptotic to n / ln(n). This file contains no proof.

(in-package "ACL2")

(defun pnt-has-divisor-at-most-p (n divisor)
  (if (or (not (natp n))
          (not (natp divisor))
          (< divisor 2))
      nil
    (or (equal (mod n divisor) 0)
        (pnt-has-divisor-at-most-p n (- divisor 1)))))

(defun pnt-prime-p (n)
  (and (natp n)
       (<= 2 n)
       (not (pnt-has-divisor-at-most-p n (- n 1)))))

(defun pnt-prime-count (n)
  (if (zp n)
      0
    (+ (if (pnt-prime-p n) 1 0)
       (pnt-prime-count (- n 1)))))

;; For z = (n - 1)/(n + 1), twice the limit of this sum is ln(n).
(defun pnt-atanh-series-prefix (z terms)
  (if (zp terms)
      0
    (let* ((index (- terms 1))
           (odd-exponent (+ (* 2 index) 1)))
      (+ (pnt-atanh-series-prefix z index)
         (/ (expt z odd-exponent) odd-exponent)))))

(defun pnt-natural-log-prefix (n terms)
  (if (and (natp n)
           (< 0 n)
           (natp terms))
      (* 2
         (pnt-atanh-series-prefix (/ (- n 1) (+ n 1))
                                  terms))
    0))

;; Quantifier order for the final predicate:
;;   for every epsilon > 0, there exists cutoff, for every n >= cutoff,
;;   there exists log-cutoff, for every terms >= log-cutoff.
(defun-sk pnt-log-tail-p (epsilon n log-cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (<= log-cutoff terms))
     (< (abs (- (/ (* (pnt-prime-count n)
                       (pnt-natural-log-prefix n terms))
                    n)
                1))
        epsilon))))

(defun-sk pnt-log-cutoff-exists-p (epsilon n)
  (exists (log-cutoff)
    (and (natp log-cutoff)
         (pnt-log-tail-p epsilon n log-cutoff))))

(defun-sk pnt-prime-tail-p (epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (pnt-log-cutoff-exists-p epsilon n))))

(defun-sk pnt-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (<= 2 cutoff)
         (pnt-prime-tail-p epsilon cutoff))))

(defun-sk prime-number-theorem-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (pnt-cutoff-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
