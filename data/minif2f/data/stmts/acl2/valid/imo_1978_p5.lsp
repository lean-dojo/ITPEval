;; Statement-only formalization of miniF2F corpus artifact imo_1978_p5:
;; for every positive natural n and injection of the naturals fixing zero,
;; the sum of 1/k from 1 through n is at most the sum of a(k)/k^2.
;; This file contains no proof.
;;
;; The conclusion uses only a(1), ..., a(n). Restricting a to those indices
;; gives a length-n list of positive pairwise-distinct naturals. Conversely,
;; every such list extends to an injection on all naturals that fixes zero by
;; mapping the remaining indices bijectively to the unused positive naturals.
;; Thus the finite-prefix encoding is bidirectionally equivalent to the source
;; quantification over injections. ACL2 evaluates the sums as exact rationals,
;; whose order agrees with their embedding into the source real numbers.

(in-package "ACL2")

(defun imo-1978-p5-positive-distinct-list-p (values)
  (if (consp values)
      (and (natp (car values))
           (< 0 (car values))
           (not (member-equal (car values) (cdr values)))
           (imo-1978-p5-positive-distinct-list-p (cdr values)))
    (equal values nil)))

(defun imo-1978-p5-harmonic-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (imo-1978-p5-harmonic-sum (- n 1))
       (/ 1 n))))

(defun imo-1978-p5-weighted-sum (values k)
  (if (consp values)
      (+ (/ (car values) (* k k))
         (imo-1978-p5-weighted-sum (cdr values) (+ k 1)))
    0))

(defun imo-1978-p5-statement (values n)
  (implies
   (and (natp n)
        (< 0 n)
        (imo-1978-p5-positive-distinct-list-p values)
        (equal (len values) n))
   (<= (imo-1978-p5-harmonic-sum n)
       (imo-1978-p5-weighted-sum values 1))))

(value-triple :itpeval-statement-checked)
:q
