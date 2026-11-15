;; Statement-only formalization of Logipedia corpus artifact
;; fermat.eq_fact_pi_p, catalog title "fermat.eq_fact_pi_p": for every natural
;; number n, n factorial equals the product of i + 1 over natural indices
;; i below (n + 1) - 1. This file contains no proof.

(in-package "ACL2")

;; The source factorial recurrence multiplies the previous factorial by n on
;; the right.
(defun logipedia-fermat-eq-fact-pi-p-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (logipedia-fermat-eq-fact-pi-p-factorial (- n 1))
       n)))

;; With the constantly true selector, source bigop over a bound k multiplies
;; f(k - 1) on the left of the recursively computed prefix. Here f(i) = i + 1.
(defun logipedia-fermat-eq-fact-pi-p-product (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (* (+ (- k 1) 1)
       (logipedia-fermat-eq-fact-pi-p-product (- k 1)))))

(defun-sk logipedia-fermat-eq-fact-pi-p-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      (logipedia-fermat-eq-fact-pi-p-factorial n)
      (logipedia-fermat-eq-fact-pi-p-product
       (nfix (- (+ n 1) 1)))))))

(value-triple :itpeval-statement-checked)
:q
