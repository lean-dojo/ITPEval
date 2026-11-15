;; Statement-only formalization of hundred-theorems artifact
;; 011_the_infinitude_of_primes ("The Infinitude of Primes"): for every
;; natural-number bound n, there exists a prime p greater than n, so the
;; natural primes are unbounded and infinite. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-011-has-nontrivial-divisor (p d)
  (declare (xargs :measure (nfix d)))
  (if (or (not (natp d))
          (< d 2))
      nil
    (or (equal (mod p d) 0)
        (hundred-theorems-011-has-nontrivial-divisor p (- d 1)))))

(defun hundred-theorems-011-primep (p)
  (and (natp p)
       (< 1 p)
       (not (hundred-theorems-011-has-nontrivial-divisor
             p
             (- p 1)))))

(defun-sk hundred-theorems-011-infinitude-of-primes-statement (n)
  (exists (p)
    (implies
     (natp n)
     (and
      (hundred-theorems-011-primep p)
      (< n p)))))

(value-triple :itpeval-statement-checked)
:q
