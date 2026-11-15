;; Statement-only formalization of Logipedia corpus artifact
;; gcd.prime_to_gcd_1, catalog title "gcd.prime_to_gcd_1": for natural
;; numbers n and m, if n is prime and does not divide m, then the module's
;; greatest common divisor of n and m is one. This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-prime-to-gcd-1-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-prime-to-gcd-1-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-prime-to-gcd-1-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-prime-to-gcd-1-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-prime-to-gcd-1-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-prime-to-gcd-1 (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-prime-to-gcd-1-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-prime-to-gcd-1-aux
     (nfix m) (nfix n) (nfix m))))

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-prime-to-gcd-1-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

;; The source prime predicate says that n is greater than one and every
;; divisor of n that is greater than one is n itself.

(defun-sk logipedia-gcd-prime-to-gcd-1-prime-divisors-p
    (n)
  (forall (divisor)
    (implies
     (and
      (natp divisor)
      (logipedia-gcd-prime-to-gcd-1-divides-p
       divisor n)
      (< 1 divisor))
     (equal divisor n))))

(defun logipedia-gcd-prime-to-gcd-1-prime-p (n)
  (and
   (natp n)
   (< 1 n)
   (logipedia-gcd-prime-to-gcd-1-prime-divisors-p
    n)))

(defun-sk logipedia-gcd-prime-to-gcd-1-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m)
      (logipedia-gcd-prime-to-gcd-1-prime-p n))
     (implies
      (not
       (logipedia-gcd-prime-to-gcd-1-divides-p
        n m))
      (equal
       (logipedia-gcd-prime-to-gcd-1 n m)
       1)))))

(value-triple :itpeval-statement-checked)
:q
