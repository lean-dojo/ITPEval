;; Statement-only formalization of Logipedia corpus artifact
;; gcd.divides_gcd_r, catalog title "gcd.divides_gcd_r": for all natural
;; numbers n and m, their module-defined greatest common divisor divides m.
;; This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-divides-gcd-r-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-divides-gcd-r-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-divides-gcd-r-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-divides-gcd-r-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-divides-gcd-r-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-divides-gcd-r (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-divides-gcd-r-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-divides-gcd-r-aux
     (nfix m) (nfix n) (nfix m))))

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-divides-gcd-r-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

(defun-sk logipedia-gcd-divides-gcd-r-statement ()
  (forall (n m)
    (implies
     (and
      (natp n)
      (natp m))
     (logipedia-gcd-divides-gcd-r-divides-p
      (logipedia-gcd-divides-gcd-r n m)
      m))))

(value-triple :itpeval-statement-checked)
:q
