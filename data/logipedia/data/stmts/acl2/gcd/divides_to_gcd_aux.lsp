;; Statement-only formalization of Logipedia corpus artifact
;; gcd.divides_to_gcd_aux, catalog title "gcd.divides_to_gcd_aux": for
;; natural p, m, and n, if p and n are positive and n divides m, the module's
;; fuel-bounded auxiliary Euclidean gcd at p, m, and n equals n. This file
;; contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-divides-to-gcd-aux-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This is the source module's gcd_aux recursion: zero fuel returns the
;; dividend; positive fuel returns the divisor when it divides the dividend
;; and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-divides-to-gcd-aux
    (fuel dividend divisor)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-divides-to-gcd-aux-mod
          dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-divides-to-gcd-aux
       (- (nfix fuel) 1)
       (nfix divisor)
       (logipedia-gcd-divides-to-gcd-aux-mod
        dividend divisor)))))

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-divides-to-gcd-aux-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

(defun-sk logipedia-gcd-divides-to-gcd-aux-statement ()
  (forall (p m n)
    (implies
     (and
      (natp p)
      (natp m)
      (natp n)
      (< 0 p)
      (< 0 n)
      (logipedia-gcd-divides-to-gcd-aux-divides-p n m))
     (equal
      (logipedia-gcd-divides-to-gcd-aux p m n)
      n))))

(value-triple :itpeval-statement-checked)
:q
