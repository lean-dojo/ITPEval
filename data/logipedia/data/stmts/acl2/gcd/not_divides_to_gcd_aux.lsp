;; Statement-only formalization of Logipedia corpus artifact
;; gcd.not_divides_to_gcd_aux, catalog title
;; "gcd.not_divides_to_gcd_aux": for natural p, m, and positive n, if n
;; does not divide m, one successor step of the module's fuel-bounded
;; auxiliary Euclidean gcd recurses on n and the remainder of m modulo n.
;; This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-not-divides-to-gcd-aux-mod
    (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This is the source module's gcd_aux recursion: zero fuel returns the
;; dividend; positive fuel returns the divisor when it divides the dividend
;; and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-not-divides-to-gcd-aux
    (fuel dividend divisor)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-not-divides-to-gcd-aux-mod
          dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-not-divides-to-gcd-aux
       (- (nfix fuel) 1)
       (nfix divisor)
       (logipedia-gcd-not-divides-to-gcd-aux-mod
        dividend divisor)))))

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-not-divides-to-gcd-aux-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

(defun-sk logipedia-gcd-not-divides-to-gcd-aux-statement ()
  (forall (p m n)
    (implies
     (and
      (natp p)
      (natp m)
      (natp n)
      (< 0 n)
      (not
       (logipedia-gcd-not-divides-to-gcd-aux-divides-p
        n m)))
     (equal
      (logipedia-gcd-not-divides-to-gcd-aux
       (+ 1 p) m n)
      (logipedia-gcd-not-divides-to-gcd-aux
       p
       n
       (logipedia-gcd-not-divides-to-gcd-aux-mod
        m n))))))

(value-triple :itpeval-statement-checked)
:q
