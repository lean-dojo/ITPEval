;; Statement-only formalization of Logipedia corpus artifact
;; gcd.divides_mod_to_divides, catalog title "gcd.divides_mod_to_divides":
;; for natural p, m, and positive n, if p divides m modulo n and p divides
;; n, then p divides m. This file contains no proof.

(in-package "ACL2")

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-divides-mod-to-divides-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

(defun-sk logipedia-gcd-divides-mod-to-divides-statement ()
  (forall (p m n)
    (implies
     (and
      (natp p)
      (natp m)
      (natp n)
      (< 0 n)
      (logipedia-gcd-divides-mod-to-divides-divides-p
       p (mod m n))
      (logipedia-gcd-divides-mod-to-divides-divides-p
       p n))
     (logipedia-gcd-divides-mod-to-divides-divides-p
      p m))))

(value-triple :itpeval-statement-checked)
:q
