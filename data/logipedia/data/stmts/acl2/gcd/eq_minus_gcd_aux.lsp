;; Statement-only formalization of Logipedia corpus artifact
;; gcd.eq_minus_gcd_aux, catalog title "gcd.eq_minus_gcd_aux": for positive
;; natural n with n <= m and n <= p, two natural coefficients give one of
;; the two truncated differences as the module's fuel-bounded auxiliary gcd.
;; This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-eq-minus-gcd-aux-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This is the source module's gcd_aux recursion: zero fuel returns the
;; dividend; positive fuel returns the divisor when it divides the dividend
;; and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-eq-minus-gcd-aux
    (fuel dividend divisor)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-eq-minus-gcd-aux-mod
          dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-eq-minus-gcd-aux
       (- (nfix fuel) 1)
       (nfix divisor)
       (logipedia-gcd-eq-minus-gcd-aux-mod
        dividend divisor)))))

(defun-sk logipedia-gcd-eq-minus-gcd-aux-witness-p
    (p m n)
  (exists (a b)
    (and
     (natp a)
     (natp b)
     (or
      (equal
       (nfix (- (* a n) (* b m)))
       (logipedia-gcd-eq-minus-gcd-aux p m n))
      (equal
       (nfix (- (* b m) (* a n)))
       (logipedia-gcd-eq-minus-gcd-aux p m n))))))

(defun-sk logipedia-gcd-eq-minus-gcd-aux-statement ()
  (forall (p m n)
    (implies
     (and
      (natp p)
      (natp m)
      (natp n)
      (< 0 n)
      (<= n m)
      (<= n p))
     (logipedia-gcd-eq-minus-gcd-aux-witness-p
      p m n))))

(value-triple :itpeval-statement-checked)
:q
