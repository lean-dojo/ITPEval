;; Statement-only formalization of Logipedia corpus artifact
;; gcd.divides_gcd_aux_mn, catalog title "gcd.divides_gcd_aux_mn": for
;; natural p, m, and positive n with n <= m and n <= p, the fuel-bounded
;; auxiliary Euclidean gcd divides both m and n. This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-divides-gcd-aux-mn-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

(defun logipedia-gcd-divides-gcd-aux-mn-dividesb
    (divisor dividend)
  (equal
   (logipedia-gcd-divides-gcd-aux-mn-mod dividend divisor)
   0))

;; This is the source module's gcd_aux recursion: zero fuel returns the
;; dividend; positive fuel returns the divisor when its Boolean divisibility
;; test succeeds and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-divides-gcd-aux-mn-aux
    (fuel dividend divisor)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (nfix dividend)
    (if
        (logipedia-gcd-divides-gcd-aux-mn-dividesb
         divisor dividend)
        (nfix divisor)
      (logipedia-gcd-divides-gcd-aux-mn-aux
       (- (nfix fuel) 1)
       (nfix divisor)
       (logipedia-gcd-divides-gcd-aux-mn-mod
        dividend divisor)))))

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-divides-gcd-aux-mn-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

(defun-sk logipedia-gcd-divides-gcd-aux-mn-statement ()
  (forall (p m n)
    (implies
     (and
      (natp p)
      (natp m)
      (natp n)
      (< 0 n)
      (<= n m)
      (<= n p))
     (let
         ((common-divisor
           (logipedia-gcd-divides-gcd-aux-mn-aux p m n)))
       (and
        (logipedia-gcd-divides-gcd-aux-mn-divides-p
         common-divisor m)
        (logipedia-gcd-divides-gcd-aux-mn-divides-p
         common-divisor n))))))

(value-triple :itpeval-statement-checked)
:q
