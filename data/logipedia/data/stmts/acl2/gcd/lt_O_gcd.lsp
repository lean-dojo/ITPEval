;; Statement-only formalization of Logipedia corpus artifact gcd.lt_O_gcd,
;; catalog title "gcd.lt_O_gcd": for all natural numbers m and n, positivity
;; of n implies positivity of their module-defined greatest common divisor.
;; This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-lt-o-gcd-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-lt-o-gcd-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-lt-o-gcd-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-lt-o-gcd-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-lt-o-gcd-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-lt-o-gcd (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-lt-o-gcd-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-lt-o-gcd-aux
     (nfix m) (nfix n) (nfix m))))

(defun-sk logipedia-gcd-lt-o-gcd-statement ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (< 0 n)
      (< 0 (logipedia-gcd-lt-o-gcd m n))))))

(value-triple :itpeval-statement-checked)
:q
