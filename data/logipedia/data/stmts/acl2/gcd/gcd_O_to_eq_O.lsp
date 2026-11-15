;; Statement-only formalization of Logipedia corpus artifact
;; gcd.gcd_O_to_eq_O, catalog title "gcd.gcd_O_to_eq_O": for natural numbers
;; m and n, if the module-defined greatest common divisor is zero, then both
;; m and n are zero. This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-gcd-o-to-eq-o-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-gcd-o-to-eq-o-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-gcd-o-to-eq-o-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-gcd-o-to-eq-o-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-gcd-o-to-eq-o-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-gcd-o-to-eq-o (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-gcd-o-to-eq-o-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-gcd-o-to-eq-o-aux
     (nfix m) (nfix n) (nfix m))))

(defun-sk logipedia-gcd-gcd-o-to-eq-o-statement ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (equal
       (logipedia-gcd-gcd-o-to-eq-o m n)
       0)
      (and
       (equal m 0)
       (equal n 0))))))

(value-triple :itpeval-statement-checked)
:q
