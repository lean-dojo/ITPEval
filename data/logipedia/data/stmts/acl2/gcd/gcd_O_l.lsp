;; Statement-only formalization of Logipedia corpus artifact gcd.gcd_O_l,
;; catalog title "gcd.gcd_O_l": for every natural number m, the module-defined
;; greatest common divisor of zero and m equals m. This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-gcd-o-l-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-gcd-o-l-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-gcd-o-l-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-gcd-o-l-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-gcd-o-l-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-gcd-o-l (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-gcd-o-l-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-gcd-o-l-aux
     (nfix m) (nfix n) (nfix m))))

(defun-sk logipedia-gcd-gcd-o-l-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal
      (logipedia-gcd-gcd-o-l 0 m)
      m))))

(value-triple :itpeval-statement-checked)
:q
