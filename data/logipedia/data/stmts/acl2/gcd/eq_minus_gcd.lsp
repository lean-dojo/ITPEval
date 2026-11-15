;; Statement-only formalization of Logipedia corpus artifact
;; gcd.eq_minus_gcd, catalog title "gcd.eq_minus_gcd": for every pair of
;; natural numbers, natural coefficients give one of the two truncated
;; differences as their module-defined greatest common divisor. This file
;; contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-eq-minus-gcd-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-eq-minus-gcd-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-eq-minus-gcd-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-eq-minus-gcd-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-eq-minus-gcd-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-eq-minus-gcd (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-eq-minus-gcd-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-eq-minus-gcd-aux
     (nfix m) (nfix n) (nfix m))))

(defun-sk logipedia-gcd-eq-minus-gcd-witness-p (m n)
  (exists (a b)
    (and
     (natp a)
     (natp b)
     (or
      (equal
       (nfix (- (* a n) (* b m)))
       (logipedia-gcd-eq-minus-gcd n m))
      (equal
       (nfix (- (* b m) (* a n)))
       (logipedia-gcd-eq-minus-gcd n m))))))

(defun-sk logipedia-gcd-eq-minus-gcd-statement ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (logipedia-gcd-eq-minus-gcd-witness-p m n))))

(value-triple :itpeval-statement-checked)
:q
