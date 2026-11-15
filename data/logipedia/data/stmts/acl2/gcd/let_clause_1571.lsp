;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_1571, catalog title "gcd.let_clause_1571": for natural
;; numbers m and n, the stated positivity and zero-equality hypotheses for
;; the module-defined gcd, m, and n imply m = n. This file contains no proof.

(in-package "ACL2")

;; The source remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-let-clause-1571-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This bounded Euclidean recursion is the source module's gcd_aux: index zero
;; returns the dividend; a successor returns the divisor when it divides the
;; dividend and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-let-clause-1571-aux
    (index dividend divisor)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-let-clause-1571-mod dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-let-clause-1571-aux
       (- (nfix index) 1)
       (nfix divisor)
       (logipedia-gcd-let-clause-1571-mod
        dividend divisor)))))

;; The source gcd selects the bounded call whose recursion index is the
;; smaller input.

(defun logipedia-gcd-let-clause-1571-gcd (n m)
  (if (<= (nfix n) (nfix m))
      (logipedia-gcd-let-clause-1571-aux
       (nfix n) (nfix m) (nfix n))
    (logipedia-gcd-let-clause-1571-aux
     (nfix m) (nfix n) (nfix m))))

(defun-sk logipedia-gcd-let-clause-1571-statement ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (< 0 n)
      (implies
       (equal
        (logipedia-gcd-let-clause-1571-gcd m n)
        0)
       (implies
        (equal m 0)
        (implies
         (equal n 0)
         (equal m n))))))))

(value-triple :itpeval-statement-checked)
:q
