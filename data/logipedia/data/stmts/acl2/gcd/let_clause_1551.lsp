;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_1551, catalog title "gcd.let_clause_1551": if a natural
;; number n is zero, then n equals x347 times n for every natural x347, with
;; the source's unused natural parameter m retained. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-gcd-let-clause-1551-all-x-p (n)
  (forall (x347)
    (implies
     (natp x347)
     (equal n (* x347 n)))))

(defun-sk logipedia-gcd-let-clause-1551-statement ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (equal 0 n)
      (logipedia-gcd-let-clause-1551-all-x-p n)))))

(value-triple :itpeval-statement-checked)
:q
