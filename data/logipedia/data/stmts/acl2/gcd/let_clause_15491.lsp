;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_15491, catalog title "gcd.let_clause_15491": if a natural
;; number n is zero, then every natural x1106 equals x1106 minus n, with the
;; source's unused natural parameter m retained. This file contains no proof.

(in-package "ACL2")

(defun logipedia-gcd-let-clause-15491-minus (minuend subtrahend)
  (nfix (- (nfix minuend) (nfix subtrahend))))

(defun-sk logipedia-gcd-let-clause-15491-all-x-p (n)
  (forall (x1106)
    (implies
     (natp x1106)
     (equal
      x1106
      (logipedia-gcd-let-clause-15491-minus
       x1106 n)))))

(defun-sk logipedia-gcd-let-clause-15491-statement ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (equal 0 n)
      (logipedia-gcd-let-clause-15491-all-x-p n)))))

(value-triple :itpeval-statement-checked)
:q
