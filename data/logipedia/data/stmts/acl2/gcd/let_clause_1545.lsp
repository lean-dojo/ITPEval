;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_1545, catalog title "gcd.let_clause_1545": the nested
;; natural-number implication from gcd(m,n) = 0 and zero divisibility,
;; through universal quotient clauses, concludes m = 0. This file contains
;; no proof.

(in-package "ACL2")

(defun-sk logipedia-gcd-let-clause-1545-divides-p (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

;; The subtraction Euclidean algorithm represents the source natural gcd.
(defun logipedia-gcd-let-clause-1545-gcd (m n)
  (declare (xargs :measure (+ (nfix m) (nfix n))))
  (if (and (natp m) (natp n))
      (cond
       ((equal m 0) n)
       ((equal n 0) m)
       ((<= m n)
        (logipedia-gcd-let-clause-1545-gcd m (- n m)))
       (t
        (logipedia-gcd-let-clause-1545-gcd (- m n) n)))
    0))

(defun-sk logipedia-gcd-let-clause-1545-forall-q2-p (m)
  (forall (q2)
    (implies
     (natp q2)
     (implies
      (equal m (* 0 q2))
      (equal m 0)))))

(defun-sk logipedia-gcd-let-clause-1545-forall-q1-p (m n)
  (forall (q1)
    (implies
     (natp q1)
     (implies
      (equal n (* 0 q1))
      (implies
       (logipedia-gcd-let-clause-1545-divides-p 0 m)
       (logipedia-gcd-let-clause-1545-forall-q2-p m))))))

(defun-sk logipedia-gcd-let-clause-1545-statement ()
  (forall (m n)
    (implies
     (and (natp m)
          (natp n))
     (implies
      (equal (logipedia-gcd-let-clause-1545-gcd m n) 0)
      (implies
       (logipedia-gcd-let-clause-1545-divides-p 0 n)
       (logipedia-gcd-let-clause-1545-forall-q1-p m n))))))

(value-triple :itpeval-statement-checked)
:q
