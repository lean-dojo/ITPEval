;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_15441, catalog title "gcd.let_clause_15441": a natural-number
;; gcd_aux induction clause in which commutativity of multiplication preserves
;; a truncated-difference equality under the stated Bezout-style hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(defun logipedia-gcd-let-clause-15441-mod (m n)
  (if (zp n)
      (nfix m)
    (mod (nfix m) (nfix n))))

(defun logipedia-gcd-let-clause-15441-gcd-aux (p m n)
  (declare (xargs :measure (nfix p)))
  (if (zp p)
      (nfix m)
    (if (equal (logipedia-gcd-let-clause-15441-mod m n) 0)
        (nfix n)
      (logipedia-gcd-let-clause-15441-gcd-aux
       (- p 1)
       (nfix n)
       (logipedia-gcd-let-clause-15441-mod m n)))))

(defun-sk logipedia-gcd-let-clause-15441-divides-p (divisor value)
  (exists (quotient)
    (and
     (natp quotient)
     (equal value (* divisor quotient)))))

(defun logipedia-gcd-let-clause-15441-bezout-p (q m n a b)
  (or
   (equal
    (nfix (- (* a n) (* b m)))
    (logipedia-gcd-let-clause-15441-gcd-aux q m n))
   (equal
    (nfix (- (* b m) (* a n)))
    (logipedia-gcd-let-clause-15441-gcd-aux q m n))))

(defun-sk logipedia-gcd-let-clause-15441-bezout-exists-p (q m n)
  (exists (a b)
    (and
     (natp a)
     (natp b)
     (logipedia-gcd-let-clause-15441-bezout-p q m n a b))))

(defun-sk logipedia-gcd-let-clause-15441-induction-hypothesis-p (q)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (< 0 n)
      (<= n m)
      (<= n q))
     (logipedia-gcd-let-clause-15441-bezout-exists-p q m n))))

(defun logipedia-gcd-let-clause-15441-step-bezout-p (q m n a b)
  (or
   (equal
    (nfix
     (- (* a (logipedia-gcd-let-clause-15441-mod m n))
        (* b n)))
    (logipedia-gcd-let-clause-15441-gcd-aux
     q n (logipedia-gcd-let-clause-15441-mod m n)))
   (equal
    (nfix
     (- (* b n)
        (* a (logipedia-gcd-let-clause-15441-mod m n))))
    (logipedia-gcd-let-clause-15441-gcd-aux
     q n (logipedia-gcd-let-clause-15441-mod m n)))))

(defun-sk logipedia-gcd-let-clause-15441-step-exists-p (q m n a)
  (exists (b)
    (and
     (natp b)
     (logipedia-gcd-let-clause-15441-step-bezout-p q m n a b))))

(defun logipedia-gcd-let-clause-15441-second-equality-p (q m n a b)
  (equal
   (nfix
    (- (* b n)
       (* a (logipedia-gcd-let-clause-15441-mod m n))))
   (logipedia-gcd-let-clause-15441-gcd-aux
    q n (logipedia-gcd-let-clause-15441-mod m n))))

(defun logipedia-gcd-let-clause-15441-final-equality-p (q m n a b)
  (equal
   (nfix
    (- (* n b)
       (* a (logipedia-gcd-let-clause-15441-mod m n))))
   (logipedia-gcd-let-clause-15441-gcd-aux
    q n (logipedia-gcd-let-clause-15441-mod m n))))

(defun-sk logipedia-gcd-let-clause-15441-forall-b-p (q m n a)
  (forall (b)
    (implies
     (natp b)
     (implies
      (logipedia-gcd-let-clause-15441-step-bezout-p q m n a b)
      (implies
       (logipedia-gcd-let-clause-15441-second-equality-p q m n a b)
       (logipedia-gcd-let-clause-15441-final-equality-p q m n a b))))))

(defun-sk logipedia-gcd-let-clause-15441-forall-a-p (q m n)
  (forall (a)
    (implies
     (natp a)
     (implies
      (logipedia-gcd-let-clause-15441-step-exists-p q m n a)
      (logipedia-gcd-let-clause-15441-forall-b-p q m n a)))))

(defun-sk logipedia-gcd-let-clause-15441-conclusion-p (q)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (< 0 n)
      (<= n m)
      (<= n (+ q 1))
      (not
       (logipedia-gcd-let-clause-15441-divides-p n m)))
     (logipedia-gcd-let-clause-15441-forall-a-p q m n))))

(defun-sk logipedia-gcd-let-clause-15441-statement ()
  (forall (p q)
    (implies
     (and
      (natp p)
      (natp q))
     (implies
      (logipedia-gcd-let-clause-15441-induction-hypothesis-p q)
      (logipedia-gcd-let-clause-15441-conclusion-p q)))))

(value-triple :itpeval-statement-checked)
:q
