;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_1544, catalog title "gcd.let_clause_1544": a natural-number
;; bounded-gcd induction hypothesis and successor-step premises imply that
;; commuting b*n to n*b preserves the stated truncated-difference equality.
;; This file contains no proof.

(in-package "ACL2")

;; The source natural remainder is totalized by mod(dividend, 0) = dividend.

(defun logipedia-gcd-let-clause-1544-mod (dividend divisor)
  (if (zp divisor)
      (nfix dividend)
    (mod (nfix dividend) (nfix divisor))))

;; This is the source module's gcd_aux recursion: zero fuel returns the
;; dividend; positive fuel returns the divisor when it divides the dividend
;; and otherwise recurses on the corresponding remainder.

(defun logipedia-gcd-let-clause-1544-aux
    (fuel dividend divisor)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (nfix dividend)
    (if (equal
         (logipedia-gcd-let-clause-1544-mod
          dividend divisor)
         0)
        (nfix divisor)
      (logipedia-gcd-let-clause-1544-aux
       (- (nfix fuel) 1)
       (nfix divisor)
       (logipedia-gcd-let-clause-1544-mod
        dividend divisor)))))

(defun logipedia-gcd-let-clause-1544-minus (left right)
  (nfix (- (nfix left) (nfix right))))

;; Source divisibility is the existence of a natural quotient.

(defun-sk logipedia-gcd-let-clause-1544-divides-p
    (divisor dividend)
  (exists (quotient)
    (and
     (natp divisor)
     (natp dividend)
     (natp quotient)
     (equal dividend (* divisor quotient)))))

;; This is the disjunction occurring in both source existential clauses.

(defun logipedia-gcd-let-clause-1544-alternative-p
    (fuel dividend divisor a b)
  (let ((bounded-gcd
         (logipedia-gcd-let-clause-1544-aux
          fuel dividend divisor)))
    (or
     (equal
      (logipedia-gcd-let-clause-1544-minus
       (* a divisor)
       (* b dividend))
      bounded-gcd)
     (equal
      (logipedia-gcd-let-clause-1544-minus
       (* b dividend)
       (* a divisor))
      bounded-gcd))))

(defun-sk logipedia-gcd-let-clause-1544-pair-exists-p
    (fuel dividend divisor)
  (exists (a b)
    (and
     (natp a)
     (natp b)
     (logipedia-gcd-let-clause-1544-alternative-p
      fuel dividend divisor a b))))

;; This predicate preserves the source induction hypothesis:
;; forall m n, 0 < n -> n <= m -> n <= q -> exists a b, ...

(defun-sk logipedia-gcd-let-clause-1544-induction-hypothesis-p
    (q)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (< 0 n)
      (implies
       (<= n m)
       (implies
        (<= n q)
        (logipedia-gcd-let-clause-1544-pair-exists-p
         q m n)))))))

;; The step's existential premise fixes a and quantifies only b.

(defun-sk logipedia-gcd-let-clause-1544-step-witness-p
    (q m n a)
  (exists (b)
    (and
     (natp b)
     (logipedia-gcd-let-clause-1544-alternative-p
      q
      n
      (logipedia-gcd-let-clause-1544-mod m n)
      a
      b))))

(defun logipedia-gcd-let-clause-1544-forward-equality-p
    (q m n a b)
  (let ((remainder
         (logipedia-gcd-let-clause-1544-mod m n)))
    (equal
     (logipedia-gcd-let-clause-1544-minus
      (* a remainder)
      (* b n))
     (logipedia-gcd-let-clause-1544-aux
      q n remainder))))

(defun logipedia-gcd-let-clause-1544-commuted-equality-p
    (q m n a b)
  (let ((remainder
         (logipedia-gcd-let-clause-1544-mod m n)))
    (equal
     (logipedia-gcd-let-clause-1544-minus
      (* a remainder)
      (* n b))
     (logipedia-gcd-let-clause-1544-aux
      q n remainder))))

;; For each source b, retain both the disjunctive premise and the forward
;; equality premise before stating the equality with the commuted product.

(defun-sk logipedia-gcd-let-clause-1544-all-b-clause-p
    (q m n a)
  (forall (b)
    (implies
     (natp b)
     (implies
      (logipedia-gcd-let-clause-1544-alternative-p
       q
       n
       (logipedia-gcd-let-clause-1544-mod m n)
       a
       b)
      (implies
       (logipedia-gcd-let-clause-1544-forward-equality-p
        q m n a b)
       (logipedia-gcd-let-clause-1544-commuted-equality-p
        q m n a b))))))

(defun-sk logipedia-gcd-let-clause-1544-all-a-clause-p
    (q m n)
  (forall (a)
    (implies
     (natp a)
     (implies
      (logipedia-gcd-let-clause-1544-step-witness-p
       q m n a)
      (logipedia-gcd-let-clause-1544-all-b-clause-p
       q m n a)))))

(defun-sk logipedia-gcd-let-clause-1544-successor-clause-p
    (q)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (implies
      (< 0 n)
      (implies
       (<= n m)
       (implies
        (<= n (+ q 1))
        (implies
         (not
          (logipedia-gcd-let-clause-1544-divides-p
           n m))
         (logipedia-gcd-let-clause-1544-all-a-clause-p
          q m n))))))))

;; Parameter p is intentionally quantified although it is unused after its
;; binder, exactly as in the source declaration.

(defun-sk logipedia-gcd-let-clause-1544-statement ()
  (forall (p q)
    (implies
     (and
      (natp p)
      (natp q))
     (implies
      (logipedia-gcd-let-clause-1544-induction-hypothesis-p
       q)
      (logipedia-gcd-let-clause-1544-successor-clause-p
       q)))))

(value-triple :itpeval-statement-checked)
:q
