;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_b2:
;; every nonempty cancellative semigroup in which each element has a finite
;; positive-power orbit has a two-sided identity and two-sided inverses. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB is ACL2's conservative mechanism for a generic function symbol.
;; These declarations therefore range over an arbitrary carrier predicate and
;; binary operation, rather than the restricted class of APPLY$-tame objects.

(defstub putnam-1989-b2-carrier (x) t)
(defstub putnam-1989-b2-multiply (x y) t)

(defun putnam-1989-b2-member-p (x)
  (if (putnam-1989-b2-carrier x) t nil))

(defun-sk putnam-1989-b2-nonempty-p ()
  (exists (x)
    (putnam-1989-b2-member-p x)))

(defun-sk putnam-1989-b2-closed-p ()
  (forall (x y)
    (implies
     (and
      (putnam-1989-b2-member-p x)
      (putnam-1989-b2-member-p y))
     (putnam-1989-b2-member-p
      (putnam-1989-b2-multiply x y)))))

(defun-sk putnam-1989-b2-associative-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1989-b2-member-p x)
      (putnam-1989-b2-member-p y)
      (putnam-1989-b2-member-p z))
     (equal
      (putnam-1989-b2-multiply
       (putnam-1989-b2-multiply x y)
       z)
      (putnam-1989-b2-multiply
       x
       (putnam-1989-b2-multiply y z))))))

(defun-sk putnam-1989-b2-cancellative-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1989-b2-member-p x)
      (putnam-1989-b2-member-p y)
      (putnam-1989-b2-member-p z))
     (and
      (implies
       (equal
        (putnam-1989-b2-multiply x y)
        (putnam-1989-b2-multiply x z))
       (equal y z))
      (implies
       (equal
        (putnam-1989-b2-multiply y x)
        (putnam-1989-b2-multiply z x))
       (equal y z))))))

;; POWER(A,N) is the source's a^(N+1), defined without assuming an identity:
;; POWER(A,0)=A and POWER(A,N+1)=A*POWER(A,N).

(defun putnam-1989-b2-power (a n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      a
    (putnam-1989-b2-multiply
     a
     (putnam-1989-b2-power a (- n 1)))))

(defun-sk putnam-1989-b2-power-representative-exists-p
    (a n bound)
  (exists (k)
    (and
     (natp k)
     (< k bound)
     (equal
      (putnam-1989-b2-power a n)
      (putnam-1989-b2-power a k)))))

;; A sequence has finite range iff some finite initial segment contains every
;; value. BOUND remains an internal existential witness.

(defun-sk putnam-1989-b2-power-orbit-covered-p
    (a bound)
  (forall (n)
    (implies
     (natp n)
     (putnam-1989-b2-power-representative-exists-p
      a n bound))))

(defun-sk putnam-1989-b2-finite-power-orbit-p (a)
  (exists (bound)
    (and
     (posp bound)
     (putnam-1989-b2-power-orbit-covered-p
      a bound))))

(defun-sk putnam-1989-b2-all-power-orbits-finite-p ()
  (forall (a)
    (implies
     (putnam-1989-b2-member-p a)
     (putnam-1989-b2-finite-power-orbit-p a))))

(defun putnam-1989-b2-semigroup-hypotheses-p ()
  (and
   (putnam-1989-b2-nonempty-p)
   (putnam-1989-b2-closed-p)
   (putnam-1989-b2-associative-p)
   (putnam-1989-b2-cancellative-p)
   (putnam-1989-b2-all-power-orbits-finite-p)))

(defun-sk putnam-1989-b2-inverse-exists-p (e x)
  (exists (y)
    (and
     (putnam-1989-b2-member-p y)
     (equal
      (putnam-1989-b2-multiply x y)
      e)
     (equal
      (putnam-1989-b2-multiply y x)
      e))))

(defun-sk putnam-1989-b2-identity-and-inverses-p (e)
  (forall (x)
    (implies
     (putnam-1989-b2-member-p x)
     (and
      (equal
       (putnam-1989-b2-multiply e x)
       x)
      (equal
       (putnam-1989-b2-multiply x e)
       x)
      (putnam-1989-b2-inverse-exists-p e x)))))

(defun-sk putnam-1989-b2-group-witness-exists-p ()
  (exists (e)
    (and
     (putnam-1989-b2-member-p e)
     (putnam-1989-b2-identity-and-inverses-p e))))

(defun putnambench-putnam-1989-b2-statement ()
  (implies
   (putnam-1989-b2-semigroup-hypotheses-p)
   (putnam-1989-b2-group-witness-exists-p)))

(value-triple :itpeval-statement-checked)
:q
