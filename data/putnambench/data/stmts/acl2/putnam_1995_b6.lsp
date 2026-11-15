;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_b6:
;; no three positive real Beatty sequences {floor(n*alpha) : n >= 1} are
;; pairwise disjoint and together equal the positive natural numbers. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols present arbitrary real scalars and their
;; floor operation. The floor law is the exact integer-part property, so no
;; Cauchy-name approximation or APPLY$ restriction is introduced.

(defstub p95b6-scalar-p (x) t)
(defstub p95b6-add (x y) t)
(defstub p95b6-multiply (x y) t)
(defstub p95b6-negate (x) t)
(defstub p95b6-less (x y) t)
(defstub p95b6-integer-embed (n) t)
(defstub p95b6-floor (x) t)

(defun p95b6-member-p (x)
  (if (p95b6-scalar-p x) t nil))

(defun p95b6-less-p (x y)
  (if (p95b6-less x y) t nil))

(defun p95b6-less-equal-p (x y)
  (not (p95b6-less-p y x)))

(defun-sk p95b6-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p95b6-member-p x)
      (p95b6-member-p y)
      (p95b6-member-p z))
     (and
      (p95b6-member-p (p95b6-add x y))
      (p95b6-member-p (p95b6-multiply x y))
      (p95b6-member-p (p95b6-negate x))
      (equal
       (p95b6-add (p95b6-add x y) z)
       (p95b6-add x (p95b6-add y z)))
      (equal (p95b6-add x y) (p95b6-add y x))
      (equal (p95b6-add x zero) x)
      (equal (p95b6-add x (p95b6-negate x)) zero)
      (equal
       (p95b6-multiply (p95b6-multiply x y) z)
       (p95b6-multiply x (p95b6-multiply y z)))
      (equal (p95b6-multiply x y) (p95b6-multiply y x))
      (equal (p95b6-multiply x one) x)
      (equal
       (p95b6-multiply x (p95b6-add y z))
       (p95b6-add
        (p95b6-multiply x y)
        (p95b6-multiply x z)))))))

(defun-sk p95b6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p95b6-member-p x)
      (p95b6-member-p y)
      (p95b6-member-p z))
     (and
      (not (p95b6-less-p x x))
      (or
       (equal x y)
       (p95b6-less-p x y)
       (p95b6-less-p y x))
      (implies
       (and
        (p95b6-less-p x y)
        (p95b6-less-p y z))
       (p95b6-less-p x z))
      (implies
       (p95b6-less-p x y)
       (p95b6-less-p
        (p95b6-add x z)
        (p95b6-add y z)))
      (implies
       (and
        (p95b6-less-p zero x)
        (p95b6-less-p zero y))
       (p95b6-less-p
        zero
        (p95b6-multiply x y)))))))

(defun-sk p95b6-integer-embedding-laws-p ()
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (p95b6-member-p (p95b6-integer-embed m))
      (equal
       (p95b6-integer-embed (+ m n))
       (p95b6-add
        (p95b6-integer-embed m)
        (p95b6-integer-embed n)))
      (equal
       (p95b6-integer-embed (* m n))
       (p95b6-multiply
        (p95b6-integer-embed m)
        (p95b6-integer-embed n)))
      (iff
       (< m n)
       (p95b6-less-p
        (p95b6-integer-embed m)
        (p95b6-integer-embed n)))))))

(defun-sk p95b6-floor-laws-p ()
  (forall (x)
    (implies
     (p95b6-member-p x)
     (and
      (integerp (p95b6-floor x))
      (p95b6-less-equal-p
       (p95b6-integer-embed (p95b6-floor x))
       x)
      (p95b6-less-p
       x
       (p95b6-integer-embed
        (+ 1 (p95b6-floor x))))))))

(defun p95b6-real-floor-context-p (zero one)
  (and
   (p95b6-member-p zero)
   (p95b6-member-p one)
   (not (equal zero one))
   (p95b6-ring-laws-p zero one)
   (p95b6-order-laws-p zero)
   (p95b6-less-p zero one)
   (equal (p95b6-integer-embed 0) zero)
   (equal (p95b6-integer-embed 1) one)
   (p95b6-integer-embedding-laws-p)
   (p95b6-floor-laws-p)))

(defun p95b6-positive-natural-p (n)
  (and (natp n) (< 0 n)))

(defun p95b6-positive-scalar-p (zero x)
  (and
   (p95b6-member-p x)
   (p95b6-less-p zero x)))

(defun-sk p95b6-beatty-member-p (alpha x)
  (exists (n)
    (and
     (p95b6-positive-natural-p n)
     (natp x)
     (equal
      x
      (p95b6-floor
       (p95b6-multiply
        (p95b6-integer-embed n)
        alpha))))))

(defun-sk p95b6-pairwise-disjoint-p (left right)
  (forall (x)
    (not
     (and
      (p95b6-beatty-member-p left x)
      (p95b6-beatty-member-p right x)))))

(defun-sk p95b6-union-is-positive-naturals-p
    (alpha beta gamma)
  (forall (x)
    (iff
     (p95b6-positive-natural-p x)
     (or
      (p95b6-beatty-member-p alpha x)
      (p95b6-beatty-member-p beta x)
      (p95b6-beatty-member-p gamma x)))))

(defun p95b6-counterexample-p
    (zero alpha beta gamma)
  (and
   (p95b6-positive-scalar-p zero alpha)
   (p95b6-positive-scalar-p zero beta)
   (p95b6-positive-scalar-p zero gamma)
   (p95b6-pairwise-disjoint-p alpha beta)
   (p95b6-pairwise-disjoint-p beta gamma)
   (p95b6-pairwise-disjoint-p alpha gamma)
   (p95b6-union-is-positive-naturals-p
    alpha beta gamma)))

(defun-sk p95b6-counterexample-exists-p (zero)
  (exists (alpha beta gamma)
    (p95b6-counterexample-p
     zero alpha beta gamma)))

(defun putnambench-putnam-1995-b6-statement (zero one)
  (implies
   (p95b6-real-floor-context-p zero one)
   (not (p95b6-counterexample-exists-p zero))))

(value-triple :itpeval-statement-checked)
:q
