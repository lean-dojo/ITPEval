;; Statement-only formalization of PutnamBench artifact putnam_1963_b5:
;; if a convergent series satisfies 0 <= a(k) <= 100*a(n) whenever
;; 1 <= n <= k <= 2*n, then n*a(n) tends to zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The sequence is an arbitrary conservative ACL2 function symbol over the
;; integers. Scalars live in an Archimedean ordered field with its rational
;; embedding, which faithfully states the source theorem for real sequences
;; without restricting them to ACL2 rationals or APPLY$ function objects.
(defstub p1963b5-scalar-p (x) t)
(defstub p1963b5-add-op (x y) t)
(defstub p1963b5-multiply-op (x y) t)
(defstub p1963b5-negate-op (x) t)
(defstub p1963b5-inverse-op (x) t)
(defstub p1963b5-less-op (x y) t)
(defstub p1963b5-rational-embed (q) t)
(defstub p1963b5-arch-bound (x) t)
(defstub p1963b5-a (n) t)

(defun p1963b5-add (x y)
  (p1963b5-add-op x y))

(defun p1963b5-mul (x y)
  (p1963b5-multiply-op x y))

(defun p1963b5-neg (x)
  (p1963b5-negate-op x))

(defun p1963b5-inv (x)
  (p1963b5-inverse-op x))

(defun p1963b5-sub (x y)
  (p1963b5-add x (p1963b5-neg y)))

(defun p1963b5-less (x y)
  (if (p1963b5-less-op x y) t nil))

(defun p1963b5-less-equal (x y)
  (not (p1963b5-less y x)))

(defun p1963b5-abs (x zero)
  (if (p1963b5-less x zero)
      (p1963b5-neg x)
    x))

(defun-sk p1963b5-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1963b5-scalar-p x)
      (p1963b5-scalar-p y)
      (p1963b5-scalar-p z))
     (and
      (p1963b5-scalar-p (p1963b5-add x y))
      (p1963b5-scalar-p (p1963b5-mul x y))
      (p1963b5-scalar-p (p1963b5-neg x))
      (implies
       (not (equal x zero))
       (p1963b5-scalar-p (p1963b5-inv x)))
      (equal (p1963b5-add (p1963b5-add x y) z)
             (p1963b5-add x (p1963b5-add y z)))
      (equal (p1963b5-add x y)
             (p1963b5-add y x))
      (equal (p1963b5-add x zero) x)
      (equal (p1963b5-add x (p1963b5-neg x)) zero)
      (equal (p1963b5-mul (p1963b5-mul x y) z)
             (p1963b5-mul x (p1963b5-mul y z)))
      (equal (p1963b5-mul x y)
             (p1963b5-mul y x))
      (equal (p1963b5-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1963b5-mul x (p1963b5-inv x)) one))
      (equal
       (p1963b5-mul x (p1963b5-add y z))
       (p1963b5-add
        (p1963b5-mul x y)
        (p1963b5-mul x z)))))))

(defun-sk p1963b5-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1963b5-scalar-p x)
      (p1963b5-scalar-p y)
      (p1963b5-scalar-p z))
     (and
      (not (p1963b5-less x x))
      (or
       (equal x y)
       (p1963b5-less x y)
       (p1963b5-less y x))
      (implies
       (and
        (p1963b5-less x y)
        (p1963b5-less y z))
       (p1963b5-less x z))
      (implies
       (p1963b5-less x y)
       (p1963b5-less
        (p1963b5-add x z)
        (p1963b5-add y z)))
      (implies
       (and
        (p1963b5-less zero x)
        (p1963b5-less zero y))
       (p1963b5-less zero (p1963b5-mul x y)))))))

(defun-sk p1963b5-rational-embedding-laws-p ()
  (forall (q r)
    (implies
     (and (rationalp q) (rationalp r))
     (and
      (p1963b5-scalar-p (p1963b5-rational-embed q))
      (equal
       (p1963b5-rational-embed (+ q r))
       (p1963b5-add
        (p1963b5-rational-embed q)
        (p1963b5-rational-embed r)))
      (equal
       (p1963b5-rational-embed (* q r))
       (p1963b5-mul
        (p1963b5-rational-embed q)
        (p1963b5-rational-embed r)))
      (iff
       (< q r)
       (p1963b5-less
        (p1963b5-rational-embed q)
        (p1963b5-rational-embed r)))))))

(defun-sk p1963b5-archimedean-p ()
  (forall (x)
    (implies
     (p1963b5-scalar-p x)
     (and
      (natp (p1963b5-arch-bound x))
      (p1963b5-less
       x
       (p1963b5-rational-embed
        (p1963b5-arch-bound x)))))))

(defun p1963b5-real-scalar-structure-p (zero one)
  (and
   (p1963b5-scalar-p zero)
   (p1963b5-scalar-p one)
   (not (equal zero one))
   (p1963b5-less zero one)
   (equal (p1963b5-rational-embed 0) zero)
   (equal (p1963b5-rational-embed 1) one)
   (p1963b5-field-laws-p zero one)
   (p1963b5-order-laws-p zero)
   (p1963b5-rational-embedding-laws-p)
   (p1963b5-archimedean-p)))

(defun-sk p1963b5-sequence-p ()
  (forall (n)
    (implies
     (integerp n)
     (p1963b5-scalar-p (p1963b5-a n)))))

(defun-sk p1963b5-local-bound-p (zero)
  (forall (n k)
    (implies
     (and
      (integerp n)
      (integerp k)
      (<= 1 n)
      (<= n k)
      (<= k (* 2 n)))
     (and
      (p1963b5-less-equal zero (p1963b5-a k))
      (p1963b5-less-equal
       (p1963b5-a k)
       (p1963b5-mul
        (p1963b5-rational-embed 100)
        (p1963b5-a n)))))))

;; This is sum_{n : Fin count} a(n), namely a(0)+...+a(count-1).
(defun p1963b5-partial-sum (count zero)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (p1963b5-add
     (p1963b5-partial-sum (- count 1) zero)
     (p1963b5-a (- count 1)))))

(defun-sk p1963b5-series-tail-p
    (limit epsilon cutoff zero)
  (forall (count)
    (implies
     (and (natp count) (<= cutoff count))
     (p1963b5-less
      (p1963b5-abs
       (p1963b5-sub
        (p1963b5-partial-sum count zero)
        limit)
       zero)
      (p1963b5-rational-embed epsilon)))))

(defun-sk p1963b5-series-cutoff-exists-p
    (limit epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1963b5-series-tail-p
      limit epsilon cutoff zero))))

(defun-sk p1963b5-series-limit-p (limit zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1963b5-series-cutoff-exists-p
      limit epsilon zero))))

(defun-sk p1963b5-series-converges-p (zero)
  (exists (limit)
    (and
     (p1963b5-scalar-p limit)
     (p1963b5-series-limit-p limit zero))))

(defun p1963b5-scaled-term (n)
  (p1963b5-mul
   (p1963b5-rational-embed n)
   (p1963b5-a n)))

(defun-sk p1963b5-target-tail-p
    (epsilon cutoff zero)
  (forall (n)
    (implies
     (and
      (integerp n)
      (<= cutoff n))
     (p1963b5-less
      (p1963b5-abs (p1963b5-scaled-term n) zero)
      (p1963b5-rational-embed epsilon)))))

(defun-sk p1963b5-target-cutoff-exists-p
    (epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1963b5-target-tail-p
      epsilon cutoff zero))))

(defun-sk p1963b5-target-limit-p (zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1963b5-target-cutoff-exists-p epsilon zero))))

(defun putnambench-putnam-1963-b5-statement (zero one)
  (implies
   (and
    (p1963b5-real-scalar-structure-p zero one)
    (p1963b5-sequence-p)
    (p1963b5-local-bound-p zero)
    (p1963b5-series-converges-p zero))
   (p1963b5-target-limit-p zero)))

(value-triple :itpeval-statement-checked)
:q
