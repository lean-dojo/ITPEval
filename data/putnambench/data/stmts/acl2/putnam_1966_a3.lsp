;; Statement-only formalization of PutnamBench artifact putnam_1966_a3:
;; if 0 < x(1) < 1 and x(n+1) = x(n)(1-x(n)), then n*x(n) tends
;; to 1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2's conservative generic-function idiom represents an arbitrary real
;; sequence without restricting it to an APPLY$-recognizable function object.
;; The explicit Archimedean ordered-field interface is sufficient for this
;; algebraic recurrence; positive rational tolerances characterize its real
;; limit exactly.
(defstub p1966a3-scalar-p (x) t)
(defstub p1966a3-add-op (x y) t)
(defstub p1966a3-multiply-op (x y) t)
(defstub p1966a3-negate-op (x) t)
(defstub p1966a3-less-op (x y) t)
(defstub p1966a3-rational-embed (q) t)
(defstub p1966a3-arch-bound (x) t)
(defstub p1966a3-x (n) t)

(defun p1966a3-add (x y)
  (p1966a3-add-op x y))

(defun p1966a3-mul (x y)
  (p1966a3-multiply-op x y))

(defun p1966a3-neg (x)
  (p1966a3-negate-op x))

(defun p1966a3-sub (x y)
  (p1966a3-add x (p1966a3-neg y)))

(defun p1966a3-less (x y)
  (if (p1966a3-less-op x y) t nil))

(defun p1966a3-abs (x zero)
  (if (p1966a3-less x zero)
      (p1966a3-neg x)
    x))

(defun-sk p1966a3-ring-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1966a3-scalar-p x)
      (p1966a3-scalar-p y)
      (p1966a3-scalar-p z))
     (and
      (p1966a3-scalar-p (p1966a3-add x y))
      (p1966a3-scalar-p (p1966a3-mul x y))
      (p1966a3-scalar-p (p1966a3-neg x))
      (equal (p1966a3-add (p1966a3-add x y) z)
             (p1966a3-add x (p1966a3-add y z)))
      (equal (p1966a3-add x y)
             (p1966a3-add y x))
      (equal (p1966a3-add x zero) x)
      (equal (p1966a3-add x (p1966a3-neg x)) zero)
      (equal (p1966a3-mul (p1966a3-mul x y) z)
             (p1966a3-mul x (p1966a3-mul y z)))
      (equal (p1966a3-mul x y)
             (p1966a3-mul y x))
      (equal (p1966a3-mul x one) x)
      (equal
       (p1966a3-mul x (p1966a3-add y z))
       (p1966a3-add (p1966a3-mul x y)
                    (p1966a3-mul x z)))))))

(defun-sk p1966a3-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1966a3-scalar-p x)
      (p1966a3-scalar-p y)
      (p1966a3-scalar-p z))
     (and
      (not (p1966a3-less x x))
      (or
       (equal x y)
       (p1966a3-less x y)
       (p1966a3-less y x))
      (implies
       (and
        (p1966a3-less x y)
        (p1966a3-less y z))
       (p1966a3-less x z))
      (implies
       (p1966a3-less x y)
       (p1966a3-less
        (p1966a3-add x z)
        (p1966a3-add y z)))
      (implies
       (and
        (p1966a3-less zero x)
        (p1966a3-less zero y))
       (p1966a3-less zero (p1966a3-mul x y)))))))

(defun-sk p1966a3-rational-embedding-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (p1966a3-scalar-p (p1966a3-rational-embed a))
      (equal
       (p1966a3-rational-embed (+ a b))
       (p1966a3-add
        (p1966a3-rational-embed a)
        (p1966a3-rational-embed b)))
      (equal
       (p1966a3-rational-embed (* a b))
       (p1966a3-mul
        (p1966a3-rational-embed a)
        (p1966a3-rational-embed b)))
      (iff
       (< a b)
       (p1966a3-less
        (p1966a3-rational-embed a)
        (p1966a3-rational-embed b)))))))

(defun-sk p1966a3-archimedean-p ()
  (forall (x)
    (implies
     (p1966a3-scalar-p x)
     (and
      (natp (p1966a3-arch-bound x))
      (p1966a3-less
       x
       (p1966a3-rational-embed
        (p1966a3-arch-bound x)))))))

(defun p1966a3-real-scalar-structure-p (zero one)
  (and
   (p1966a3-scalar-p zero)
   (p1966a3-scalar-p one)
   (not (equal zero one))
   (p1966a3-less zero one)
   (equal (p1966a3-rational-embed 0) zero)
   (equal (p1966a3-rational-embed 1) one)
   (p1966a3-ring-laws-p zero one)
   (p1966a3-order-laws-p zero)
   (p1966a3-rational-embedding-laws-p)
   (p1966a3-archimedean-p)))

(defun-sk p1966a3-sequence-p ()
  (forall (n)
    (implies
     (natp n)
     (p1966a3-scalar-p (p1966a3-x n)))))

(defun-sk p1966a3-recurrence-p (one)
  (forall (n)
    (implies
     (and (natp n) (<= 1 n))
     (equal
      (p1966a3-x (+ n 1))
      (p1966a3-mul
       (p1966a3-x n)
       (p1966a3-sub one (p1966a3-x n)))))))

(defun p1966a3-scaled-value (n)
  (p1966a3-mul
   (p1966a3-rational-embed n)
   (p1966a3-x n)))

(defun-sk p1966a3-limit-tail-p
    (epsilon cutoff zero one)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1966a3-less
      (p1966a3-abs
       (p1966a3-sub (p1966a3-scaled-value n) one)
       zero)
      (p1966a3-rational-embed epsilon)))))

(defun-sk p1966a3-limit-cutoff-exists-p
    (epsilon zero one)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1966a3-limit-tail-p
      epsilon cutoff zero one))))

(defun-sk p1966a3-converges-to-one-p (zero one)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1966a3-limit-cutoff-exists-p
      epsilon zero one))))

(defun putnambench-putnam-1966-a3-statement (zero one)
  (implies
   (and
    (p1966a3-real-scalar-structure-p zero one)
    (p1966a3-sequence-p)
    (p1966a3-less zero (p1966a3-x 1))
    (p1966a3-less (p1966a3-x 1) one)
    (p1966a3-recurrence-p one))
   (p1966a3-converges-to-one-p zero one)))

(value-triple :itpeval-statement-checked)
:q
