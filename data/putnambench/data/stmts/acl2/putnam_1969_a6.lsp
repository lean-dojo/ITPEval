;; Statement-only formalization of PutnamBench artifact putnam_1969_a6:
;; if y(n) = x(n-1) + 2*x(n) from index two onward and y converges, then x
;; converges. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; X and Y are arbitrary conservative sequence symbols. Scalar values live in
;; an Archimedean ordered field with its rational embedding. Positive rational
;; tolerances form a neighborhood basis at zero in this setting, so the
;; epsilon formulation is equivalent to the source's real convergence while
;; avoiding both rational-valued-sequence and APPLY$ restrictions.
(defstub p1969a6-scalar-p (x) t)
(defstub p1969a6-add-op (x y) t)
(defstub p1969a6-multiply-op (x y) t)
(defstub p1969a6-negate-op (x) t)
(defstub p1969a6-inverse-op (x) t)
(defstub p1969a6-less-op (x y) t)
(defstub p1969a6-rational-embed (q) t)
(defstub p1969a6-arch-bound (x) t)
(defstub p1969a6-x (n) t)
(defstub p1969a6-y (n) t)

(defun p1969a6-add (x y)
  (p1969a6-add-op x y))

(defun p1969a6-mul (x y)
  (p1969a6-multiply-op x y))

(defun p1969a6-neg (x)
  (p1969a6-negate-op x))

(defun p1969a6-inv (x)
  (p1969a6-inverse-op x))

(defun p1969a6-sub (x y)
  (p1969a6-add x (p1969a6-neg y)))

(defun p1969a6-less (x y)
  (if (p1969a6-less-op x y) t nil))

(defun p1969a6-abs (x zero)
  (if (p1969a6-less x zero)
      (p1969a6-neg x)
    x))

(defun-sk p1969a6-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1969a6-scalar-p x)
      (p1969a6-scalar-p y)
      (p1969a6-scalar-p z))
     (and
      (p1969a6-scalar-p (p1969a6-add x y))
      (p1969a6-scalar-p (p1969a6-mul x y))
      (p1969a6-scalar-p (p1969a6-neg x))
      (implies
       (not (equal x zero))
       (p1969a6-scalar-p (p1969a6-inv x)))
      (equal (p1969a6-add (p1969a6-add x y) z)
             (p1969a6-add x (p1969a6-add y z)))
      (equal (p1969a6-add x y)
             (p1969a6-add y x))
      (equal (p1969a6-add x zero) x)
      (equal (p1969a6-add x (p1969a6-neg x)) zero)
      (equal (p1969a6-mul (p1969a6-mul x y) z)
             (p1969a6-mul x (p1969a6-mul y z)))
      (equal (p1969a6-mul x y)
             (p1969a6-mul y x))
      (equal (p1969a6-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1969a6-mul x (p1969a6-inv x)) one))
      (equal
       (p1969a6-mul x (p1969a6-add y z))
       (p1969a6-add (p1969a6-mul x y)
                    (p1969a6-mul x z)))))))

(defun-sk p1969a6-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1969a6-scalar-p x)
      (p1969a6-scalar-p y)
      (p1969a6-scalar-p z))
     (and
      (not (p1969a6-less x x))
      (or
       (equal x y)
       (p1969a6-less x y)
       (p1969a6-less y x))
      (implies
       (and
        (p1969a6-less x y)
        (p1969a6-less y z))
       (p1969a6-less x z))
      (implies
       (p1969a6-less x y)
       (p1969a6-less
        (p1969a6-add x z)
        (p1969a6-add y z)))
      (implies
       (and
        (p1969a6-less zero x)
        (p1969a6-less zero y))
       (p1969a6-less zero (p1969a6-mul x y)))))))

(defun-sk p1969a6-rational-embedding-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (p1969a6-scalar-p (p1969a6-rational-embed a))
      (equal
       (p1969a6-rational-embed (+ a b))
       (p1969a6-add
        (p1969a6-rational-embed a)
        (p1969a6-rational-embed b)))
      (equal
       (p1969a6-rational-embed (* a b))
       (p1969a6-mul
        (p1969a6-rational-embed a)
        (p1969a6-rational-embed b)))
      (iff
       (< a b)
       (p1969a6-less
        (p1969a6-rational-embed a)
        (p1969a6-rational-embed b)))))))

(defun-sk p1969a6-archimedean-p ()
  (forall (x)
    (implies
     (p1969a6-scalar-p x)
     (and
      (natp (p1969a6-arch-bound x))
      (p1969a6-less
       x
       (p1969a6-rational-embed
        (p1969a6-arch-bound x)))))))

(defun p1969a6-ordered-field-with-rationals-p (zero one)
  (and
   (p1969a6-scalar-p zero)
   (p1969a6-scalar-p one)
   (not (equal zero one))
   (p1969a6-less zero one)
   (equal (p1969a6-rational-embed 0) zero)
   (equal (p1969a6-rational-embed 1) one)
   (p1969a6-field-laws-p zero one)
   (p1969a6-order-laws-p zero)
   (p1969a6-rational-embedding-laws-p)
   (p1969a6-archimedean-p)))

(defun-sk p1969a6-sequences-p ()
  (forall (n)
    (implies
     (natp n)
     (and
      (p1969a6-scalar-p (p1969a6-x n))
      (p1969a6-scalar-p (p1969a6-y n))))))

(defun-sk p1969a6-recurrence-p (one)
  (forall (n)
    (implies
     (and (natp n) (<= 2 n))
     (equal
      (p1969a6-y n)
      (p1969a6-add
       (p1969a6-x (1- n))
       (p1969a6-mul
        (p1969a6-add one one)
        (p1969a6-x n)))))))

(defun-sk p1969a6-y-tail-p
    (limit epsilon cutoff zero)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1969a6-less
      (p1969a6-abs
       (p1969a6-sub (p1969a6-y n) limit)
       zero)
      (p1969a6-rational-embed epsilon)))))

(defun-sk p1969a6-y-cutoff-exists-p
    (limit epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1969a6-y-tail-p limit epsilon cutoff zero))))

(defun-sk p1969a6-y-limit-p (limit zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1969a6-y-cutoff-exists-p
      limit epsilon zero))))

(defun-sk p1969a6-y-converges-p (zero)
  (exists (limit)
    (and
     (p1969a6-scalar-p limit)
     (p1969a6-y-limit-p limit zero))))

(defun-sk p1969a6-x-tail-p
    (limit epsilon cutoff zero)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1969a6-less
      (p1969a6-abs
       (p1969a6-sub (p1969a6-x n) limit)
       zero)
      (p1969a6-rational-embed epsilon)))))

(defun-sk p1969a6-x-cutoff-exists-p
    (limit epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1969a6-x-tail-p limit epsilon cutoff zero))))

(defun-sk p1969a6-x-limit-p (limit zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1969a6-x-cutoff-exists-p
      limit epsilon zero))))

(defun-sk p1969a6-x-converges-p (zero)
  (exists (limit)
    (and
     (p1969a6-scalar-p limit)
     (p1969a6-x-limit-p limit zero))))

(defun putnambench-putnam-1969-a6-statement (zero one)
  (implies
   (and
    (p1969a6-ordered-field-with-rationals-p zero one)
    (p1969a6-sequences-p)
    (p1969a6-recurrence-p one)
    (p1969a6-y-converges-p zero))
   (p1969a6-x-converges-p zero)))

(value-triple :itpeval-statement-checked)
:q
