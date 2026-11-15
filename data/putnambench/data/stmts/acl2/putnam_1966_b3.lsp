;; Statement-only formalization of PutnamBench artifact putnam_1966_b3:
;; convergence of sum 1/p(n) for a positive sequence implies convergence of
;; sum n^2*p(n)/(p(1)+...+p(n))^2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; P is an arbitrary conservative sequence symbol. The scalar interface is an
;; Archimedean ordered field with a rational embedding, so the epsilon limits
;; state the source theorem for arbitrary real sequences without APPLY$ or a
;; rational-valued restriction.
(defstub p1966b3-scalar-p (x) t)
(defstub p1966b3-add-op (x y) t)
(defstub p1966b3-multiply-op (x y) t)
(defstub p1966b3-negate-op (x) t)
(defstub p1966b3-inverse-op (x) t)
(defstub p1966b3-less-op (x y) t)
(defstub p1966b3-rational-embed (q) t)
(defstub p1966b3-arch-bound (x) t)
(defstub p1966b3-p (n) t)

(defun p1966b3-add (x y)
  (p1966b3-add-op x y))

(defun p1966b3-mul (x y)
  (p1966b3-multiply-op x y))

(defun p1966b3-neg (x)
  (p1966b3-negate-op x))

(defun p1966b3-inv (x)
  (p1966b3-inverse-op x))

(defun p1966b3-sub (x y)
  (p1966b3-add x (p1966b3-neg y)))

(defun p1966b3-div (x y)
  (p1966b3-mul x (p1966b3-inv y)))

(defun p1966b3-less (x y)
  (if (p1966b3-less-op x y) t nil))

(defun p1966b3-abs (x zero)
  (if (p1966b3-less x zero)
      (p1966b3-neg x)
    x))

(defun-sk p1966b3-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1966b3-scalar-p x)
      (p1966b3-scalar-p y)
      (p1966b3-scalar-p z))
     (and
      (p1966b3-scalar-p (p1966b3-add x y))
      (p1966b3-scalar-p (p1966b3-mul x y))
      (p1966b3-scalar-p (p1966b3-neg x))
      (implies
       (not (equal x zero))
       (p1966b3-scalar-p (p1966b3-inv x)))
      (equal (p1966b3-add (p1966b3-add x y) z)
             (p1966b3-add x (p1966b3-add y z)))
      (equal (p1966b3-add x y)
             (p1966b3-add y x))
      (equal (p1966b3-add x zero) x)
      (equal (p1966b3-add x (p1966b3-neg x)) zero)
      (equal (p1966b3-mul (p1966b3-mul x y) z)
             (p1966b3-mul x (p1966b3-mul y z)))
      (equal (p1966b3-mul x y)
             (p1966b3-mul y x))
      (equal (p1966b3-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1966b3-mul x (p1966b3-inv x)) one))
      (equal
       (p1966b3-mul x (p1966b3-add y z))
       (p1966b3-add
        (p1966b3-mul x y)
        (p1966b3-mul x z)))))))

(defun-sk p1966b3-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1966b3-scalar-p x)
      (p1966b3-scalar-p y)
      (p1966b3-scalar-p z))
     (and
      (not (p1966b3-less x x))
      (or
       (equal x y)
       (p1966b3-less x y)
       (p1966b3-less y x))
      (implies
       (and (p1966b3-less x y)
            (p1966b3-less y z))
       (p1966b3-less x z))
      (implies
       (p1966b3-less x y)
       (p1966b3-less
        (p1966b3-add x z)
        (p1966b3-add y z)))
      (implies
       (and
        (p1966b3-less zero x)
        (p1966b3-less zero y))
       (p1966b3-less zero (p1966b3-mul x y)))))))

(defun-sk p1966b3-rational-embedding-laws-p ()
  (forall (q r)
    (implies
     (and (rationalp q) (rationalp r))
     (and
      (p1966b3-scalar-p (p1966b3-rational-embed q))
      (equal
       (p1966b3-rational-embed (+ q r))
       (p1966b3-add
        (p1966b3-rational-embed q)
        (p1966b3-rational-embed r)))
      (equal
       (p1966b3-rational-embed (* q r))
       (p1966b3-mul
        (p1966b3-rational-embed q)
        (p1966b3-rational-embed r)))
      (iff
       (< q r)
       (p1966b3-less
        (p1966b3-rational-embed q)
        (p1966b3-rational-embed r)))))))

(defun-sk p1966b3-archimedean-p ()
  (forall (x)
    (implies
     (p1966b3-scalar-p x)
     (and
      (natp (p1966b3-arch-bound x))
      (p1966b3-less
       x
       (p1966b3-rational-embed
        (p1966b3-arch-bound x)))))))

(defun p1966b3-real-scalar-structure-p (zero one)
  (and
   (p1966b3-scalar-p zero)
   (p1966b3-scalar-p one)
   (not (equal zero one))
   (p1966b3-less zero one)
   (equal (p1966b3-rational-embed 0) zero)
   (equal (p1966b3-rational-embed 1) one)
   (p1966b3-field-laws-p zero one)
   (p1966b3-order-laws-p zero)
   (p1966b3-rational-embedding-laws-p)
   (p1966b3-archimedean-p)))

(defun-sk p1966b3-positive-sequence-p (zero)
  (forall (n)
    (implies
     (natp n)
     (and
      (p1966b3-scalar-p (p1966b3-p n))
      (p1966b3-less zero (p1966b3-p n))))))

;; Sum over Finset.Icc 1 n.
(defun p1966b3-p-prefix (n zero)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1966b3-add
     (p1966b3-p-prefix (- n 1) zero)
     (p1966b3-p n))))

(defun p1966b3-reciprocal-prefix (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1966b3-add
     (p1966b3-reciprocal-prefix (- n 1) zero one)
     (p1966b3-div one (p1966b3-p n)))))

(defun p1966b3-target-term (n zero)
  (let* ((n-value (p1966b3-rational-embed n))
         (prefix (p1966b3-p-prefix n zero)))
    (p1966b3-div
     (p1966b3-mul
      (p1966b3-p n)
      (p1966b3-mul n-value n-value))
     (p1966b3-mul prefix prefix))))

(defun p1966b3-target-prefix (n zero)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1966b3-add
     (p1966b3-target-prefix (- n 1) zero)
     (p1966b3-target-term n zero))))

(defun-sk p1966b3-source-tail-p
    (limit epsilon cutoff zero one)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1966b3-less
      (p1966b3-abs
       (p1966b3-sub
        (p1966b3-reciprocal-prefix n zero one)
        limit)
       zero)
      (p1966b3-rational-embed epsilon)))))

(defun-sk p1966b3-source-cutoff-exists-p
    (limit epsilon zero one)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1966b3-source-tail-p
      limit epsilon cutoff zero one))))

(defun-sk p1966b3-source-limit-p (limit zero one)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1966b3-source-cutoff-exists-p
      limit epsilon zero one))))

(defun-sk p1966b3-source-converges-p (zero one)
  (exists (limit)
    (and
     (p1966b3-scalar-p limit)
     (p1966b3-source-limit-p limit zero one))))

(defun-sk p1966b3-target-tail-p
    (limit epsilon cutoff zero)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1966b3-less
      (p1966b3-abs
       (p1966b3-sub
        (p1966b3-target-prefix n zero)
        limit)
       zero)
      (p1966b3-rational-embed epsilon)))))

(defun-sk p1966b3-target-cutoff-exists-p
    (limit epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1966b3-target-tail-p
      limit epsilon cutoff zero))))

(defun-sk p1966b3-target-limit-p (limit zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1966b3-target-cutoff-exists-p
      limit epsilon zero))))

(defun-sk p1966b3-target-converges-p (zero)
  (exists (limit)
    (and
     (p1966b3-scalar-p limit)
     (p1966b3-target-limit-p limit zero))))

;; Completeness is needed only after the target partial sums have been shown
;; Cauchy. This explicit instance states that real completeness step without
;; assuming the theorem's convergence conclusion.
(defun-sk p1966b3-target-cauchy-tail-p
    (epsilon cutoff zero)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (<= cutoff m)
      (<= cutoff n))
     (p1966b3-less
      (p1966b3-abs
       (p1966b3-sub
        (p1966b3-target-prefix m zero)
        (p1966b3-target-prefix n zero))
       zero)
      (p1966b3-rational-embed epsilon)))))

(defun-sk p1966b3-target-cauchy-cutoff-exists-p
    (epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1966b3-target-cauchy-tail-p
      epsilon cutoff zero))))

(defun-sk p1966b3-target-cauchy-p (zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1966b3-target-cauchy-cutoff-exists-p
      epsilon zero))))

(defun p1966b3-target-completeness-p (zero)
  (implies
   (p1966b3-target-cauchy-p zero)
   (p1966b3-target-converges-p zero)))

(defun putnambench-putnam-1966-b3-statement (zero one)
  (implies
   (and
    (p1966b3-real-scalar-structure-p zero one)
    (p1966b3-positive-sequence-p zero)
    (p1966b3-source-converges-p zero one)
    (p1966b3-target-completeness-p zero))
   (p1966b3-target-converges-p zero)))

(value-triple :itpeval-statement-checked)
:q
