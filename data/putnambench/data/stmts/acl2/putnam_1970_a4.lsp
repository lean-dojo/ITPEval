;; Statement-only formalization of PutnamBench artifact putnam_1970_a4:
;; if x(n+2)-x(n) tends to zero, then
;; (x(n+1)-x(n))/(n+1) tends to zero. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; X is an arbitrary conservative sequence symbol over an Archimedean ordered
;; field. Positive rational tolerances are cofinal in its order topology, so
;; the epsilon definitions below preserve arbitrary real-valued sequences
;; instead of restricting their values to ACL2 rationals or APPLY$ codes.
(defstub p1970a4-scalar-p (x) t)
(defstub p1970a4-add-op (x y) t)
(defstub p1970a4-multiply-op (x y) t)
(defstub p1970a4-negate-op (x) t)
(defstub p1970a4-inverse-op (x) t)
(defstub p1970a4-less-op (x y) t)
(defstub p1970a4-rational-embed (q) t)
(defstub p1970a4-arch-bound (x) t)
(defstub p1970a4-x (n) t)

(defun p1970a4-add (x y)
  (p1970a4-add-op x y))

(defun p1970a4-mul (x y)
  (p1970a4-multiply-op x y))

(defun p1970a4-neg (x)
  (p1970a4-negate-op x))

(defun p1970a4-inv (x)
  (p1970a4-inverse-op x))

(defun p1970a4-sub (x y)
  (p1970a4-add x (p1970a4-neg y)))

(defun p1970a4-less (x y)
  (if (p1970a4-less-op x y) t nil))

(defun p1970a4-abs (x zero)
  (if (p1970a4-less x zero)
      (p1970a4-neg x)
    x))

(defun-sk p1970a4-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1970a4-scalar-p x)
      (p1970a4-scalar-p y)
      (p1970a4-scalar-p z))
     (and
      (p1970a4-scalar-p (p1970a4-add x y))
      (p1970a4-scalar-p (p1970a4-mul x y))
      (p1970a4-scalar-p (p1970a4-neg x))
      (implies
       (not (equal x zero))
       (p1970a4-scalar-p (p1970a4-inv x)))
      (equal (p1970a4-add (p1970a4-add x y) z)
             (p1970a4-add x (p1970a4-add y z)))
      (equal (p1970a4-add x y)
             (p1970a4-add y x))
      (equal (p1970a4-add x zero) x)
      (equal (p1970a4-add x (p1970a4-neg x)) zero)
      (equal (p1970a4-mul (p1970a4-mul x y) z)
             (p1970a4-mul x (p1970a4-mul y z)))
      (equal (p1970a4-mul x y)
             (p1970a4-mul y x))
      (equal (p1970a4-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p1970a4-mul x (p1970a4-inv x)) one))
      (equal
       (p1970a4-mul x (p1970a4-add y z))
       (p1970a4-add (p1970a4-mul x y)
                    (p1970a4-mul x z)))))))

(defun-sk p1970a4-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1970a4-scalar-p x)
      (p1970a4-scalar-p y)
      (p1970a4-scalar-p z))
     (and
      (not (p1970a4-less x x))
      (or
       (equal x y)
       (p1970a4-less x y)
       (p1970a4-less y x))
      (implies
       (and
        (p1970a4-less x y)
        (p1970a4-less y z))
       (p1970a4-less x z))
      (implies
       (p1970a4-less x y)
       (p1970a4-less
        (p1970a4-add x z)
        (p1970a4-add y z)))
      (implies
       (and
        (p1970a4-less zero x)
        (p1970a4-less zero y))
       (p1970a4-less zero (p1970a4-mul x y)))))))

(defun-sk p1970a4-rational-embedding-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (p1970a4-scalar-p (p1970a4-rational-embed a))
      (equal
       (p1970a4-rational-embed (+ a b))
       (p1970a4-add
        (p1970a4-rational-embed a)
        (p1970a4-rational-embed b)))
      (equal
       (p1970a4-rational-embed (* a b))
       (p1970a4-mul
        (p1970a4-rational-embed a)
        (p1970a4-rational-embed b)))
      (iff
       (< a b)
       (p1970a4-less
        (p1970a4-rational-embed a)
        (p1970a4-rational-embed b)))))))

(defun-sk p1970a4-archimedean-p ()
  (forall (x)
    (implies
     (p1970a4-scalar-p x)
     (and
      (natp (p1970a4-arch-bound x))
      (p1970a4-less
       x
       (p1970a4-rational-embed
        (p1970a4-arch-bound x)))))))

(defun p1970a4-ordered-field-with-rationals-p (zero one)
  (and
   (p1970a4-scalar-p zero)
   (p1970a4-scalar-p one)
   (not (equal zero one))
   (p1970a4-less zero one)
   (equal (p1970a4-rational-embed 0) zero)
   (equal (p1970a4-rational-embed 1) one)
   (p1970a4-field-laws-p zero one)
   (p1970a4-order-laws-p zero)
   (p1970a4-rational-embedding-laws-p)
   (p1970a4-archimedean-p)))

(defun-sk p1970a4-sequence-p ()
  (forall (n)
    (implies
     (natp n)
     (p1970a4-scalar-p (p1970a4-x n)))))

(defun p1970a4-source-value (n)
  (p1970a4-sub
   (p1970a4-x (+ n 2))
   (p1970a4-x n)))

(defun p1970a4-target-value (n)
  (p1970a4-mul
   (p1970a4-sub
    (p1970a4-x (+ n 1))
    (p1970a4-x n))
   (p1970a4-inv
    (p1970a4-rational-embed (+ n 1)))))

(defun-sk p1970a4-source-tail-p
    (epsilon cutoff zero)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1970a4-less
      (p1970a4-abs (p1970a4-source-value n) zero)
      (p1970a4-rational-embed epsilon)))))

(defun-sk p1970a4-source-cutoff-exists-p
    (epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1970a4-source-tail-p epsilon cutoff zero))))

(defun-sk p1970a4-source-limit-p (zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1970a4-source-cutoff-exists-p
      epsilon zero))))

(defun-sk p1970a4-target-tail-p
    (epsilon cutoff zero)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1970a4-less
      (p1970a4-abs (p1970a4-target-value n) zero)
      (p1970a4-rational-embed epsilon)))))

(defun-sk p1970a4-target-cutoff-exists-p
    (epsilon zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1970a4-target-tail-p epsilon cutoff zero))))

(defun-sk p1970a4-target-limit-p (zero)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p1970a4-target-cutoff-exists-p
      epsilon zero))))

(defun putnambench-putnam-1970-a4-statement (zero one)
  (implies
   (and
    (p1970a4-ordered-field-with-rationals-p zero one)
    (p1970a4-sequence-p)
    (p1970a4-source-limit-p zero))
   (p1970a4-target-limit-p zero)))

(value-triple :itpeval-statement-checked)
:q
