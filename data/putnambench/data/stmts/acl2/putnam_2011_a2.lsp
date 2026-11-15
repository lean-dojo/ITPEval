;; Statement-only formalization of PutnamBench artifact putnam_2011_a2:
;; positive sequences satisfying a(0)=b(0)=1 and
;; b(n)=b(n-1)*a(n)-2, with b bounded, make
;; sum_i 1/(a(0)*...*a(i)) converge to 3/2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A and B are arbitrary conservative sequence symbols over an Archimedean
;; ordered field. This is ACL2's native generic-function idiom and preserves
;; arbitrary real-valued sequences without restricting them to APPLY$ codes.
(defstub p2011a2-scalar-p (x) t)
(defstub p2011a2-add-op (x y) t)
(defstub p2011a2-multiply-op (x y) t)
(defstub p2011a2-negate-op (x) t)
(defstub p2011a2-inverse-op (x) t)
(defstub p2011a2-less-op (x y) t)
(defstub p2011a2-rational-embed (q) t)
(defstub p2011a2-arch-bound (x) t)
(defstub p2011a2-a (n) t)
(defstub p2011a2-b (n) t)

(defun p2011a2-add (x y)
  (p2011a2-add-op x y))

(defun p2011a2-mul (x y)
  (p2011a2-multiply-op x y))

(defun p2011a2-neg (x)
  (p2011a2-negate-op x))

(defun p2011a2-inv (x)
  (p2011a2-inverse-op x))

(defun p2011a2-sub (x y)
  (p2011a2-add x (p2011a2-neg y)))

(defun p2011a2-less (x y)
  (if (p2011a2-less-op x y) t nil))

(defun p2011a2-less-equal (x y)
  (not (p2011a2-less y x)))

(defun p2011a2-abs (x zero)
  (if (p2011a2-less x zero)
      (p2011a2-neg x)
    x))

(defun-sk p2011a2-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p2011a2-scalar-p x)
      (p2011a2-scalar-p y)
      (p2011a2-scalar-p z))
     (and
      (p2011a2-scalar-p (p2011a2-add x y))
      (p2011a2-scalar-p (p2011a2-mul x y))
      (p2011a2-scalar-p (p2011a2-neg x))
      (implies
       (not (equal x zero))
       (p2011a2-scalar-p (p2011a2-inv x)))
      (equal (p2011a2-add (p2011a2-add x y) z)
             (p2011a2-add x (p2011a2-add y z)))
      (equal (p2011a2-add x y)
             (p2011a2-add y x))
      (equal (p2011a2-add x zero) x)
      (equal (p2011a2-add x (p2011a2-neg x)) zero)
      (equal (p2011a2-mul (p2011a2-mul x y) z)
             (p2011a2-mul x (p2011a2-mul y z)))
      (equal (p2011a2-mul x y)
             (p2011a2-mul y x))
      (equal (p2011a2-mul x one) x)
      (implies
       (not (equal x zero))
       (equal (p2011a2-mul x (p2011a2-inv x)) one))
      (equal
       (p2011a2-mul x (p2011a2-add y z))
       (p2011a2-add
        (p2011a2-mul x y)
        (p2011a2-mul x z)))))))

(defun-sk p2011a2-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p2011a2-scalar-p x)
      (p2011a2-scalar-p y)
      (p2011a2-scalar-p z))
     (and
      (not (p2011a2-less x x))
      (or
       (equal x y)
       (p2011a2-less x y)
       (p2011a2-less y x))
      (implies
       (and
        (p2011a2-less x y)
        (p2011a2-less y z))
       (p2011a2-less x z))
      (implies
       (p2011a2-less x y)
       (p2011a2-less
        (p2011a2-add x z)
        (p2011a2-add y z)))
      (implies
       (and
        (p2011a2-less zero x)
        (p2011a2-less zero y))
       (p2011a2-less zero (p2011a2-mul x y)))))))

(defun-sk p2011a2-rational-embedding-laws-p ()
  (forall (q r)
    (implies
     (and (rationalp q) (rationalp r))
     (and
      (p2011a2-scalar-p (p2011a2-rational-embed q))
      (equal
       (p2011a2-rational-embed (+ q r))
       (p2011a2-add
        (p2011a2-rational-embed q)
        (p2011a2-rational-embed r)))
      (equal
       (p2011a2-rational-embed (* q r))
       (p2011a2-mul
        (p2011a2-rational-embed q)
        (p2011a2-rational-embed r)))
      (iff
       (< q r)
       (p2011a2-less
        (p2011a2-rational-embed q)
        (p2011a2-rational-embed r)))))))

(defun-sk p2011a2-archimedean-p ()
  (forall (x)
    (implies
     (p2011a2-scalar-p x)
     (and
      (natp (p2011a2-arch-bound x))
      (p2011a2-less
       x
       (p2011a2-rational-embed
        (p2011a2-arch-bound x)))))))

(defun p2011a2-real-scalar-structure-p (zero one)
  (and
   (p2011a2-scalar-p zero)
   (p2011a2-scalar-p one)
   (not (equal zero one))
   (p2011a2-less zero one)
   (equal (p2011a2-rational-embed 0) zero)
   (equal (p2011a2-rational-embed 1) one)
   (p2011a2-field-laws-p zero one)
   (p2011a2-order-laws-p zero)
   (p2011a2-rational-embedding-laws-p)
   (p2011a2-archimedean-p)))

(defun-sk p2011a2-positive-sequences-p (zero)
  (forall (n)
    (implies
     (natp n)
     (and
      (p2011a2-scalar-p (p2011a2-a n))
      (p2011a2-scalar-p (p2011a2-b n))
      (p2011a2-less zero (p2011a2-a n))
      (p2011a2-less zero (p2011a2-b n))))))

(defun-sk p2011a2-recurrence-p ()
  (forall (n)
    (implies
     (and (natp n) (<= 1 n))
     (equal
      (p2011a2-b n)
      (p2011a2-sub
       (p2011a2-mul
        (p2011a2-b (- n 1))
        (p2011a2-a n))
       (p2011a2-rational-embed 2))))))

(defun-sk p2011a2-bound-p (bound zero)
  (forall (n)
    (implies
     (natp n)
     (p2011a2-less-equal
      (p2011a2-abs (p2011a2-b n) zero)
      bound))))

(defun-sk p2011a2-bounded-p (zero)
  (exists (bound)
    (and
     (p2011a2-scalar-p bound)
     (p2011a2-bound-p bound zero))))

;; Product over Fin terms: a(0)*...*a(terms-1).
(defun p2011a2-product-prefix (terms one)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      one
    (p2011a2-mul
     (p2011a2-product-prefix (- terms 1) one)
     (p2011a2-a (- terms 1)))))

;; Sum over i : Fin terms of 1/(product over j : Fin (i+1) of a(j)).
(defun p2011a2-partial-sum (terms zero one)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (p2011a2-add
     (p2011a2-partial-sum (- terms 1) zero one)
     (p2011a2-inv
      (p2011a2-product-prefix terms one)))))

(defun-sk p2011a2-limit-tail-p
    (epsilon cutoff zero one)
  (forall (terms)
    (implies
     (and (natp terms) (<= cutoff terms))
     (p2011a2-less
      (p2011a2-abs
       (p2011a2-sub
        (p2011a2-partial-sum terms zero one)
        (p2011a2-rational-embed 3/2))
       zero)
      (p2011a2-rational-embed epsilon)))))

(defun-sk p2011a2-limit-cutoff-exists-p
    (epsilon zero one)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p2011a2-limit-tail-p
      epsilon cutoff zero one))))

(defun-sk p2011a2-converges-to-three-halves-p
    (zero one)
  (forall (epsilon)
    (implies
     (and (rationalp epsilon) (< 0 epsilon))
     (p2011a2-limit-cutoff-exists-p
      epsilon zero one))))

(defun putnambench-putnam-2011-a2-statement (zero one)
  (implies
   (and
    (p2011a2-real-scalar-structure-p zero one)
    (p2011a2-positive-sequences-p zero)
    (equal (p2011a2-a 0) one)
    (equal (p2011a2-b 0) one)
    (p2011a2-recurrence-p)
    (p2011a2-bounded-p zero))
   (p2011a2-converges-to-three-halves-p zero one)))

(value-triple :itpeval-statement-checked)
:q
