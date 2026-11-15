;; Statement-only formalization of PutnamBench artifact putnam_1994_a1:
;; if 0 < a(n) <= a(2n)+a(2n+1) for n >= 1, then the partial sums
;; of a diverge to positive infinity. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source sequence is represented by an arbitrary conservative ACL2
;; function symbol. Both directions of the Archimedean property are explicit:
;; rational upper bounds are cofinal, and every positive scalar dominates
;; some positive reciprocal integer. The second clause rules out positive
;; infinitesimals, which would make the source conclusion false.
(defstub p1994a1-scalar-p (x) t)
(defstub p1994a1-add-op (x y) t)
(defstub p1994a1-negate-op (x) t)
(defstub p1994a1-less-op (x y) t)
(defstub p1994a1-rational-embed (q) t)
(defstub p1994a1-arch-bound (x) t)
(defstub p1994a1-reciprocal-bound (x) t)
(defstub p1994a1-a (n) t)

(defun p1994a1-add (x y)
  (p1994a1-add-op x y))

(defun p1994a1-neg (x)
  (p1994a1-negate-op x))

(defun p1994a1-less (x y)
  (if (p1994a1-less-op x y) t nil))

(defun p1994a1-less-equal (x y)
  (not (p1994a1-less y x)))

(defun-sk p1994a1-additive-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1994a1-scalar-p x)
      (p1994a1-scalar-p y)
      (p1994a1-scalar-p z))
     (and
      (p1994a1-scalar-p (p1994a1-add x y))
      (p1994a1-scalar-p (p1994a1-neg x))
      (equal (p1994a1-add (p1994a1-add x y) z)
             (p1994a1-add x (p1994a1-add y z)))
      (equal (p1994a1-add x y)
             (p1994a1-add y x))
      (equal (p1994a1-add x zero) x)
      (equal (p1994a1-add x (p1994a1-neg x)) zero)))))

(defun-sk p1994a1-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p1994a1-scalar-p x)
      (p1994a1-scalar-p y)
      (p1994a1-scalar-p z))
     (and
      (not (p1994a1-less x x))
      (or
       (equal x y)
       (p1994a1-less x y)
       (p1994a1-less y x))
      (implies
       (and
        (p1994a1-less x y)
        (p1994a1-less y z))
       (p1994a1-less x z))
      (implies
       (p1994a1-less x y)
       (p1994a1-less
        (p1994a1-add x z)
        (p1994a1-add y z)))))))

(defun-sk p1994a1-rational-embedding-laws-p ()
  (forall (a b)
    (implies
     (and (rationalp a) (rationalp b))
     (and
      (p1994a1-scalar-p (p1994a1-rational-embed a))
      (equal
       (p1994a1-rational-embed (+ a b))
       (p1994a1-add
        (p1994a1-rational-embed a)
        (p1994a1-rational-embed b)))
      (iff
       (< a b)
       (p1994a1-less
        (p1994a1-rational-embed a)
        (p1994a1-rational-embed b)))))))

(defun-sk p1994a1-archimedean-p ()
  (forall (x)
    (implies
     (p1994a1-scalar-p x)
     (and
      (natp (p1994a1-arch-bound x))
      (p1994a1-less
       x
       (p1994a1-rational-embed
        (p1994a1-arch-bound x)))
      (implies
       (p1994a1-less
        (p1994a1-rational-embed 0)
        x)
       (and
        (posp (p1994a1-reciprocal-bound x))
        (p1994a1-less
         (p1994a1-rational-embed
          (/ 1 (p1994a1-reciprocal-bound x)))
         x)))))))

(defun p1994a1-real-additive-structure-p (zero)
  (and
   (p1994a1-scalar-p zero)
   (equal (p1994a1-rational-embed 0) zero)
   (p1994a1-additive-laws-p zero)
   (p1994a1-order-laws-p)
   (p1994a1-rational-embedding-laws-p)
   (p1994a1-archimedean-p)))

(defun-sk p1994a1-sequence-hypotheses-p (zero)
  (forall (n)
    (implies
     (and (natp n) (<= 1 n))
     (and
      (p1994a1-scalar-p (p1994a1-a n))
      (p1994a1-less zero (p1994a1-a n))
      (p1994a1-less-equal
       (p1994a1-a n)
       (p1994a1-add
        (p1994a1-a (* 2 n))
        (p1994a1-a (+ (* 2 n) 1))))))))

(defun p1994a1-partial-sum (n zero)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1994a1-add
     (p1994a1-partial-sum (- n 1) zero)
     (p1994a1-a n))))

(defun-sk p1994a1-above-bound-tail-p
    (bound cutoff zero)
  (forall (n)
    (implies
     (and (natp n) (<= cutoff n))
     (p1994a1-less
      (p1994a1-rational-embed bound)
      (p1994a1-partial-sum n zero)))))

(defun-sk p1994a1-above-bound-cutoff-exists-p
    (bound zero)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1994a1-above-bound-tail-p
      bound cutoff zero))))

(defun-sk p1994a1-partial-sums-diverge-p (zero)
  (forall (bound)
    (implies
     (rationalp bound)
     (p1994a1-above-bound-cutoff-exists-p
      bound zero))))

(defun putnambench-putnam-1994-a1-statement (zero)
  (implies
   (and
    (p1994a1-real-additive-structure-p zero)
    (p1994a1-sequence-hypotheses-p zero))
   (p1994a1-partial-sums-diverge-p zero)))

(value-triple :itpeval-statement-checked)
:q
