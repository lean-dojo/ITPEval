;; Statement-only formalization of PutnamBench corpus artifact putnam_2022_a3:
;; for every prime p greater than 5, the number of infinite nonzero residue
;; sequences satisfying a_n*a_(n+2) = 1+a_(n+1) modulo p is congruent to
;; 0 or 2 modulo 5. This file contains no proof.

(in-package "ACL2")

;; For a natural number, testing every candidate divisor from 2 through
;; number-1 is exactly the usual definition of primality.
(defun putnam-2022-a3-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (putnam-2022-a3-no-divisor-from-p
        number (+ divisor 1)))
    t))

(defun putnam-2022-a3-primep (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2022-a3-no-divisor-from-p number 2)))

;; Under the root predicate's prime-modulus hypothesis, every x in
;; 1,...,p-1 has a unique inverse. This bounded search returns that inverse.
(defun putnam-2022-a3-inverse-search (x p candidate)
  (declare (xargs :measure (nfix (- p candidate))))
  (if (and (natp p)
           (natp candidate)
           (< candidate p))
      (if (equal (mod (* x candidate) p) 1)
          candidate
        (putnam-2022-a3-inverse-search
         x p (+ candidate 1)))
    0))

(defun putnam-2022-a3-inverse (x p)
  (putnam-2022-a3-inverse-search x p 1))

(defun putnam-2022-a3-next-value (x y p)
  (mod
   (* (+ 1 y)
      (putnam-2022-a3-inverse x p))
   p))

;; A state is the ordered pair (a_n,a_(n+1)). The transition below is the
;; unique solution of a_n*a_(n+2) = 1+a_(n+1) modulo the prime p.
(defun putnam-2022-a3-valid-orbit-prefix-p
    (x y p transitions-remaining)
  (declare (xargs :measure (nfix transitions-remaining)))
  (and
   (natp x)
   (natp y)
   (< 0 x)
   (< x p)
   (< 0 y)
   (< y p)
   (if (zp transitions-remaining)
       t
     (putnam-2022-a3-valid-orbit-prefix-p
      y
      (putnam-2022-a3-next-value x y p)
      p
      (- transitions-remaining 1)))))

;; There are exactly (p-1)^2 nonzero pair states. Thus an initial pair gives
;; an infinite nonzero orbit iff (p-1)^2+1 successive states are nonzero:
;; the forward direction is immediate, while the reverse direction has a
;; repeated state and the deterministic transition repeats forever. Hence
;; counting these initial pairs is in bijection with the source set of all
;; infinite sequences, rather than a restriction to finite sequences.
(defun putnam-2022-a3-count-second-values
    (x y p transition-count)
  (declare (xargs :measure (nfix y)))
  (if (zp y)
      0
    (+ (if (putnam-2022-a3-valid-orbit-prefix-p
             x y p transition-count)
           1
         0)
       (putnam-2022-a3-count-second-values
        x (- y 1) p transition-count))))

(defun putnam-2022-a3-count-first-values
    (x p transition-count)
  (declare (xargs :measure (nfix x)))
  (if (zp x)
      0
    (+ (putnam-2022-a3-count-second-values
        x (- p 1) p transition-count)
       (putnam-2022-a3-count-first-values
        (- x 1) p transition-count))))

(defun putnam-2022-a3-sequence-count (p)
  (let ((state-count (* (- p 1) (- p 1))))
    (putnam-2022-a3-count-first-values
     (- p 1) p state-count)))

(defun putnambench-putnam-2022-a3-statement (p f)
  (implies
   (and
    (natp p)
    (natp f)
    (< 5 p)
    (putnam-2022-a3-primep p)
    (equal f (putnam-2022-a3-sequence-count p)))
   (or
    (equal (mod f 5) 0)
    (equal (mod f 5) 2))))

(value-triple :itpeval-statement-checked)
:q
