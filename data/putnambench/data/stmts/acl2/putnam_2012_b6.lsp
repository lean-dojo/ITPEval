;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_b6:
;; the cubic permutation of residue classes modulo an odd prime p congruent
;; to 2 modulo 3 is even exactly when p is 3 modulo 4. This file contains
;; no proof.

(in-package "ACL2")

(defun putnam-2012-b6-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-2012-b6-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-2012-b6-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-2012-b6-no-divisor-through-p
    p (- p 1))))

;; Fin p is represented by its canonical natural representatives
;; 0,...,p-1. Multiplication in Fin p is multiplication modulo p.
(defun putnam-2012-b6-cube-residue (x p)
  (if (and (natp x)
           (posp p))
      (mod (* x x x) p)
    0))

;; Count inversions formed by the entry at index I and all earlier indices.
(defun putnam-2012-b6-inversions-with-lower-indices
    (p i count)
  (declare (xargs :measure (nfix count)))
  (if (and (natp p)
           (natp i)
           (natp count))
      (if (zp count)
          0
        (let ((j (- count 1)))
          (+
           (if
            (>
             (putnam-2012-b6-cube-residue j p)
             (putnam-2012-b6-cube-residue i p))
            1
            0)
           (putnam-2012-b6-inversions-with-lower-indices
            p i j))))
    0))

;; This is the full inversion count of the list
;; [0^3 mod p, 1^3 mod p, ..., (p-1)^3 mod p]. Under the hypotheses below
;; that list is exactly the source cube permutation, and even inversion
;; parity is equivalent to permutation sign +1.
(defun putnam-2012-b6-cube-inversion-count-through
    (p count)
  (declare (xargs :measure (nfix count)))
  (if (and (natp p)
           (natp count))
      (if (zp count)
          0
        (let ((i (- count 1)))
          (+
           (putnam-2012-b6-inversions-with-lower-indices
            p i i)
           (putnam-2012-b6-cube-inversion-count-through
            p i))))
    0))

(defun putnambench-putnam-2012-b6-statement (p)
  (implies
   (and
    (putnam-2012-b6-prime-p p)
    (equal (mod p 2) 1)
    (equal (mod p 3) 2))
   (iff
    (equal
     (mod
      (putnam-2012-b6-cube-inversion-count-through p p)
      2)
     0)
    (equal (mod p 4) 3))))

(value-triple :itpeval-statement-checked)
:q
