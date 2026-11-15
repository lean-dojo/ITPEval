;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_b5:
;; for every prime p greater than 3, the number of descents between consecutive
;; nonzero modular inverses modulo p is greater than p/4 - 1. This file contains
;; no proof.

(in-package "ACL2")

;; For a natural p, this checks every possible proper divisor from candidate
;; down through 2.
(defun putnam-2025-b5-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-2025-b5-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-2025-b5-primep (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-2025-b5-no-divisor-through-p
    p (- p 1))))

;; Under the statement hypotheses, each k in 1,...,p-1 has exactly one
;; candidate in 1,...,p-1 whose product with k is 1 modulo p. The descending
;; search therefore returns the canonical residue represented by ZMod.val.
(defun putnam-2025-b5-mod-inverse-through (p k candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (posp p))
          (not (natp candidate))
          (zp candidate))
      0
    (if (equal (mod (* k candidate) p) 1)
        candidate
      (putnam-2025-b5-mod-inverse-through
       p k (- candidate 1)))))

(defun putnam-2025-b5-mod-inverse (p k)
  (putnam-2025-b5-mod-inverse-through
   p k (nfix (- p 1))))

;; Descending recursion over k counts exactly the source interval
;; Finset.Icc 1 (p-2).
(defun putnam-2025-b5-descent-count-through (p k)
  (declare (xargs :measure (nfix k)))
  (if (or (not (natp k))
          (zp k))
      0
    (+
     (if (< (putnam-2025-b5-mod-inverse p (+ k 1))
            (putnam-2025-b5-mod-inverse p k))
         1
       0)
     (putnam-2025-b5-descent-count-through
      p (- k 1)))))

(defun putnam-2025-b5-descent-count (p)
  (putnam-2025-b5-descent-count-through
   p (nfix (- p 2))))

(defun putnambench-putnam-2025-b5-statement (p)
  (implies
   (and
    (natp p)
    (putnam-2025-b5-primep p)
    (< 3 p))
   (< (- (/ p 4) 1)
      (putnam-2025-b5-descent-count p))))

(value-triple :itpeval-statement-checked)
:q
