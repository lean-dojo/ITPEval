;; Statement-only formalization of PutnamBench corpus artifact putnam_2012_a5:
;; affine maps of a positive-dimensional vector space over F_p having a full
;; orbit from zero exist exactly for n = 1 and for (n,p) = (2,2). This file
;; contains no proof.

(in-package "ACL2")

;; Because p is prime, the source field with p elements is uniquely isomorphic
;; to the residue field F_p. Vectors use canonical residue lists. A single
;; base-p code contains first the n entries of v and then the n^2 row-major
;; entries of M, so the bounded search below ranges over every source pair
;; (M,v) while keeping both existential witnesses internal.

(defun putnam-2012-a5-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-2012-a5-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-2012-a5-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-2012-a5-no-divisor-through-p
    p (- p 1))))

(defun putnam-2012-a5-base-digit (code base position)
  (mod (floor code (expt base position)) base))

(defun putnam-2012-a5-zero-vector (remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     0
     (putnam-2012-a5-zero-vector (- remaining 1)))))

(defun putnam-2012-a5-row-dot-product
    (code p n vector row column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (*
      (putnam-2012-a5-base-digit
       code p (+ n (* row n) column))
      (nth column vector))
     (putnam-2012-a5-row-dot-product
      code p n vector row (+ column 1) (- remaining 1)))))

(defun putnam-2012-a5-affine-image-rows
    (code p n vector row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (mod
      (+
       (putnam-2012-a5-base-digit code p row)
       (putnam-2012-a5-row-dot-product
        code p n vector row 0 n))
      p)
     (putnam-2012-a5-affine-image-rows
      code p n vector (+ row 1) (- remaining 1)))))

(defun putnam-2012-a5-affine-image (code p n vector)
  (putnam-2012-a5-affine-image-rows
   code p n vector 0 n))

;; Starting with zero, this checks exactly p^n successive positive iterates.
;; Rejecting an iterate already in SEEN is equivalent to pairwise distinctness
;; of G^k(0) for k = 1,...,p^n.
(defun putnam-2012-a5-full-orbit-p
    (code p n current seen remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((next
           (putnam-2012-a5-affine-image
            code p n current)))
      (and
       (not (member-equal next seen))
       (putnam-2012-a5-full-orbit-p
        code
        p
        n
        next
        (cons next seen)
        (- remaining 1))))))

(defun putnam-2012-a5-witness-search-p
    (n p remaining-codes)
  (declare (xargs :measure (nfix remaining-codes)))
  (if (and (natp n)
           (natp p)
           (< 0 p)
           (natp remaining-codes))
      (if (zp remaining-codes)
          nil
        (let ((code (- remaining-codes 1)))
          (or
           (putnam-2012-a5-full-orbit-p
            code
            p
            n
            (putnam-2012-a5-zero-vector n)
            nil
            (expt p n))
           (putnam-2012-a5-witness-search-p
            n p code))))
    nil))

(defun putnam-2012-a5-affine-full-orbit-exists-p (n p)
  (if (and (posp n) (putnam-2012-a5-prime-p p))
      (putnam-2012-a5-witness-search-p
       n
       p
       (expt p (+ (* n n) n)))
    nil))

(defun putnam-2012-a5-solution-p (n p)
  (or
   (equal n 1)
   (and
    (equal n 2)
    (equal p 2))))

(defun putnambench-putnam-2012-a5-statement (n p)
  (implies
   (and
    (posp n)
    (putnam-2012-a5-prime-p p))
   (iff
    (putnam-2012-a5-solution-p n p)
    (putnam-2012-a5-affine-full-orbit-exists-p n p))))

(value-triple :itpeval-statement-checked)
:q
