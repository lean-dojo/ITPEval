;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_b3:
;; every finite set with at least two elements admits a right-cancellative
;; binary operation for which no triple satisfies associativity. This file
;; contains no proof.

(in-package "ACL2")

;; For each cardinality N, the canonical carrier is {0, ..., N-1}. Every
;; binary operation on it is represented uniquely by the N^2 base-N digits of
;; an integer CODE below N^(N^2), ordered by the pair index X*N+Y. Transport
;; along a bijection between an arbitrary N-element type and this carrier
;; preserves equality, right cancellation, and failure of associativity.
(defun putnam-1984-b3-operation (n code x y)
  (if (and (posp n)
           (natp code)
           (natp x)
           (natp y))
      (mod
       (floor code
              (expt n (+ (* x n) y)))
       n)
    0))

(defun putnam-1984-b3-z-laws-p
    (n code x y remaining-z)
  (declare (xargs :measure (nfix remaining-z)))
  (if (zp remaining-z)
      t
    (let* ((z (- remaining-z 1))
           (xz
            (putnam-1984-b3-operation n code x z))
           (yz
            (putnam-1984-b3-operation n code y z))
           (y-z
            (putnam-1984-b3-operation n code y z))
           (x-y
            (putnam-1984-b3-operation n code x y)))
      (and
       (putnam-1984-b3-z-laws-p
        n code x y z)
       (implies (equal xz yz)
                (equal x y))
       (not
        (equal
         (putnam-1984-b3-operation n code x y-z)
         (putnam-1984-b3-operation n code x-y z)))))))

(defun putnam-1984-b3-y-laws-p
    (n code x remaining-y)
  (declare (xargs :measure (nfix remaining-y)))
  (if (zp remaining-y)
      t
    (let ((y (- remaining-y 1)))
      (and
       (putnam-1984-b3-y-laws-p
        n code x y)
       (putnam-1984-b3-z-laws-p
        n code x y n)))))

(defun putnam-1984-b3-operation-laws-p
    (n code remaining-x)
  (declare (xargs :measure (nfix remaining-x)))
  (if (zp remaining-x)
      t
    (let ((x (- remaining-x 1)))
      (and
       (putnam-1984-b3-operation-laws-p
        n code x)
       (putnam-1984-b3-y-laws-p
        n code x n)))))

;; The bounded search keeps the source existential quantifier internal. Since
;; every operation has exactly one code in this range, it succeeds exactly
;; when an operation satisfying both source clauses exists.
(defun putnam-1984-b3-operation-exists-p
    (n remaining-codes)
  (declare (xargs :measure (nfix remaining-codes)))
  (if (zp remaining-codes)
      nil
    (let ((code (- remaining-codes 1)))
      (or
       (putnam-1984-b3-operation-laws-p
        n code n)
       (putnam-1984-b3-operation-exists-p
        n code)))))

(defun putnambench-putnam-1984-b3-statement (n)
  (implies
   (and (natp n)
        (<= 2 n))
   (putnam-1984-b3-operation-exists-p
    n (expt n (* n n)))))

(value-triple :itpeval-statement-checked)
:q
