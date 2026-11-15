;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_b5:
;; for an odd prime p, the intersection of the quadratic residues modulo p
;; with their translates by one has floor(p/4) + 1 elements. This file
;; contains no proof.

(in-package "ACL2")

;; Every element of ZMod p has a unique representative in {0,...,p-1}.
;; The searches below therefore express the two internal existential
;; witnesses, and the final recursion counts exactly the source intersection.

(defun putnam-1991-b5-no-divisor-through-p (p candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod p candidate) 0))
     (putnam-1991-b5-no-divisor-through-p
      p (- candidate 1)))))

(defun putnam-1991-b5-prime-p (p)
  (and
   (natp p)
   (< 1 p)
   (putnam-1991-b5-no-divisor-through-p
    p (- p 1))))

;; Search x = 0,...,p-1 for z = x^2 + OFFSET modulo p.
(defun putnam-1991-b5-residue-witness-p
    (z p offset witness-count)
  (declare (xargs :measure (nfix witness-count)))
  (if (or (not (posp p))
          (zp witness-count))
      nil
    (let ((x (- witness-count 1)))
      (or
       (equal z (mod (+ (* x x) offset) p))
       (putnam-1991-b5-residue-witness-p
        z p offset x)))))

(defun putnam-1991-b5-intersection-member-p (z p)
  (and
   (natp z)
   (< z p)
   (putnam-1991-b5-residue-witness-p z p 0 p)
   (putnam-1991-b5-residue-witness-p z p 1 p)))

(defun putnam-1991-b5-intersection-count-through
    (p residue-count)
  (declare (xargs :measure (nfix residue-count)))
  (if (or (not (posp p))
          (zp residue-count))
      0
    (let ((z (- residue-count 1)))
      (+
       (if (putnam-1991-b5-intersection-member-p z p)
           1
         0)
       (putnam-1991-b5-intersection-count-through p z)))))

(defun putnambench-putnam-1991-b5-statement (p)
  (implies
   (and
    (natp p)
    (putnam-1991-b5-prime-p p)
    (equal (mod p 2) 1))
   (equal
    (putnam-1991-b5-intersection-count-through p p)
    (+ (floor p 4) 1))))

(value-triple :itpeval-statement-checked)
:q
