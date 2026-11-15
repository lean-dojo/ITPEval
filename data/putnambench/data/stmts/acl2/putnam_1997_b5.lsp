;; Statement-only formalization of PutnamBench corpus artifact putnam_1997_b5:
;; for every natural n at least 2, base-2 tetration at heights n and n-1 is
;; congruent modulo n. This file contains no proof.

(in-package "ACL2")

(defun putnam-1997-b5-tetration (base height)
  (declare (xargs :measure (nfix height)))
  (if (or (not (natp base))
          (not (natp height)))
      0
    (if (zp height)
        1
      (expt base
            (putnam-1997-b5-tetration base (- height 1))))))

(defun putnambench-putnam-1997-b5-statement (n)
  (implies
   (and (natp n)
        (<= 2 n))
   (equal
    (mod (putnam-1997-b5-tetration 2 n) n)
    (mod (putnam-1997-b5-tetration 2 (- n 1)) n))))

(value-triple :itpeval-statement-checked)
:q
