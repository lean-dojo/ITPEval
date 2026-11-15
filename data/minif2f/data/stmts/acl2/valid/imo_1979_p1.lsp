;; Statement-only formalization of miniF2F corpus artifact imo_1979_p1:
;; if the alternating harmonic sum from k = 1 through 1319 equals p/q for
;; natural p and positive natural q, then 1979 divides p. This file contains
;; no proof.
;;
;; The finite sum and p/q are rational, so ACL2's exact rational arithmetic
;; represents their equality in the reals without changing the proposition.

(in-package "ACL2")

(defun imo-1979-p1-alternating-harmonic-sum-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (imo-1979-p1-alternating-harmonic-sum-through (- n 1))
       (if (equal (mod n 2) 0)
           (- (/ 1 n))
         (/ 1 n)))))

(defun imo-1979-p1-statement (p q)
  (implies
   (and (natp p)
        (natp q)
        (< 0 q)
        (equal
         (imo-1979-p1-alternating-harmonic-sum-through 1319)
         (/ p q)))
   (equal (mod p 1979) 0)))

(value-triple :itpeval-statement-checked)
:q
