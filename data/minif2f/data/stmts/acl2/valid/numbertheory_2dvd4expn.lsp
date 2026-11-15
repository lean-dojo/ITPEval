;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_2dvd4expn: for every nonzero natural number n, 2 divides 4
;; raised to the nth power. This file contains no proof.

(in-package "ACL2")

(defun numbertheory-2dvd4expn-statement (n)
  (implies
   (and (natp n)
        (not (equal n 0)))
   (equal (mod (expt 4 n) 2)
          0)))

(value-triple :itpeval-statement-checked)
:q
