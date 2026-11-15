;; Statement-only formalization of miniF2F corpus artifact mathd_numbertheory_668:
;; in the integers modulo 7, the inverse of 2 + 3 minus the sum of the
;; inverses of 2 and 3 is 1. This file contains no proof.
;;
;; Canonical residues from 0 through 6 represent Z/7Z. The inverse function
;; below is the complete field inverse on those residues, with inverse 0 = 0.

(in-package "ACL2")

(defun mathd-numbertheory-668-inverse-mod-7 (x)
  (case (mod x 7)
    (0 0)
    (1 1)
    (2 4)
    (3 5)
    (4 2)
    (5 3)
    (otherwise 6)))

(defun mathd-numbertheory-668-statement (l r)
  (implies
   (and (integerp l)
        (integerp r)
        (<= 0 l)
        (< l 7)
        (<= 0 r)
        (< r 7)
        (equal l
               (mathd-numbertheory-668-inverse-mod-7
                (+ 2 3)))
        (equal r
               (mod
                (+ (mathd-numbertheory-668-inverse-mod-7 2)
                   (mathd-numbertheory-668-inverse-mod-7 3))
                7)))
   (equal (- l r) 1)))

(value-triple :itpeval-statement-checked)
:q
