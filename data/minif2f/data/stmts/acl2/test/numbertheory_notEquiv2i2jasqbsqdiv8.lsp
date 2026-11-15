;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_notEquiv2i2jasqbsqdiv8: the universal equivalence between
;; both integer coordinates being even and their squared sum being divisible
;; by 8 fails. This file contains no proof.

(in-package "ACL2")

(defun-sk numbertheory-notequiv2i2jasqbsqdiv8-both-even-p (a b)
  (exists (i j)
    (and (integerp i)
         (integerp j)
         (equal a (* 2 i))
         (equal b (* 2 j)))))

(defun-sk numbertheory-notequiv2i2jasqbsqdiv8-sum-divisible-p (a b)
  (exists (k)
    (and (integerp k)
         (equal (+ (* a a) (* b b))
                (* 8 k)))))

(defun-sk numbertheory-notequiv2i2jasqbsqdiv8-statement ()
  (exists (a b)
    (and
     (integerp a)
     (integerp b)
     (not
      (iff
       (numbertheory-notequiv2i2jasqbsqdiv8-both-even-p a b)
       (numbertheory-notequiv2i2jasqbsqdiv8-sum-divisible-p a b))))))

(value-triple :itpeval-statement-checked)
:q
