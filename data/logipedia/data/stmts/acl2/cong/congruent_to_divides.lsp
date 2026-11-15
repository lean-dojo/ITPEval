;; Statement-only formalization of Logipedia corpus artifact
;; cong.congruent_to_divides, catalog title "cong.congruent_to_divides":
;; congruent natural numbers modulo a positive natural modulus have a
;; truncated natural difference divisible by that modulus. This file contains
;; no proof.

(in-package "ACL2")

(defun-sk logipedia-cong-congruent-to-divides-divides-p (p value)
  (exists (q)
    (and (natp q)
         (equal value (* p q)))))

(defun logipedia-cong-congruent-to-divides-statement (n m p)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (< 0 p)
        (equal (mod n p)
               (mod m p)))
   (logipedia-cong-congruent-to-divides-divides-p
    p
    (nfix (- n m)))))

(value-triple :itpeval-statement-checked)
:q
