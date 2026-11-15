;; Statement-only formalization of Logipedia corpus artifact
;; cong.congruent_times, catalog title "cong.congruent_times": congruent
;; natural-number factors have congruent products modulo a positive natural
;; modulus. This file contains no proof.

(in-package "ACL2")

(defun logipedia-cong-congruent-times-statement (n m n1 m1 p)
  (implies
   (and (natp n)
        (natp m)
        (natp n1)
        (natp m1)
        (natp p)
        (< 0 p)
        (equal (mod n p)
               (mod n1 p))
        (equal (mod m p)
               (mod m1 p)))
   (equal (mod (* n m) p)
          (mod (* n1 m1) p))))

(value-triple :itpeval-statement-checked)
:q
