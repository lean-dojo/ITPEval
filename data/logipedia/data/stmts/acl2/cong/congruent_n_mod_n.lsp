;; Statement-only formalization of Logipedia corpus artifact
;; cong.congruent_n_mod_n, catalog title "cong.congruent_n_mod_n": every
;; natural number is congruent to its remainder modulo a positive natural
;; modulus. This file contains no proof.

(in-package "ACL2")

(defun logipedia-cong-congruent-n-mod-n-statement (n p)
  (implies
   (and (natp n)
        (natp p)
        (< 0 p))
   (equal (mod n p)
          (mod (mod n p) p))))

(value-triple :itpeval-statement-checked)
:q
