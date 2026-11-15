;; Statement-only formalization of Logipedia corpus artifact
;; cong.congruent_n_n, catalog title "cong.congruent_n_n": every natural
;; number is congruent to itself modulo every natural modulus. This file
;; contains no proof.

(in-package "ACL2")

(defun logipedia-cong-congruent-n-n-statement (n p)
  (implies
   (and (natp n)
        (natp p))
   (equal (mod n p)
          (mod n p))))

(value-triple :itpeval-statement-checked)
:q
