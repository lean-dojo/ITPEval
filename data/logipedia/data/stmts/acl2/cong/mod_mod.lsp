;; Statement-only formalization of Logipedia corpus artifact cong.mod_mod,
;; catalog title "cong.mod_mod": taking a natural-number remainder modulo a
;; positive natural modulus is idempotent. This file contains no proof.

(in-package "ACL2")

(defun logipedia-cong-mod-mod-statement (n p)
  (implies
   (and (natp n)
        (natp p)
        (< 0 p))
   (equal (mod n p)
          (mod (mod n p) p))))

(value-triple :itpeval-statement-checked)
:q
