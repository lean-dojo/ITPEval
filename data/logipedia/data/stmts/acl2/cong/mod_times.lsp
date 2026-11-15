;; Statement-only formalization of Logipedia corpus artifact cong.mod_times,
;; catalog title "cong.mod_times": reducing a product modulo a positive natural
;; modulus agrees with multiplying the reduced natural-number factors and
;; reducing again. This file contains no proof.

(in-package "ACL2")

(defun logipedia-cong-mod-times-statement (n m p)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (< 0 p))
   (equal (mod (* n m) p)
          (mod (* (mod n p)
                  (mod m p))
               p))))

(value-triple :itpeval-statement-checked)
:q
