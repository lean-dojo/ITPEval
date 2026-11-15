;; Statement-only formalization of Logipedia corpus artifact
;; cong.eq_times_plus_to_congruent, catalog title
;; "cong.eq_times_plus_to_congruent": if a natural number equals a natural
;; multiple of a positive modulus plus another natural number, then the two
;; numbers are congruent modulo that modulus. This file contains no proof.

(in-package "ACL2")

(defun logipedia-cong-eq-times-plus-to-congruent-statement (n m p r)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (natp r)
        (< 0 p)
        (equal n (+ (* r p) m)))
   (equal (mod n p)
          (mod m p))))

(value-triple :itpeval-statement-checked)
:q
