;; Statement-only formalization of Logipedia corpus artifact
;; cong.divides_to_congruent, catalog title "cong.divides_to_congruent": if a
;; positive natural modulus divides the truncated difference of ordered
;; natural numbers, then those numbers are congruent modulo it. This file
;; contains no proof.

(in-package "ACL2")

(defun-sk logipedia-cong-divides-to-congruent-divides-p (p value)
  (exists (q)
    (and (natp q)
         (equal value (* p q)))))

(defun logipedia-cong-divides-to-congruent-statement (n m p)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (< 0 p)
        (<= m n)
        (logipedia-cong-divides-to-congruent-divides-p
         p
         (nfix (- n m))))
   (equal (mod n p)
          (mod m p))))

(value-triple :itpeval-statement-checked)
:q
