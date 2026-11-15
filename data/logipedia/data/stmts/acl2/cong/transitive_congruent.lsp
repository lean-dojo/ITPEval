;; Statement-only formalization of Logipedia corpus artifact
;; cong.transitive_congruent, catalog title "cong.transitive_congruent":
;; congruence of natural numbers defined by equality of remainders modulo any
;; natural modulus is transitive. This file contains no proof.

(in-package "ACL2")

;; The source natural-number remainder is totalized by mod(n, 0) = n.

(defun logipedia-cong-transitive-congruent-mod (n p)
  (if (equal p 0)
      n
    (mod n p)))

(defun logipedia-cong-transitive-congruent-statement (p x y z)
  (implies
   (and (natp p)
        (natp x)
        (natp y)
        (natp z))
   (implies
    (and
     (equal
      (logipedia-cong-transitive-congruent-mod x p)
      (logipedia-cong-transitive-congruent-mod y p))
     (equal
      (logipedia-cong-transitive-congruent-mod y p)
      (logipedia-cong-transitive-congruent-mod z p)))
    (equal
     (logipedia-cong-transitive-congruent-mod x p)
     (logipedia-cong-transitive-congruent-mod z p)))))

(value-triple :itpeval-statement-checked)
:q
