;; Statement-only formalization of Logipedia corpus artifact
;; cong.let_clause_73, catalog title "cong.let_clause_73": for natural
;; numbers n, m, p, x134, x135, and x136 with p positive, swapping x134 and
;; x135 preserves their nested sum with x136. This file contains no proof.

(in-package "ACL2")

(defun logipedia-cong-let-clause-73-statement
    (n m p x134 x135 x136)
  (implies
   (and (natp n)
        (natp m)
        (natp p)
        (< 0 p)
        (natp x134)
        (natp x135)
        (natp x136))
   (equal (+ x134 (+ x135 x136))
          (+ x135 (+ x134 x136)))))

(value-triple :itpeval-statement-checked)
:q
