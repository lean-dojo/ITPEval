;; Statement-only formalization of Logipedia corpus artifact
;; gcd.let_clause_1549, catalog title "gcd.let_clause_1549": for natural
;; numbers m and n, positivity of n and m = 0 imply that every natural x
;; equals the truncated natural difference x - m. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-gcd-let-clause-1549-statement ()
  (forall (m n x1106)
    (implies
     (and
      (natp m)
      (natp n)
      (natp x1106))
     (implies
      (< 0 n)
      (implies
       (equal 0 m)
       (equal
        x1106
        (nfix (- (nfix x1106) (nfix m)))))))))

(value-triple :itpeval-statement-checked)
:q
