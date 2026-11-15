;; Statement-only formalization of Logipedia corpus artifact
;; nat.minus_minus_comm, catalog title "nat.minus_minus_comm": for all natural
;; numbers a, b, and c, iterated truncated subtraction commutes in the two
;; subtrahends. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-minus-minus-comm-statement ()
  (forall (a b c)
    (implies
     (and
      (natp a)
      (natp b)
      (natp c))
     (equal
      (nfix (- (nfix (- a b)) c))
      (nfix (- (nfix (- a c)) b))))))

(value-triple :itpeval-statement-checked)
:q
