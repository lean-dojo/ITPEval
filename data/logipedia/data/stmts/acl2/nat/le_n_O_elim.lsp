;; Statement-only formalization of Logipedia corpus artifact
;; nat.le_n_O_elim, catalog title "nat.le_n_O_elim": a natural number at
;; most zero satisfies every proposition-valued predicate that holds at zero.
;; This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-le-n-o-elim-predicate (n) t)

(defun logipedia-nat-le-n-o-elim-statement (n)
  (implies
   (and
    (natp n)
    (<= n 0))
   (implies
    (logipedia-nat-le-n-o-elim-predicate 0)
    (logipedia-nat-le-n-o-elim-predicate n))))

(value-triple :itpeval-statement-checked)
:q
