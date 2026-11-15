;; Statement-only formalization of Logipedia corpus artifact
;; nat.lt_O_n_elim, catalog title "nat.lt_O_n_elim": every positive natural
;; number satisfies any proposition-valued predicate that holds at every
;; successor. This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; nat -> Prop. Its use in Boolean positions imposes no additional law.
(defstub logipedia-nat-lt-o-n-elim-predicate (n) t)

(defun-sk logipedia-nat-lt-o-n-elim-successors-p ()
  (forall (m)
    (implies
     (natp m)
     (logipedia-nat-lt-o-n-elim-predicate (+ 1 m)))))

(defun-sk logipedia-nat-lt-o-n-elim-statement ()
  (forall (n)
    (implies
     (natp n)
     (implies
      (< 0 n)
      (implies
       (logipedia-nat-lt-o-n-elim-successors-p)
       (logipedia-nat-lt-o-n-elim-predicate n))))))

(value-triple :itpeval-statement-checked)
:q
