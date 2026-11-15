;; Statement-only formalization of Logipedia corpus artifact nat.le_gen,
;; catalog title "nat.le_gen": every predicate on the natural numbers that
;; holds for all naturals at most n holds at n. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-nat-le-gen-p (i) t)

(defun-sk logipedia-nat-le-gen-hypothesis-p (n)
  (forall (i)
    (implies
     (and
      (natp i)
      (<= i n))
     (logipedia-nat-le-gen-p i))))

(defun-sk logipedia-nat-le-gen-statement ()
  (forall (n)
    (implies
     (natp n)
     (implies
      (logipedia-nat-le-gen-hypothesis-p n)
      (logipedia-nat-le-gen-p n)))))

(value-triple :itpeval-statement-checked)
:q
