;; Statement-only formalization of miniF2F corpus artifact imo_1987_p4:
;; every function from the natural numbers to themselves has some n for which
;; f(f(n)) differs from n + 1987. This file contains no proof.

(in-package "ACL2")

;; This unconstrained unary symbol represents the arbitrary source function.
;; Its natural-number codomain is stated explicitly below rather than being
;; supplied as a constraint on the symbol.
(defstub imo-1987-p4-f (n) t)

(defun-sk imo-1987-p4-nat-to-nat-p ()
  (forall (n)
    (implies
     (natp n)
     (natp (imo-1987-p4-f n)))))

(defun imo-1987-p4-counterexample-at-p (n)
  (and
   (natp n)
   (not
    (equal
     (imo-1987-p4-f (imo-1987-p4-f n))
     (+ n 1987)))))

(defun-sk imo-1987-p4-counterexample-exists-p ()
  (exists (n)
    (imo-1987-p4-counterexample-at-p n)))

(defun imo-1987-p4-statement ()
  (implies
   (imo-1987-p4-nat-to-nat-p)
   (imo-1987-p4-counterexample-exists-p)))

(value-triple :itpeval-statement-checked)
:q
