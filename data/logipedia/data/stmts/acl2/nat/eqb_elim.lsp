;; Statement-only formalization of Logipedia corpus artifact nat.eqb_elim,
;; catalog title "nat.eqb_elim": for any two natural numbers and any
;; proposition-valued predicate on Booleans, the equality and inequality
;; branches establish the predicate at their Boolean equality test.
;; This file contains no proof.

(in-package "ACL2")

;; This conservative interface represents the source's arbitrary predicate
;; bool -> Prop. Its use in Boolean positions gives ACL2's proposition-valued
;; interpretation without imposing any additional law.
(defstub logipedia-nat-eqb-elim-predicate
  (boolean-value)
  t)

;; The source module's recursive equality test on Peano naturals, with T and
;; NIL representing its true and false constructors.
(defun logipedia-nat-eqb-elim-eqb (n m)
  (if (zp n)
      (if (zp m) t nil)
    (if (zp m)
        nil
      (logipedia-nat-eqb-elim-eqb (1- n) (1- m)))))

(defun-sk logipedia-nat-eqb-elim-statement ()
  (forall (n m)
    (implies
     (and (natp n)
          (natp m))
     (implies
      (implies
       (equal n m)
       (logipedia-nat-eqb-elim-predicate t))
      (implies
       (implies
        (not (equal n m))
        (logipedia-nat-eqb-elim-predicate nil))
       (logipedia-nat-eqb-elim-predicate
        (logipedia-nat-eqb-elim-eqb n m)))))))

(value-triple :itpeval-statement-checked)
:q
