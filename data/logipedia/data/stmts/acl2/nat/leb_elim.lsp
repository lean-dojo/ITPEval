;; Statement-only formalization of Logipedia corpus artifact nat.leb_elim,
;; catalog title "nat.leb_elim": elimination for the recursive Boolean
;; less-than-or-equal test on natural numbers, selecting the predicate's true
;; or false case according to the corresponding order proposition. This file
;; contains no proof.

(in-package "ACL2")

;; This is the source module's Peano recursion for Boolean less-than-or-equal,
;; represented on ACL2's natural numbers with T and NIL as the Boolean values.
(defun logipedia-nat-leb-elim-leb (n m)
  (if (zp n)
      t
    (if (zp m)
        nil
      (logipedia-nat-leb-elim-leb (1- n) (1- m)))))

;; A predicate on the two-element Boolean type is represented extensionally by
;; its proposition truth values at T and NIL.
(defun-sk logipedia-nat-leb-elim-statement ()
  (forall (n m p-true p-false)
    (implies
     (and
      (natp n)
      (natp m))
     (implies
      (implies
       (<= n m)
       p-true)
      (implies
       (implies
        (not (<= n m))
        p-false)
       (if (logipedia-nat-leb-elim-leb n m)
           p-true
         p-false))))))

(value-triple :itpeval-statement-checked)
:q
