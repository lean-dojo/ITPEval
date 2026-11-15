;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_451:
;; a real bijection whose inverse sends -15 to 0, 0 to 3, 3 to 9, and 9
;; to 20 satisfies sigma(sigma(9)) = 0. This file contains no proof.
;;
;; Lean, Rocq, and Metamath give the inverse value at 9 as 20. Isabelle
;; instead writes sigma(9) = 20, which conflicts with its preceding
;; inverse-at-3 value because the inverse law forces sigma(9) = 3. The
;; predicate below preserves the common nonvacuous statement.
;;
;; ACL2 is first-order, so the bijection is eliminated into its complete
;; relevant orbit. Equal inputs have equal sigma-values, and
;; sigma(sigma-inverse(x)) = x is recorded at -15, 0, 3, and 9. Every source
;; bijection induces these equalities. Conversely, every satisfying orbit is
;; realized by the real bijection cycling -15 to 20 to 9 to 3 to 0 to -15
;; and fixing every other real. Thus this observation encoding is
;; bidirectionally equivalent to the common source statement.

(in-package "ACL2")

(defun mathd-algebra-451-statement
    (inverse-at-minus-fifteen
     inverse-at-zero
     inverse-at-three
     inverse-at-nine
     sigma-at-inverse-at-minus-fifteen
     sigma-at-zero
     sigma-at-inverse-at-zero
     sigma-at-three
     sigma-at-inverse-at-three
     sigma-at-nine
     sigma-at-inverse-at-nine
     sigma-at-twenty
     sigma-at-sigma-at-nine)
  (implies
   (and
    (equal inverse-at-minus-fifteen 0)
    (equal inverse-at-zero 3)
    (equal inverse-at-three 9)
    (equal inverse-at-nine 20)
    (equal sigma-at-inverse-at-minus-fifteen sigma-at-zero)
    (equal sigma-at-inverse-at-minus-fifteen -15)
    (equal sigma-at-inverse-at-zero sigma-at-three)
    (equal sigma-at-inverse-at-zero 0)
    (equal sigma-at-inverse-at-three sigma-at-nine)
    (equal sigma-at-inverse-at-three 3)
    (equal sigma-at-inverse-at-nine sigma-at-twenty)
    (equal sigma-at-inverse-at-nine 9)
    (equal sigma-at-sigma-at-nine sigma-at-three))
   (equal sigma-at-sigma-at-nine 0)))

(value-triple :itpeval-statement-checked)
:q
