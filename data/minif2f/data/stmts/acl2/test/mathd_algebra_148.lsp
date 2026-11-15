;; Statement-only formalization of miniF2F artifact mathd_algebra_148: a
;; real coefficient c in f(x) = c*x^3 - 9*x + 3 is determined by f(2) = 9,
;; namely c = 3. This file contains no proof.
;;
;; ACL2 is first-order, so the function hypotheses are represented by the
;; value f(2), the only function value needed for the conclusion. Instantiating
;; the source formula at 2 gives the first scalar equation below. Conversely,
;; any scalars satisfying both equations have c = 3 and f(2) = 9 and extend to
;; the source real function by f(x) = c*x^3 - 9*x + 3. Thus the scalar
;; implication is bidirectionally equivalent to the source statement. The
;; antecedent forces exact rational values, so unrestricted ACL2 parameters do
;; not narrow the source real domain.

(in-package "ACL2")

(defun mathd-algebra-148-statement (c f-at-2)
  (implies
   (and (equal f-at-2
               (+ (- (* c (expt 2 3))
                     (* 9 2))
                  3))
        (equal f-at-2 9))
   (equal c 3)))

(value-triple :itpeval-statement-checked)
:q
