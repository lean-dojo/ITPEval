;; Statement-only formalization of miniF2F artifact mathd_algebra_171: a
;; real-valued function defined by f(x) = 5*x + 4 has f(1) = 9. This file
;; contains no proof.
;;
;; ACL2 is first-order, so the function hypothesis is represented by f(1),
;; the only function value used in the conclusion. Instantiating the source
;; hypothesis at 1 gives the scalar antecedent below. Conversely, any scalar
;; satisfying that antecedent equals 9 and is realized by the source function
;; f(x) = 5*x + 4. Thus this scalar implication is bidirectionally equivalent
;; to the source statement. The antecedent forces an exact integer value, so
;; the unrestricted ACL2 parameter does not narrow the source real domain.

(in-package "ACL2")

(defun mathd-algebra-171-statement (f-at-1)
  (implies
   (equal f-at-1
          (+ (* 5 1) 4))
   (equal f-at-1 9)))

(value-triple :itpeval-statement-checked)
:q
