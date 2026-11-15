;; Statement-only formalization of miniF2F artifact mathd_algebra_270: a real
;; function equal to 1/(x + 2) away from -2 satisfies f(f(1)) = 3/7. This file
;; contains no proof.
;;
;; ACL2 is first-order, so the function is represented by the observations
;; f(1) and f(f(1)). The guarded equalities below are exactly the source
;; hypothesis instantiated at 1 and f(1). Every source function supplies these
;; observations. Conversely, the antecedent forces the observations to be
;; 1/3 and 3/7, and they extend to a source function by using 1/(x + 2) away
;; from -2 and an arbitrary value at -2. Thus the observation implication is
;; bidirectionally equivalent to the source statement and does not restrict
;; its real domain.

(in-package "ACL2")

(defun mathd-algebra-270-statement (f-at-1 f-at-f-at-1)
  (implies
   (and
    (implies (not (equal 1 -2))
             (equal f-at-1
                    (/ 1 (+ 1 2))))
    (implies (not (equal f-at-1 -2))
             (equal f-at-f-at-1
                    (/ 1 (+ f-at-1 2)))))
   (equal f-at-f-at-1
          (/ 3 7))))

(value-triple :itpeval-statement-checked)
:q
