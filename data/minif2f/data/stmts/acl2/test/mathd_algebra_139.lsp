;; Statement-only formalization of miniF2F artifact mathd_algebra_139: a
;; real-valued binary function given by the reciprocal-difference quotient on
;; nonzero inputs has value 1/33 at (3, 11). This file contains no proof.
;;
;; Only s(3,11) occurs in the conclusion. Instantiating the source hypothesis
;; at (3,11) gives the scalar antecedent below. Conversely, any scalar
;; satisfying that antecedent extends to a real function satisfying the source
;; formula on all nonzero inputs, by using the formula there and arbitrary
;; values elsewhere. Thus this scalar implication is bidirectionally
;; equivalent to the source statement. Its antecedent forces the scalar to an
;; exact rational value, so the unrestricted ACL2 parameter does not narrow
;; the source real domain.

(in-package "ACL2")

(defun mathd-algebra-139-statement (s-at-3-11)
  (implies
   (equal s-at-3-11
          (/ (- (/ 1 11)
                (/ 1 3))
             (- 3 11)))
   (equal s-at-3-11
          (/ 1 33))))

(value-triple :itpeval-statement-checked)
:q
