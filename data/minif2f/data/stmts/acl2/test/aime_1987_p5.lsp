;; Statement-only formalization of miniF2F artifact aime_1987_p5: for integers
;; x and y, the Diophantine equation y^2 + 3 * (x^2 * y^2) =
;; 30 * x^2 + 517 implies 3 * (x^2 * y^2) = 588. This file contains no
;; proof.

(in-package "ACL2")

(defun aime-1987-p5-statement (x y)
  (implies (and (integerp x)
                (integerp y)
                (equal (+ (expt y 2)
                          (* 3
                             (* (expt x 2)
                                (expt y 2))))
                       (+ (* 30 (expt x 2))
                          517)))
           (equal (* 3
                     (* (expt x 2)
                        (expt y 2)))
                  588)))

(value-triple :itpeval-statement-checked)
:q
