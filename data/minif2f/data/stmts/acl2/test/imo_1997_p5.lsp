;; Statement-only formalization of miniF2F corpus artifact imo_1997_p5:
;; positive natural numbers x and y satisfying x^(y^2) = y^x must be (1, 1),
;; (16, 2), or (27, 3). This file contains no proof.

(in-package "ACL2")

(defun imo-1997-p5-statement (x y)
  (implies
   (and (natp x)
        (natp y)
        (< 0 x)
        (< 0 y)
        (equal (expt x (expt y 2))
               (expt y x)))
   (or (and (equal x 1)
            (equal y 1))
       (and (equal x 16)
            (equal y 2))
       (and (equal x 27)
            (equal y 3)))))

(value-triple :itpeval-statement-checked)
:q
