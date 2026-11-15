;; Statement-only formalization of miniF2F corpus artifact imo_1992_p1:
;; integers 1 < p < q < r such that (p - 1)*(q - 1)*(r - 1) divides
;; p*q*r - 1 must form (2, 4, 8) or (3, 5, 15). This file contains no proof.

(in-package "ACL2")

(defun imo-1992-p1-statement (p q r)
  (implies
   (and (integerp p)
        (integerp q)
        (integerp r)
        (< 1 p)
        (< p q)
        (< q r)
        (equal
         (mod (- (* (* p q) r) 1)
              (* (* (- p 1) (- q 1))
                 (- r 1)))
         0))
   (or (and (equal p 2)
            (equal q 4)
            (equal r 8))
       (and (equal p 3)
            (equal q 5)
            (equal r 15)))))

(value-triple :itpeval-statement-checked)
:q
