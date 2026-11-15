;; Statement-only formalization of miniF2F corpus artifact imo_1977_p5:
;; natural numbers a, b, q, and r satisfying the stated remainder and
;; quadratic equations have absolute distances from 22 equal to 15 and 28,
;; in either order. This file contains no proof.

(in-package "ACL2")

(defun imo-1977-p5-statement (a b q r)
  (implies
   (and (natp a)
        (natp b)
        (natp q)
        (natp r)
        (< r (+ a b))
        (equal (+ (expt a 2)
                  (expt b 2))
               (+ (* (+ a b) q)
                  r))
        (equal (+ (expt q 2) r)
               1977))
   (or (and (equal (abs (- a 22)) 15)
            (equal (abs (- b 22)) 28))
       (and (equal (abs (- a 22)) 28)
            (equal (abs (- b 22)) 15)))))

(value-triple :itpeval-statement-checked)
:q
