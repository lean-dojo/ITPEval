;; Statement-only formalization of miniF2F corpus artifact amc12a_2020_p7:
;; for the seven natural values a(0) through a(6), whose cubes are 1, 8, 27,
;; 64, 125, 216, and 343, six times their sum of squares minus twice the sum
;; of the first six squares is 658. This file contains no proof.

(in-package "ACL2")

;; Only a(0) through a(6) occur in the source proposition. Restriction gives
;; the seven parameters below, and every such natural tuple extends to a total
;; natural-valued function by assigning arbitrary values at all other indices.

(defun amc12a-2020-p7-statement (a0 a1 a2 a3 a4 a5 a6)
  (implies
   (and (natp a0)
        (natp a1)
        (natp a2)
        (natp a3)
        (natp a4)
        (natp a5)
        (natp a6)
        (equal (expt a0 3) 1)
        (equal (expt a1 3) 8)
        (equal (expt a2 3) 27)
        (equal (expt a3 3) 64)
        (equal (expt a4 3) 125)
        (equal (expt a5 3) 216)
        (equal (expt a6 3) 343))
   (equal
    (- (* 6
          (+ (+ (+ (expt a0 2)
                   (expt a1 2))
                (+ (expt a2 2)
                   (expt a3 2)))
             (+ (+ (expt a4 2)
                   (expt a5 2))
                (expt a6 2))))
       (* 2
          (+ (+ (+ (expt a0 2)
                   (expt a1 2))
                (+ (expt a2 2)
                   (expt a3 2)))
             (+ (expt a4 2)
                (expt a5 2)))))
    658)))

(value-triple :itpeval-statement-checked)
:q
