;; Statement-only formalization of miniF2F corpus artifact amc12b_2020_p2:
;; the real-number identity ((100^2 - 7^2) / (70^2 - 11^2)) times
;; (((70 - 11) * (70 + 11)) / ((100 - 7) * (100 + 7))) equals 1.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12b-2020-p2-statement ()
  (equal
   (* (/ (- (expt 100 2)
            (expt 7 2))
         (- (expt 70 2)
            (expt 11 2)))
      (/ (* (- 70 11)
            (+ 70 11))
         (* (- 100 7)
            (+ 100 7))))
   1))

(value-triple :itpeval-statement-checked)
:q
