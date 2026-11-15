;; Statement-only formalization of Logipedia corpus artifact nat.pred_Sn,
;; catalog title "nat.pred_Sn": every natural number is the predecessor of
;; its successor. This file contains no proof.

(in-package "ACL2")

(defun-sk logipedia-nat-pred-sn-statement ()
  (forall (n)
    (implies
     (natp n)
     (equal
      n
      (nfix (- (+ n 1) 1))))))

(value-triple :itpeval-statement-checked)
:q
