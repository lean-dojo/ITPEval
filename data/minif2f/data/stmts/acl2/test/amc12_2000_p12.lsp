;; Statement-only formalization of miniF2F artifact amc12_2000_p12: for
;; natural numbers a, m, and c whose sum is 12, the expression
;; a*m*c + a*m + m*c + a*c is at most 112. This file contains no proof.

(in-package "ACL2")

(defun amc12-2000-p12-statement (a m c)
  (implies (and (natp a)
                (natp m)
                (natp c)
                (equal (+ a (+ m c)) 12))
           (<= (+ (* a (* m c))
                  (+ (* a m)
                     (+ (* m c) (* a c))))
               112)))

(value-triple :itpeval-statement-checked)
:q
