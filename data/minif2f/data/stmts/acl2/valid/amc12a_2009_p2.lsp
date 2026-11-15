;; Statement-only formalization of miniF2F corpus artifact amc12a_2009_p2:
;; the nested rational expression 1 + 1/(1 + 1/(1 + 1)) equals 5/3.
;; This file contains no proof.

(in-package "ACL2")

(defun amc12a-2009-p2-statement ()
  (equal (+ 1
            (/ 1
               (+ 1
                  (/ 1
                     (+ 1 1)))))
         (/ 5 3)))

(value-triple :itpeval-statement-checked)
:q
