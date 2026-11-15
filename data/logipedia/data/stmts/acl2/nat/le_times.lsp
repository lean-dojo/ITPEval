;; Statement-only formalization of Logipedia corpus artifact nat.le_times,
;; catalog title "nat.le_times": componentwise less-than-or-equal on natural
;; numbers is preserved by multiplication. This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-le-times-statement (n1 n2 m1 m2)
  (implies
   (and (natp n1)
        (natp n2)
        (natp m1)
        (natp m2)
        (<= n1 n2)
        (<= m1 m2))
   (<= (* n1 m1)
       (* n2 m2))))

(value-triple :itpeval-statement-checked)
:q
