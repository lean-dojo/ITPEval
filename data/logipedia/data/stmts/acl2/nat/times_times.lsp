;; Statement-only formalization of Logipedia corpus artifact nat.times_times,
;; catalog title "nat.times_times": for all natural numbers x, y, and z,
;; x times (y times z) equals y times (x times z). This file contains no proof.

(in-package "ACL2")

(defun logipedia-nat-times-times-statement (x y z)
  (implies
   (and (natp x)
        (natp y)
        (natp z))
   (equal (* x (* y z))
          (* y (* x z)))))

(value-triple :itpeval-statement-checked)
:q
