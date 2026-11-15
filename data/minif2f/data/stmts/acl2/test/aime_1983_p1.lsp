;; Statement-only formalization of miniF2F artifact aime_1983_p1: for natural
;; numbers x, y, and z greater than 1 and a nonnegative natural w, the
;; logarithmic equalities log_x(w) = 24, log_y(w) = 40, and log_(x*y*z)(w) =
;; 12 imply log_z(w) = 60, expressed here by their equivalent exact-power
;; equations. This file contains no proof.

(in-package "ACL2")

(defun aime-1983-p1-statement (x y z w)
  (implies (and (natp x)
                (natp y)
                (natp z)
                (natp w)
                (< 1 x)
                (< 1 y)
                (< 1 z)
                (equal w (expt x 24))
                (equal w (expt y 40))
                (equal w (expt (* x (* y z)) 12)))
           (equal w (expt z 60))))

(value-triple :itpeval-statement-checked)
:q
