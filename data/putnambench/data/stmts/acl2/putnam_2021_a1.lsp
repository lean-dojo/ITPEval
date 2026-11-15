;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_a1:
;; the least number of length-5 hops between integer lattice points from
;; (0,0) to (2021,2021) is 578. This file contains no proof.

(in-package "ACL2")

;; The integer solutions of dx^2 + dy^2 = 25 are exactly
;;
;;   (+/-5,0), (0,+/-5), (+/-4,+/-3), and (+/-3,+/-4).
;;
;; Recursing over these twelve moves therefore searches exactly all
;; integer-coordinate hop sequences of the requested length. The search keeps
;; the source existential path witness internal to the predicate.
(defun putnam-2021-a1-path-exists-p (steps x y)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (and (equal x 2021)
           (equal y 2021))
    (let ((remaining (- steps 1)))
      (or
       (putnam-2021-a1-path-exists-p remaining (+ x 5) y)
       (putnam-2021-a1-path-exists-p remaining (- x 5) y)
       (putnam-2021-a1-path-exists-p remaining x (+ y 5))
       (putnam-2021-a1-path-exists-p remaining x (- y 5))
       (putnam-2021-a1-path-exists-p remaining (+ x 4) (+ y 3))
       (putnam-2021-a1-path-exists-p remaining (+ x 4) (- y 3))
       (putnam-2021-a1-path-exists-p remaining (- x 4) (+ y 3))
       (putnam-2021-a1-path-exists-p remaining (- x 4) (- y 3))
       (putnam-2021-a1-path-exists-p remaining (+ x 3) (+ y 4))
       (putnam-2021-a1-path-exists-p remaining (+ x 3) (- y 4))
       (putnam-2021-a1-path-exists-p remaining (- x 3) (+ y 4))
       (putnam-2021-a1-path-exists-p remaining (- x 3) (- y 4))))))

;; Check every natural hop count from LIMIT down through zero. This is the
;; universal lower-bound half of leastness, rather than a finite replacement
;; for the path objects themselves.
(defun putnam-2021-a1-no-path-through-p (limit)
  (declare (xargs :measure (nfix limit)))
  (and
   (not (putnam-2021-a1-path-exists-p limit 0 0))
   (or (zp limit)
       (putnam-2021-a1-no-path-through-p (- limit 1)))))

;; Existence at 578 together with nonexistence below 578 is bidirectionally
;; equivalent to the source IsLeast/LEAST assertion after expanding P_def and
;; substituting the annotated solution value.
(defun putnambench-putnam-2021-a1-statement ()
  (and
   (putnam-2021-a1-path-exists-p 578 0 0)
   (putnam-2021-a1-no-path-through-p 577)))

(value-triple :itpeval-statement-checked)
:q
