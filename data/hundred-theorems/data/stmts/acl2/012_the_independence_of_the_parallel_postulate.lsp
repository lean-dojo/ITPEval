;; Statement-only formalization of Hundred Theorems artifact 012,
;; "The Independence of the Parallel Postulate": an exact rational-coordinate
;; form of the Klein-disk counterexample refuting Tarski's Euclidean axiom
;; (axiom 10), the non-Euclidean half of the independence result. This file
;; contains no proof.

(in-package "ACL2")

(defun ht-012-klein-pointp (x y)
  (and (rationalp x)
       (rationalp y)
       (< (+ (* x x) (* y y)) 1)))

(defun ht-012-point-equalp (x1 y1 x2 y2)
  (and (equal x1 x2)
       (equal y1 y2)))

(defun ht-012-euclidean-betweenp (px py ax ay bx by)
  (and (rationalp px)
       (rationalp py)
       (rationalp ax)
       (rationalp ay)
       (rationalp bx)
       (rationalp by)
       (equal (* (- px ax) (- by ay))
              (* (- py ay) (- bx ax)))
       (<= (+ (* (- px ax) (- px bx))
              (* (- py ay) (- py by)))
           0)))

(defun ht-012-pbetweenp (px py ax ay bx by)
  (and (ht-012-klein-pointp px py)
       (ht-012-klein-pointp ax ay)
       (ht-012-klein-pointp bx by)
       (ht-012-euclidean-betweenp px py ax ay bx by)))

(defun hundred-theorems-012-statement (x1 y1 x2 y2)
  (implies
   (and (ht-012-klein-pointp x1 y1)
        (ht-012-klein-pointp x2 y2))
   (and
    (ht-012-pbetweenp (/ 1 4) (/ 1 4)
                      0 0
                      (/ 3 5) (/ 3 5))
    (ht-012-pbetweenp (/ 1 4) (/ 1 4)
                      (/ 1 2) 0
                      0 (/ 1 2))
    (not (ht-012-point-equalp 0 0 (/ 1 4) (/ 1 4)))
    (not
     (and
      (ht-012-pbetweenp (/ 1 2) 0
                        0 0
                        x1 y1)
      (ht-012-pbetweenp 0 (/ 1 2)
                        0 0
                        x2 y2)
      (ht-012-pbetweenp (/ 3 5) (/ 3 5)
                        x1 y1
                        x2 y2))))))

(value-triple :itpeval-statement-checked)
:q
