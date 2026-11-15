;; Statement-only formalization of PutnamBench artifact putnam_1964_a1:
;; among six distinct points in the real plane, the longest pairwise distance
;; divided by the shortest is at least sqrt(3). This file contains no proof.

(in-package "ACL2")

;; ACL2's exact rational plane is bidirectionally equivalent to the source
;; theorem over the real plane. A counterexample has
;;   max(pairwise distance squared) < 3 * min(pairwise distance squared).
;; Distinctness makes the minimum positive, and this strict inequality is an
;; open condition on the twelve coordinates because finite minima and maxima
;; of continuous functions are continuous. A real counterexample therefore
;; persists under a small rational perturbation; the converse is immediate.

(defun putnam-1964-a1-point-p (point)
  (and (consp point)
       (rationalp (car point))
       (rationalp (cdr point))))

(defun putnam-1964-a1-point-list-p (points)
  (if (consp points)
      (and (putnam-1964-a1-point-p (car points))
           (putnam-1964-a1-point-list-p (cdr points)))
    (equal points nil)))

(defun putnam-1964-a1-square (x)
  (* x x))

(defun putnam-1964-a1-distance-squared (first second)
  (+ (putnam-1964-a1-square (- (car first) (car second)))
     (putnam-1964-a1-square (- (cdr first) (cdr second)))))

(defun putnam-1964-a1-distances-from (point remaining)
  (if (consp remaining)
      (cons (putnam-1964-a1-distance-squared point (car remaining))
            (putnam-1964-a1-distances-from point (cdr remaining)))
    nil))

(defun putnam-1964-a1-pairwise-distances-squared (points)
  (if (consp points)
      (append
       (putnam-1964-a1-distances-from (car points) (cdr points))
       (putnam-1964-a1-pairwise-distances-squared (cdr points)))
    nil))

(defun putnam-1964-a1-minimum (values)
  (if (endp (cdr values))
      (car values)
    (let ((tail-minimum (putnam-1964-a1-minimum (cdr values))))
      (if (< (car values) tail-minimum)
          (car values)
        tail-minimum))))

(defun putnam-1964-a1-maximum (values)
  (if (endp (cdr values))
      (car values)
    (let ((tail-maximum (putnam-1964-a1-maximum (cdr values))))
      (if (< tail-maximum (car values))
          (car values)
        tail-maximum))))

(defun putnambench-putnam-1964-a1-statement (points)
  (implies
   (and (true-listp points)
        (equal (len points) 6)
        (putnam-1964-a1-point-list-p points)
        (no-duplicatesp-equal points))
   (let ((distances-squared
          (putnam-1964-a1-pairwise-distances-squared points)))
     (<= (* 3 (putnam-1964-a1-minimum distances-squared))
         (putnam-1964-a1-maximum distances-squared)))))

(value-triple :itpeval-statement-checked)
:q
