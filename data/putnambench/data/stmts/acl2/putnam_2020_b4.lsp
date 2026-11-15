;; Statement-only formalization of PutnamBench corpus artifact putnam_2020_b4:
;; the average reciprocal of one plus the sum of powers of three along all
;; length-4040 integer unit-step walks from zero back to zero is 1/4040.
;; This file contains no proof.

(in-package "ACL2")

;; A walk in the source set is uniquely determined by its 4040 successive
;; choices of +1 or -1. Conversely, every such choice sequence ending at zero
;; extends uniquely to the source function by setting every later value to
;; zero. Thus the recursion below enumerates the source set bijectively.

(defun putnam-2020-b4-power-of-three (height)
  (if (and (integerp height)
           (< height 0))
      (/ 1 (expt 3 (- height)))
    (expt 3 (nfix height))))

(defun putnam-2020-b4-walk-count (steps-left height)
  (declare (xargs :measure (nfix steps-left)))
  (if (zp steps-left)
      (if (equal height 0) 1 0)
    (+ (putnam-2020-b4-walk-count
        (- (nfix steps-left) 1)
        (+ height 1))
       (putnam-2020-b4-walk-count
        (- (nfix steps-left) 1)
        (- height 1)))))

;; Q-SO-FAR starts at 1. After a step reaches position j, its 3^height term
;; is added exactly when j is an interior position, so the endpoint j = 4040
;; is excluded just as in the source sum from 1 through 4039. Invalid walks
;; contribute zero at the leaf; valid walks contribute their exact reciprocal.

(defun putnam-2020-b4-reciprocal-sum
    (steps-left height q-so-far)
  (declare (xargs :measure (nfix steps-left)))
  (if (zp steps-left)
      (if (equal height 0)
          (/ 1 q-so-far)
        0)
    (let* ((remaining (- (nfix steps-left) 1))
           (up-height (+ height 1))
           (down-height (- height 1))
           (up-q
            (if (zp remaining)
                q-so-far
              (+ q-so-far
                 (putnam-2020-b4-power-of-three
                  up-height))))
           (down-q
            (if (zp remaining)
                q-so-far
              (+ q-so-far
                 (putnam-2020-b4-power-of-three
                  down-height)))))
      (+ (putnam-2020-b4-reciprocal-sum
          remaining up-height up-q)
         (putnam-2020-b4-reciprocal-sum
          remaining down-height down-q)))))

(defun putnam-2020-b4-average ()
  (/ (putnam-2020-b4-reciprocal-sum 4040 0 1)
     (putnam-2020-b4-walk-count 4040 0)))

(defun putnambench-putnam-2020-b4-statement ()
  (equal
   (putnam-2020-b4-average)
   (/ 1 4040)))

(value-triple :itpeval-statement-checked)
:q
