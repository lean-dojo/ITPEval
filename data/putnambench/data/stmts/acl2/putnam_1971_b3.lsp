;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_b3:
;; the Lebesgue measure of the real times at which one car has completed
;; exactly twice as many laps as a later-starting car is one hour. This file
;; contains no proof.

(in-package "ACL2")

;; Write the positive real delay as T = n + a, where n = floor(T) and
;; 0 <= a < 1.  After translating t by T, split u = t - T >= 0 into the
;; unit cells k <= u < k+1.  Writing u = k+s, the source floor equality is
;;
;;   floor(n+a+k+s) = 2*k.
;;
;; Thus the contribution of cell k is the length of the intersection of
;; [0,1) with [k-n-a, k+1-n-a).  Cells above n+1 are empty, so the finite
;; sum below is exactly the source set's Lebesgue measure.
;;
;; The resulting measure is a rational piecewise-linear expression in a,
;; with rational breakpoints.  Its equality to 1 for every real a in [0,1)
;; is equivalent to its equality for every rational a there: a real failure
;; inside a linear piece persists at a nearby rational, and every breakpoint
;; is rational.  Hence rationalp is an exact validity encoding here, not a
;; restriction of the source's arbitrary real delay.

(defun putnam-1971-b3-cell-measure (n a k)
  (let* ((lower (- (- k n) a))
         (upper (+ lower 1))
         (left (if (< lower 0) 0 lower))
         (right (if (< 1 upper) 1 upper)))
    (if (< left right)
        (- right left)
      0)))

(defun putnam-1971-b3-measure-sum (n a k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      (putnam-1971-b3-cell-measure n a 0)
    (+ (putnam-1971-b3-cell-measure n a k)
       (putnam-1971-b3-measure-sum n a (- k 1)))))

(defun putnambench-putnam-1971-b3-statement (n a)
  (implies
   (and
    (natp n)
    (rationalp a)
    (<= 0 a)
    (< a 1)
    (or (< 0 n)
        (< 0 a)))
   (equal
    (putnam-1971-b3-measure-sum n a (+ n 1))
    1)))

(value-triple :itpeval-statement-checked)
:q
