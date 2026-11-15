;; Statement-only formalization of PutnamBench artifact putnam_1966_a1:
;; for positive integers x > y, the product x*y equals the difference of
;; two inclusive partial sums of the sequence 0, 0, 1, 1, 2, 2, ...
;; This file contains no proof.

(in-package "ACL2")

;; This is the source term m/2 for even m and (m-1)/2 for odd m.
(defun putnam-1966-a1-sequence-term (m)
  (if (equal (mod m 2) 0)
      (/ m 2)
    (/ (- m 1) 2)))

;; This recursively represents the inclusive sum from m = 0 through n.
(defun putnam-1966-a1-sum-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1966-a1-sequence-term 0)
    (+ (putnam-1966-a1-sum-through (- n 1))
       (putnam-1966-a1-sequence-term n))))

;; The source function f has been eliminated by substituting its defining
;; inclusive sum. Under x > y > 0, both sum bounds are natural numbers.
(defun putnambench-putnam-1966-a1-statement (x y)
  (implies
   (and (integerp x)
        (integerp y)
        (< 0 x)
        (< 0 y)
        (< y x))
   (equal
    (* x y)
    (- (putnam-1966-a1-sum-through (+ x y))
       (putnam-1966-a1-sum-through (- x y))))))

(value-triple :itpeval-statement-checked)
:q
