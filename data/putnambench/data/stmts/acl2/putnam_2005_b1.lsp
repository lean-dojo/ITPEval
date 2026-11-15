;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_b1:
;; the nonzero real polynomial (y - 2*x)*(y - 2*x - 1) vanishes at
;; (floor(a), floor(2*a)) for every real a. This file contains no proof.

(in-package "ACL2")

;; For every real a, if n = floor(a), then floor(2*a) is either 2*n or
;; 2*n+1. Conversely, every pair (n, 2*n+b), for integer n and b in {0,1},
;; is realized by a real a: take a=n when b=0 and a=n+1/2 when b=1.
;; Thus the integer/bit universal closure below is bidirectionally equivalent
;; to the source's universal quantification over all real a.

(defun putnam-2005-b1-solution (x y)
  (* (- y (* 2 x))
     (- (- y (* 2 x)) 1)))

(defun putnam-2005-b1-branch-p (branch)
  (or (equal branch 0)
      (equal branch 1)))

(defun putnambench-putnam-2005-b1-statement (n branch)
  (and
   ;; Its value at (0,2) is 2, witnessing that the fixed polynomial is nonzero.
   (not (equal (putnam-2005-b1-solution 0 2) 0))
   (implies
    (and (integerp n)
         (putnam-2005-b1-branch-p branch))
    (equal
     (putnam-2005-b1-solution
      n
      (+ (* 2 n) branch))
     0))))

(value-triple :itpeval-statement-checked)
:q
