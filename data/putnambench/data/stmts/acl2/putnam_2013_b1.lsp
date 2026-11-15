;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_b1:
;; the integer sequence defined by c(1)=1, c(2n)=c(n), and
;; c(2n+1)=(-1)^n*c(n) has sum c(n)*c(n+2), for 1 <= n <= 2013,
;; equal to -1. This file contains no proof.

(in-package "ACL2")

;; The source assumptions uniquely determine every positive-index value of c.
;; STEPS is internal recursion fuel; starting it at N is more than sufficient
;; because each recursive call replaces a positive N greater than 1 by
;; floor(N/2).
(defun putnam-2013-b1-c-aux (n steps)
  (declare (xargs :measure (nfix steps)))
  (if (or (zp steps)
          (not (posp n)))
      0
    (if (equal n 1)
        1
      (let ((half (floor n 2)))
        (* (if (equal (mod n 2) 0)
               1
             (expt -1 half))
           (putnam-2013-b1-c-aux
            half (- steps 1)))))))

(defun putnam-2013-b1-c (n)
  (if (posp n)
      (putnam-2013-b1-c-aux n n)
    0))

;; Inclusive sum from 1 through N of c(n)*c(n+2).
(defun putnam-2013-b1-sum-through (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (+ (putnam-2013-b1-sum-through (- n 1))
       (* (putnam-2013-b1-c n)
          (putnam-2013-b1-c (+ n 2))))))

;; Substituting the uniquely defined positive part of c for the arbitrary
;; source function preserves the hypotheses and the finite-sum conclusion.
(defun putnambench-putnam-2013-b1-statement ()
  (equal (putnam-2013-b1-sum-through 2013)
         -1))

(value-triple :itpeval-statement-checked)
:q
