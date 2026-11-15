;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_a2:
;; 181 is an odd prime factor of the 2015th term of the integer sequence
;; starting with 1, 2 and satisfying a(n) = 4*a(n-1) - a(n-2).
;; This file contains no proof.

(in-package "ACL2")

;; The source base cases and recurrence uniquely determine this integer-valued
;; sequence at every natural index.
(defun putnam-2015-a2-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      0
    (cond
     ((equal n 0) 1)
     ((equal n 1) 2)
     (t (- (* 4
              (putnam-2015-a2-sequence (- n 1)))
           (putnam-2015-a2-sequence (- n 2)))))))

(defun putnam-2015-a2-no-proper-divisor-through-p
    (number candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate))
          (<= candidate 1))
      t
    (and
     (not (equal (mod number candidate) 0))
     (putnam-2015-a2-no-proper-divisor-through-p
      number (- candidate 1)))))

(defun putnam-2015-a2-prime-p (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2015-a2-no-proper-divisor-through-p
    number (- number 1))))

(defun putnambench-putnam-2015-a2-statement ()
  (let ((solution 181))
    (and
     (equal (mod solution 2) 1)
     (putnam-2015-a2-prime-p solution)
     (equal
      (mod (putnam-2015-a2-sequence 2015)
           solution)
      0))))

(value-triple :itpeval-statement-checked)
:q
