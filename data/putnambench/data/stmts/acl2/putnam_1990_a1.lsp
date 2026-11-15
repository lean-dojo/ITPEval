;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_a1:
;; the integer sequence with initial values 2, 3, 6 and the given third-order
;; recurrence has closed form n! + 2^n. This file contains no proof.

(in-package "ACL2")

(defun putnam-1990-a1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1990-a1-factorial (- n 1)))))

;; The source assumptions uniquely determine T at every natural index.
;; This recursive function has exactly the source initial values and
;; recurrence, so replacing arbitrary T by it is bidirectionally equivalent:
;; every source T agrees with this function by induction, and this function
;; itself is a source instance.
(defun putnam-1990-a1-sequence-value (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      0
    (cond
     ((equal n 0) 2)
     ((equal n 1) 3)
     ((equal n 2) 6)
     (t
      (-
       (+
        (* (+ n 4)
           (putnam-1990-a1-sequence-value (- n 1)))
        (* (- (* 4 n) 8)
           (putnam-1990-a1-sequence-value (- n 3))))
       (* 4 n
          (putnam-1990-a1-sequence-value (- n 2))))))))

(defun putnambench-putnam-1990-a1-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-1990-a1-sequence-value n)
    (+ (putnam-1990-a1-factorial n)
       (expt 2 n)))))

(value-triple :itpeval-statement-checked)
:q
