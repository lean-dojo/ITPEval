;; Statement-only formalization of PutnamBench corpus artifact putnam_2017_b6:
;; the number of ordered 64-tuples of distinct elements of 1 through 2017
;; whose position-weighted sum is divisible by 2017 has the stated factorial
;; value. This file contains no proof.

(in-package "ACL2")

(defun putnam-2017-b6-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-2017-b6-factorial (- n 1)))))

;; POSITION is the next tuple index, CANDIDATE is the value currently being
;; considered there, and USED contains exactly the values at earlier indices.
;; Thus the recursion enumerates every admissible ordered tuple exactly once.
(defun putnam-2017-b6-count-tuples
    (position candidate used weighted-sum)
  (declare
   (xargs
    :measure
    (+
     (* 2018 (nfix (- 64 position)))
     (nfix (- 2018 candidate)))))
  (if (or (not (natp position))
          (not (natp candidate)))
      0
    (if (>= position 64)
        (if (equal (mod weighted-sum 2017) 0) 1 0)
      (if (> candidate 2017)
          0
        (+
         (if (member-equal candidate used)
             0
           (putnam-2017-b6-count-tuples
            (+ position 1)
            1
            (cons candidate used)
            (+
             weighted-sum
             (* (if (< position 2) 1 position)
                candidate))))
         (putnam-2017-b6-count-tuples
          position
          (+ candidate 1)
          used
          weighted-sum))))))

(defun putnambench-putnam-2017-b6-statement ()
  (equal
   (putnam-2017-b6-count-tuples 0 1 nil 0)
   (-
    (/ (putnam-2017-b6-factorial 2016)
       (putnam-2017-b6-factorial 1953))
    (* (putnam-2017-b6-factorial 63) 2016))))

(value-triple :itpeval-statement-checked)
:q
