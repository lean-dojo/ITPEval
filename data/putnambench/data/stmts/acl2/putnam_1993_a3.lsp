;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_a3:
;; the number of functions from the subsets of an n-element set to
;; {1,...,m} that send intersections to minima is sum_{j=1}^m j^n.
;; This file contains no proof.

(in-package "ACL2")

;; Subsets of {1,...,n} are represented by their n-bit characteristic
;; numbers, exactly the naturals below 2^n. A function on this power set is
;; represented by the 2^n base-m digits of a natural below m^(2^n), with
;; digit d corresponding to source value d+1. These encodings are bijective,
;; and adding one preserves both equality and minimum, so the predicates
;; below count exactly the source function space rather than an approximation.

(defun putnam-1993-a3-function-value
    (function-code subset-code m)
  (mod
   (floor function-code (expt m subset-code))
   m))

(defun putnam-1993-a3-subset-intersection
    (left right remaining-bits)
  (declare (xargs :measure (nfix remaining-bits)))
  (if (zp remaining-bits)
      0
    (+
     (if (and (equal (mod left 2) 1)
              (equal (mod right 2) 1))
         1
       0)
     (*
      2
      (putnam-1993-a3-subset-intersection
       (floor left 2)
       (floor right 2)
       (- remaining-bits 1))))))

(defun putnam-1993-a3-pairs-for-left-p
    (function-code left remaining-right m n)
  (declare (xargs :measure (nfix remaining-right)))
  (if (zp remaining-right)
      t
    (let* ((right (- remaining-right 1))
           (left-value
            (putnam-1993-a3-function-value
             function-code left m))
           (right-value
            (putnam-1993-a3-function-value
             function-code right m))
           (intersection
            (putnam-1993-a3-subset-intersection
             left right n))
           (intersection-value
            (putnam-1993-a3-function-value
             function-code intersection m)))
      (and
       (equal
        intersection-value
        (if (< left-value right-value)
            left-value
          right-value))
       (putnam-1993-a3-pairs-for-left-p
        function-code left right m n)))))

(defun putnam-1993-a3-meet-preserving-p
    (function-code remaining-left subset-count m n)
  (declare (xargs :measure (nfix remaining-left)))
  (if (zp remaining-left)
      t
    (let ((left (- remaining-left 1)))
      (and
       (putnam-1993-a3-pairs-for-left-p
        function-code left subset-count m n)
       (putnam-1993-a3-meet-preserving-p
        function-code left subset-count m n)))))

(defun putnam-1993-a3-count-functions
    (remaining-functions subset-count m n)
  (declare (xargs :measure (nfix remaining-functions)))
  (if (zp remaining-functions)
      0
    (let ((function-code (- remaining-functions 1)))
      (+
       (if (putnam-1993-a3-meet-preserving-p
            function-code subset-count subset-count m n)
           1
         0)
       (putnam-1993-a3-count-functions
        function-code subset-count m n)))))

(defun putnam-1993-a3-power-sum (n upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      0
    (+
     (expt upper n)
     (putnam-1993-a3-power-sum n (- upper 1)))))

(defun putnambench-putnam-1993-a3-statement (n m)
  (implies
   (and
    (posp n)
    (posp m))
   (let ((subset-count (expt 2 n)))
     (equal
      (putnam-1993-a3-count-functions
       (expt m subset-count)
       subset-count
       m
       n)
      (putnam-1993-a3-power-sum n m)))))

(value-triple :itpeval-statement-checked)
:q
