;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_a1:
;; the number of ordered triples of sets with union {1,...,10} and empty
;; triple intersection has prime exponents (10,10,0,0). This file contains
;; no proof.

(in-package "ACL2")

;; The union condition forces each source set to be a subset of {1,...,10}.
;; Such a set has a unique mask in {0,...,2^10-1}, whose bit E-1 records
;; membership of E. Thus triples of masks are in bijection with the source
;; ordered triples, and the test below expresses the union and intersection
;; conditions at every element.
(defun putnam-1985-a1-mask-member-p (element mask)
  (and
   (natp element)
   (< 0 element)
   (<= element 10)
   (natp mask)
   (< mask (expt 2 10))
   (equal
    (mod (floor mask (expt 2 (- element 1))) 2)
    1)))

(defun putnam-1985-a1-admissible-through-p
    (a1 a2 a3 remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((in-a1
           (putnam-1985-a1-mask-member-p remaining a1))
          (in-a2
           (putnam-1985-a1-mask-member-p remaining a2))
          (in-a3
           (putnam-1985-a1-mask-member-p remaining a3)))
      (and
       (or in-a1 in-a2 in-a3)
       (not (and in-a1 in-a2 in-a3))
       (putnam-1985-a1-admissible-through-p
        a1 a2 a3 (- remaining 1))))))

(defun putnam-1985-a1-admissible-triple-p (a1 a2 a3)
  (and
   (natp a1)
   (< a1 (expt 2 10))
   (natp a2)
   (< a2 (expt 2 10))
   (natp a3)
   (< a3 (expt 2 10))
   (putnam-1985-a1-admissible-through-p a1 a2 a3 10)))

(defun putnam-1985-a1-count-a3 (a1 a2 a3-count)
  (declare (xargs :measure (nfix a3-count)))
  (if (zp a3-count)
      0
    (let ((a3 (- a3-count 1)))
      (+
       (if (putnam-1985-a1-admissible-triple-p a1 a2 a3)
           1
         0)
       (putnam-1985-a1-count-a3 a1 a2 a3)))))

(defun putnam-1985-a1-count-a2 (a1 a2-count)
  (declare (xargs :measure (nfix a2-count)))
  (if (zp a2-count)
      0
    (let ((a2 (- a2-count 1)))
      (+
       (putnam-1985-a1-count-a3 a1 a2 (expt 2 10))
       (putnam-1985-a1-count-a2 a1 a2)))))

(defun putnam-1985-a1-count-a1 (a1-count)
  (declare (xargs :measure (nfix a1-count)))
  (if (zp a1-count)
      0
    (let ((a1 (- a1-count 1)))
      (+
       (putnam-1985-a1-count-a2 a1 (expt 2 10))
       (putnam-1985-a1-count-a1 a1)))))

(defun putnam-1985-a1-triple-count ()
  (putnam-1985-a1-count-a1 (expt 2 10)))

(defun putnambench-putnam-1985-a1-statement ()
  (equal
   (putnam-1985-a1-triple-count)
   (* (* (expt 2 10)
         (expt 3 10))
      (* (expt 5 0)
         (expt 7 0)))))

(value-triple :itpeval-statement-checked)
:q
