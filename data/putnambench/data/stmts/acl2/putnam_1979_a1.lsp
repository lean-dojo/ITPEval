;; Statement-only formalization of PutnamBench corpus artifact putnam_1979_a1:
;; among nonempty finite multisets of positive integers with sum 1979, one 2
;; together with 659 copies of 3 has greatest product. This file contains no
;; proof.

(in-package "ACL2")

;; Proper lists represent finite multisets. Admissibility, sum, and product are
;; invariant under permutation, and every finite multiset has such a list
;; representative. The free competitor argument is therefore the source
;; universal quantifier over finite multisets.

(defun putnam-1979-a1-positive-integer-list-p (values)
  (if (consp values)
      (and
       (posp (car values))
       (putnam-1979-a1-positive-integer-list-p
        (cdr values)))
    (equal values nil)))

(defun putnam-1979-a1-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-1979-a1-sum (cdr values)))
    0))

(defun putnam-1979-a1-product (values)
  (if (consp values)
      (* (car values)
         (putnam-1979-a1-product (cdr values)))
    1))

(defun putnam-1979-a1-repeat (count value)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons value
          (putnam-1979-a1-repeat
           (- count 1) value))))

(defun putnam-1979-a1-solution ()
  (cons 2 (putnam-1979-a1-repeat 659 3)))

(defun putnam-1979-a1-admissible-p (values)
  (and
   (true-listp values)
   (consp values)
   (putnam-1979-a1-positive-integer-list-p values)
   (equal (putnam-1979-a1-sum values) 1979)))

(defun putnambench-putnam-1979-a1-statement (competitor)
  (let ((solution (putnam-1979-a1-solution)))
    (and
     (putnam-1979-a1-admissible-p solution)
     (implies
      (putnam-1979-a1-admissible-p competitor)
      (>= (putnam-1979-a1-product solution)
          (putnam-1979-a1-product competitor))))))

(value-triple :itpeval-statement-checked)
:q
