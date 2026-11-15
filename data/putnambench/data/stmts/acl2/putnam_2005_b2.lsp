;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_b2:
;; the positive integer sequences with sum 5*n - 4 and reciprocal sum one
;; are exactly [1], the six permutations of [2,3,6], and [4,4,4,4]. This
;; file contains no proof.

(in-package "ACL2")

;; Proper natural-number lists represent the finite tuples from the Rocq
;; statement. They are also canonical representatives of the first n values
;; of the function encodings in Lean and Isabelle; values beyond n do not
;; occur in either the hypotheses or the classified solution.

(defun putnam-2005-b2-natural-list-p (values)
  (if (consp values)
      (and
       (natp (car values))
       (putnam-2005-b2-natural-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2005-b2-positive-integer-list-p (values)
  (if (consp values)
      (and
       (posp (car values))
       (putnam-2005-b2-positive-integer-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2005-b2-sum (values)
  (if (consp values)
      (+ (car values)
         (putnam-2005-b2-sum (cdr values)))
    0))

(defun putnam-2005-b2-reciprocal-sum (values)
  (if (consp values)
      (+ (/ (car values))
         (putnam-2005-b2-reciprocal-sum (cdr values)))
    0))

(defun putnam-2005-b2-equations-p (n values)
  (and
   (< 0 n)
   (putnam-2005-b2-positive-integer-list-p values)
   (equal (putnam-2005-b2-sum values)
          (- (* 5 n) 4))
   (equal (putnam-2005-b2-reciprocal-sum values)
          1)))

(defun putnam-2005-b2-listed-solution-p (n values)
  (or
   (and (equal n 1)
        (equal values '(1)))
   (and
    (equal n 3)
    (or (equal values '(2 3 6))
        (equal values '(2 6 3))
        (equal values '(3 2 6))
        (equal values '(3 6 2))
        (equal values '(6 2 3))
        (equal values '(6 3 2))))
   (and (equal n 4)
        (equal values '(4 4 4 4)))))

(defun putnambench-putnam-2005-b2-statement (n values)
  (implies
   (and
    (natp n)
    (true-listp values)
    (putnam-2005-b2-natural-list-p values)
    (equal (len values) n))
   (iff
    (putnam-2005-b2-equations-p n values)
    (putnam-2005-b2-listed-solution-p n values))))

(value-triple :itpeval-statement-checked)
:q
