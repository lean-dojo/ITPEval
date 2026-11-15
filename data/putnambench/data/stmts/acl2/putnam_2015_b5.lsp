;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_b5:
;; the permutation count with adjacent images at distance at most two has
;; P_(n+5) - P_(n+4) - P_(n+3) + P_n equal to 4 for every n >= 2.
;; This file contains no proof.

(in-package "ACL2")

;; A permutation is represented by its image list in the domain order
;; 1,...,n. Inserting each value into every position enumerates every
;; permutation exactly once. The source condition for all i,j with
;; |i-j| = 1 is therefore exactly the adjacent-entry test below.

(defun putnam-2015-b5-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2015-b5-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2015-b5-prefix-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-2015-b5-prefix-each value (cdr lists)))))

(defun putnam-2015-b5-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-2015-b5-prefix-each
      (car values)
      (putnam-2015-b5-insert-everywhere
       value (cdr values))))))

(defun putnam-2015-b5-insert-into-each (value lists)
  (if (endp lists)
      nil
    (append
     (putnam-2015-b5-insert-everywhere value (car lists))
     (putnam-2015-b5-insert-into-each value (cdr lists)))))

(defun putnam-2015-b5-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-2015-b5-insert-into-each
     (car values)
     (putnam-2015-b5-permutations (cdr values)))))

(defun putnam-2015-b5-natural-distance (left right)
  (if (<= left right)
      (- right left)
    (- left right)))

(defun putnam-2015-b5-admissible-permutation-p (permutation)
  (if (and (consp permutation)
           (consp (cdr permutation)))
      (and
       (<=
        (putnam-2015-b5-natural-distance
         (car permutation) (car (cdr permutation)))
        2)
       (putnam-2015-b5-admissible-permutation-p
        (cdr permutation)))
    t))

(defun putnam-2015-b5-count-admissible (permutations)
  (if (endp permutations)
      0
    (+
     (if
         (putnam-2015-b5-admissible-permutation-p
          (car permutations))
         1
       0)
     (putnam-2015-b5-count-admissible
      (cdr permutations)))))

(defun putnam-2015-b5-p (n)
  (if (natp n)
      (putnam-2015-b5-count-admissible
       (putnam-2015-b5-permutations
        (putnam-2015-b5-range-from 1 n)))
    0))

(defun putnambench-putnam-2015-b5-statement (n)
  (implies
   (and (natp n)
        (<= 2 n))
   (equal
    (+
     (-
      (-
       (putnam-2015-b5-p (+ n 5))
       (putnam-2015-b5-p (+ n 4)))
      (putnam-2015-b5-p (+ n 3)))
     (putnam-2015-b5-p n))
    4)))

(value-triple :itpeval-statement-checked)
:q
