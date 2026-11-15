;; Statement-only formalization of PutnamBench artifact putnam_1965_a5:
;; for every positive natural n, the number of orderings of 1 through n in
;; which each entry after the first differs by one from an earlier entry is
;; 2 raised to n - 1. This file contains no proof.

(in-package "ACL2")

;; PUTNAM-1965-A5-RANGE-FROM constructs the canonical carrier
;; START, START+1, ..., START+COUNT-1.
(defun putnam-1965-a5-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1965-a5-range-from
           (+ start 1) (- count 1)))))

(defun putnam-1965-a5-prepend-to-each (value lists)
  (if (consp lists)
      (cons (cons value (car lists))
            (putnam-1965-a5-prepend-to-each
             value (cdr lists)))
    nil))

(defun putnam-1965-a5-insert-everywhere (value values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (cons (cons value values)
            (putnam-1965-a5-prepend-to-each
             (car values)
             (putnam-1965-a5-insert-everywhere
              value (cdr values))))
    (list (list value))))

(defun putnam-1965-a5-insert-into-each-permutation
    (value permutations)
  (if (consp permutations)
      (append
       (putnam-1965-a5-insert-everywhere
        value (car permutations))
       (putnam-1965-a5-insert-into-each-permutation
        value (cdr permutations)))
    nil))

;; For a duplicate-free input list, this enumerates every permutation
;; exactly once as its image list in position order.
(defun putnam-1965-a5-permutations (values)
  (if (consp values)
      (putnam-1965-a5-insert-into-each-permutation
       (car values)
       (putnam-1965-a5-permutations (cdr values)))
    (list nil)))

(defun putnam-1965-a5-has-earlier-neighbor-p
    (value earlier-values)
  (if (consp earlier-values)
      (or (equal value (+ (car earlier-values) 1))
          (equal (car earlier-values) (+ value 1))
          (putnam-1965-a5-has-earlier-neighbor-p
           value (cdr earlier-values)))
    nil))

(defun putnam-1965-a5-valid-tail-p
    (remaining-values earlier-values)
  (if (consp remaining-values)
      (and
       (putnam-1965-a5-has-earlier-neighbor-p
        (car remaining-values) earlier-values)
       (putnam-1965-a5-valid-tail-p
        (cdr remaining-values)
        (cons (car remaining-values) earlier-values)))
    t))

(defun putnam-1965-a5-valid-ordering-p (ordering)
  (and (consp ordering)
       (putnam-1965-a5-valid-tail-p
        (cdr ordering) (list (car ordering)))))

(defun putnam-1965-a5-count-valid-orderings (orderings)
  (if (consp orderings)
      (+ (if (putnam-1965-a5-valid-ordering-p
              (car orderings))
             1
           0)
         (putnam-1965-a5-count-valid-orderings
          (cdr orderings)))
    0))

(defun putnambench-putnam-1965-a5-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-1965-a5-count-valid-orderings
     (putnam-1965-a5-permutations
      (putnam-1965-a5-range-from 1 n)))
    (expt 2 (- n 1)))))

(value-triple :itpeval-statement-checked)
:q
