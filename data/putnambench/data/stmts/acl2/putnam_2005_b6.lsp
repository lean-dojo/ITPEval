;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_b6:
;; the signed sum over permutations of 1 through n, weighted by the reciprocal
;; of one plus the number of fixed points, equals (-1)^(n+1)*n/(n+1).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A permutation is its image list in the canonical domain order 1,...,n.
;; Insertion generates every such list exactly once. This is bijective with
;; permutations of Fin n and with permutations of the naturals supported on
;; {1,...,n}; the latter extend each list uniquely by fixing all other values.

(defun putnam-2005-b6-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2005-b6-range-from
           (+ start 1)
           (- count 1)))))

(defun putnam-2005-b6-prefix-each (item lists)
  (if (consp lists)
      (cons
       (cons item (car lists))
       (putnam-2005-b6-prefix-each item (cdr lists)))
    nil))

(defun putnam-2005-b6-insert-everywhere (item list)
  (if (consp list)
      (cons
       (cons item list)
       (putnam-2005-b6-prefix-each
        (car list)
        (putnam-2005-b6-insert-everywhere
         item (cdr list))))
    (list (list item))))

(defun putnam-2005-b6-insert-into-each (item lists)
  (if (consp lists)
      (append
       (putnam-2005-b6-insert-everywhere
        item (car lists))
       (putnam-2005-b6-insert-into-each
        item (cdr lists)))
    nil))

(defun putnam-2005-b6-permutations (list)
  (if (consp list)
      (putnam-2005-b6-insert-into-each
       (car list)
       (putnam-2005-b6-permutations (cdr list)))
    (list nil)))

;; Inversion parity is the usual sign of the represented permutation.
(defun putnam-2005-b6-count-greater (item list)
  (if (consp list)
      (+ (if (> item (car list)) 1 0)
         (putnam-2005-b6-count-greater item (cdr list)))
    0))

(defun putnam-2005-b6-inversion-count (permutation)
  (if (consp permutation)
      (+ (putnam-2005-b6-count-greater
          (car permutation)
          (cdr permutation))
         (putnam-2005-b6-inversion-count
          (cdr permutation)))
    0))

(defun putnam-2005-b6-sign (permutation)
  (if (evenp
       (putnam-2005-b6-inversion-count permutation))
      1
    -1))

(defun putnam-2005-b6-fixed-point-count
    (permutation expected)
  (if (consp permutation)
      (+ (if (equal (car permutation) expected) 1 0)
         (putnam-2005-b6-fixed-point-count
          (cdr permutation)
          (+ expected 1)))
    0))

(defun putnam-2005-b6-signed-fixed-point-sum
    (permutations)
  (if (consp permutations)
      (let ((permutation (car permutations)))
        (+
         (/ (putnam-2005-b6-sign permutation)
            (+ (putnam-2005-b6-fixed-point-count
                permutation 1)
               1))
         (putnam-2005-b6-signed-fixed-point-sum
          (cdr permutations))))
    0))

(defun putnam-2005-b6-left-side (n)
  (putnam-2005-b6-signed-fixed-point-sum
   (putnam-2005-b6-permutations
    (putnam-2005-b6-range-from 1 n))))

(defun putnam-2005-b6-right-side (n)
  (* (if (evenp (+ n 1)) 1 -1)
     (/ n (+ n 1))))

(defun putnambench-putnam-2005-b6-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (putnam-2005-b6-left-side n)
    (putnam-2005-b6-right-side n))))

(value-triple :itpeval-statement-checked)
:q
