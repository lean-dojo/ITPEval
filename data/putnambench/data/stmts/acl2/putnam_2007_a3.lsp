;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_a3:
;; for every positive integer k, the proportion of permutations of the
;; integers 1 through 3k+1 having no prefix sum divisible by 3 is
;; k!(k+1)!/((3k+1)(2k)!). This file contains no proof.

(in-package "ACL2")

;; A permutation of the finite integer interval is represented by its image
;; list. Since the interval has no duplicates, insertion at every position
;; enumerates every permutation exactly once.
(defun putnam-2007-a3-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2007-a3-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2007-a3-prefix-each (value lists)
  (if (consp lists)
      (cons (cons value (car lists))
            (putnam-2007-a3-prefix-each value (cdr lists)))
    nil))

(defun putnam-2007-a3-insert-everywhere (value values)
  (if (consp values)
      (cons
       (cons value values)
       (putnam-2007-a3-prefix-each
        (car values)
        (putnam-2007-a3-insert-everywhere
         value (cdr values))))
    (list (list value))))

(defun putnam-2007-a3-insert-into-each (value permutations)
  (if (consp permutations)
      (append
       (putnam-2007-a3-insert-everywhere
        value (car permutations))
       (putnam-2007-a3-insert-into-each
        value (cdr permutations)))
    nil))

(defun putnam-2007-a3-permutations (values)
  (if (consp values)
      (putnam-2007-a3-insert-into-each
       (car values)
       (putnam-2007-a3-permutations (cdr values)))
    (list nil)))

(defun putnam-2007-a3-good-prefixes-from-p
    (values partial-sum)
  (if (consp values)
      (let ((next-sum (+ partial-sum (car values))))
        (and
         (not (equal (mod next-sum 3) 0))
         (putnam-2007-a3-good-prefixes-from-p
          (cdr values) next-sum)))
    t))

(defun putnam-2007-a3-good-permutation-p (values)
  (putnam-2007-a3-good-prefixes-from-p values 0))

(defun putnam-2007-a3-count-good (permutations)
  (if (consp permutations)
      (+ (if (putnam-2007-a3-good-permutation-p
              (car permutations))
             1
           0)
         (putnam-2007-a3-count-good (cdr permutations)))
    0))

(defun putnam-2007-a3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (nfix n)
       (putnam-2007-a3-factorial (- (nfix n) 1)))))

;; Cross multiplication states
;;
;;   good-count / all-count = k!(k+1)! / ((3k+1)(2k)!)
;;
;; using only exact integers. The generated finite lists are bijective with
;; the Fin-indexed permutation functions in the source.
(defun putnambench-putnam-2007-a3-statement (k)
  (implies
   (posp k)
   (let* ((entry-count (+ (* 3 k) 1))
          (entries
           (putnam-2007-a3-range-from 1 entry-count))
          (permutations
           (putnam-2007-a3-permutations entries))
          (good-count
           (putnam-2007-a3-count-good permutations))
          (all-count (len permutations)))
     (equal
      (* good-count
         entry-count
         (putnam-2007-a3-factorial (* 2 k)))
      (* all-count
         (putnam-2007-a3-factorial k)
         (putnam-2007-a3-factorial (+ k 1)))))))

(value-triple :itpeval-statement-checked)
:q
