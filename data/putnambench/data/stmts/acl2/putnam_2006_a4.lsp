;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_a4:
;; for every integer n greater than one, the average number of endpoint-aware
;; local maxima over all permutations of n elements is (n+1)/3. This file
;; contains no proof.

(in-package "ACL2")

;; A permutation is represented by its image list on 0,...,n-1. The generator
;; below enumerates every such list exactly once. This is bijective with the
;; Fin n permutations in Lean and with the Isabelle permutations that fix all
;; indices at least n.

(defun putnam-2006-a4-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2006-a4-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2006-a4-prepend-to-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-2006-a4-prepend-to-each
      value (cdr lists)))))

(defun putnam-2006-a4-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-2006-a4-prepend-to-each
      (car values)
      (putnam-2006-a4-insert-everywhere
       value (cdr values))))))

(defun putnam-2006-a4-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-2006-a4-insert-everywhere
      value (car permutations))
     (putnam-2006-a4-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-2006-a4-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-2006-a4-insert-into-permutations
     (car values)
     (putnam-2006-a4-permutations (cdr values)))))

;; PREVIOUS is the value immediately before the first element of REMAINING.
;; The final element needs only the left comparison; every earlier element
;; needs both strict comparisons.
(defun putnam-2006-a4-local-maxima-after-first
    (previous remaining)
  (if (endp remaining)
      0
    (if (endp (cdr remaining))
        (if (< previous (car remaining)) 1 0)
      (+ (if (and (< previous (car remaining))
                  (> (car remaining) (cadr remaining)))
             1
           0)
         (putnam-2006-a4-local-maxima-after-first
          (car remaining) (cdr remaining))))))

(defun putnam-2006-a4-local-maxima-count (permutation)
  (if (endp permutation)
      0
    (if (endp (cdr permutation))
        1
      (+ (if (> (car permutation) (cadr permutation))
             1
           0)
         (putnam-2006-a4-local-maxima-after-first
          (car permutation) (cdr permutation))))))

(defun putnam-2006-a4-total-local-maxima (permutations)
  (if (endp permutations)
      0
    (+ (putnam-2006-a4-local-maxima-count
        (car permutations))
       (putnam-2006-a4-total-local-maxima
        (cdr permutations)))))

(defun putnambench-putnam-2006-a4-statement (n)
  (implies
   (and (natp n)
        (< 1 n))
   (let* ((permutations
           (putnam-2006-a4-permutations
            (putnam-2006-a4-range-from 0 n)))
          (total-local-maxima
           (putnam-2006-a4-total-local-maxima
            permutations)))
     (equal
      (/ total-local-maxima (len permutations))
      (/ (+ n 1) 3)))))

(value-triple :itpeval-statement-checked)
:q
