;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_b6:
;; for positive integers n and k, the number of permutations of 0 through
;; n-1 moving every entry by at most k is odd exactly when n is congruent to
;; 0 or 1 modulo 2k+1. This file contains no proof.

(in-package "ACL2")

;; The canonical duplicate-free carrier is 0,...,N-1. A permutation is its
;; image list in carrier order. Insertion at every position enumerates each
;; permutation of this carrier exactly once.
(defun putnam-2008-b6-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2008-b6-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2008-b6-prefix-each (value lists)
  (if (consp lists)
      (cons (cons value (car lists))
            (putnam-2008-b6-prefix-each value (cdr lists)))
    nil))

(defun putnam-2008-b6-insert-everywhere (value values)
  (if (consp values)
      (cons
       (cons value values)
       (putnam-2008-b6-prefix-each
        (car values)
        (putnam-2008-b6-insert-everywhere
         value (cdr values))))
    (list (list value))))

(defun putnam-2008-b6-insert-into-each
    (value permutations)
  (if (consp permutations)
      (append
       (putnam-2008-b6-insert-everywhere
        value (car permutations))
       (putnam-2008-b6-insert-into-each
        value (cdr permutations)))
    nil))

(defun putnam-2008-b6-permutations (values)
  (if (consp values)
      (putnam-2008-b6-insert-into-each
       (car values)
       (putnam-2008-b6-permutations (cdr values)))
    (list nil)))

;; Pairing the domain carrier and image list positionwise is the corresponding
;; Fin N permutation. Integer absolute value preserves the symmetric source
;; condition |sigma(i)-i| <= k.
(defun putnam-2008-b6-k-limited-p (domain image k)
  (if (consp domain)
      (and
       (consp image)
       (<= (abs (- (car image) (car domain))) k)
       (putnam-2008-b6-k-limited-p
        (cdr domain) (cdr image) k))
    (equal image nil)))

(defun putnam-2008-b6-count-k-limited
    (domain permutations k)
  (if (consp permutations)
      (+ (if (putnam-2008-b6-k-limited-p
              domain (car permutations) k)
             1
           0)
         (putnam-2008-b6-count-k-limited
          domain (cdr permutations) k))
    0))

(defun putnambench-putnam-2008-b6-statement (n k)
  (implies
   (and (posp n)
        (posp k))
   (let* ((carrier
           (putnam-2008-b6-range-from 0 n))
          (permutations
           (putnam-2008-b6-permutations carrier))
          (limited-count
           (putnam-2008-b6-count-k-limited
            carrier permutations k))
          (modulus (+ (* 2 k) 1))
          (residue (mod n modulus)))
     (iff
      (equal (mod limited-count 2) 1)
      (or (equal residue 0)
          (equal residue 1))))))

(value-triple :itpeval-statement-checked)
:q
