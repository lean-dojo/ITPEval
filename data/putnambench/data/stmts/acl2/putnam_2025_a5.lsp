;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_a5:
;; the sign sequences maximizing the number of compatible permutations are
;; exactly the two alternating sign sequences. This file contains no proof.

(in-package "ACL2")

;; A function Fin n -> Z-units is exactly a length-n list with every entry
;; equal to 1 or -1. Likewise, a permutation of Fin (n+1) is represented by
;; its value list on the increasing domain 0,...,n. The generators below
;; enumerate both finite function spaces completely, so the internal
;; maximality check preserves the source's universal quantifier over t.

(defun putnam-2025-a5-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2025-a5-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2025-a5-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2025-a5-prefix-each
           item (cdr lists)))))

(defun putnam-2025-a5-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (putnam-2025-a5-prefix-each
      (car list)
      (putnam-2025-a5-insert-everywhere
       item (cdr list))))))

(defun putnam-2025-a5-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2025-a5-insert-everywhere
      item (car lists))
     (putnam-2025-a5-insert-into-each
      item (cdr lists)))))

(defun putnam-2025-a5-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2025-a5-insert-into-each
     (car list)
     (putnam-2025-a5-permutations (cdr list)))))

(defun putnam-2025-a5-sign-sequence-p (signs n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (equal signs nil)
    (and
     (consp signs)
     (or (equal (car signs) 1)
         (equal (car signs) -1))
     (putnam-2025-a5-sign-sequence-p
      (cdr signs) (- n 1)))))

(defun putnam-2025-a5-prefix-sign (sign sequences)
  (if (endp sequences)
      nil
    (cons
     (cons sign (car sequences))
     (putnam-2025-a5-prefix-sign
      sign (cdr sequences)))))

(defun putnam-2025-a5-all-sign-sequences (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list nil)
    (let ((tails
           (putnam-2025-a5-all-sign-sequences
            (- n 1))))
      (append
       (putnam-2025-a5-prefix-sign 1 tails)
       (putnam-2025-a5-prefix-sign -1 tails)))))

;; Reading a permutation list from left to right, this is exactly
;; s_i * (a_(i+1) - a_i) > 0 at every index.

(defun putnam-2025-a5-compatible-p (signs permutation)
  (if (endp signs)
      t
    (and
     (consp permutation)
     (consp (cdr permutation))
     (< 0
        (* (car signs)
           (- (car (cdr permutation))
              (car permutation))))
     (putnam-2025-a5-compatible-p
      (cdr signs) (cdr permutation)))))

(defun putnam-2025-a5-count-compatible
    (signs permutations)
  (if (endp permutations)
      0
    (+ (if (putnam-2025-a5-compatible-p
            signs (car permutations))
           1
         0)
       (putnam-2025-a5-count-compatible
        signs (cdr permutations)))))

(defun putnam-2025-a5-all-counts-at-most-p
    (sequences bound permutations)
  (if (endp sequences)
      t
    (and
     (<=
      (putnam-2025-a5-count-compatible
       (car sequences) permutations)
      bound)
     (putnam-2025-a5-all-counts-at-most-p
      (cdr sequences) bound permutations))))

(defun putnam-2025-a5-alternating-from-p
    (signs expected)
  (if (endp signs)
      (equal signs nil)
    (and
     (equal (car signs) expected)
     (putnam-2025-a5-alternating-from-p
      (cdr signs) (- expected)))))

(defun putnam-2025-a5-solution-p (signs)
  (or
   (putnam-2025-a5-alternating-from-p signs 1)
   (putnam-2025-a5-alternating-from-p signs -1)))

(defun putnambench-putnam-2025-a5-statement (n signs)
  (implies
   (and
    (natp n)
    (<= 1 n)
    (putnam-2025-a5-sign-sequence-p signs n))
   (let* ((permutations
           (putnam-2025-a5-permutations
            (putnam-2025-a5-range-from 0 (+ n 1))))
          (sign-sequences
           (putnam-2025-a5-all-sign-sequences n))
          (selected-count
           (putnam-2025-a5-count-compatible
            signs permutations)))
     (iff
      (putnam-2025-a5-all-counts-at-most-p
       sign-sequences selected-count permutations)
      (putnam-2025-a5-solution-p signs)))))

(value-triple :itpeval-statement-checked)
:q
