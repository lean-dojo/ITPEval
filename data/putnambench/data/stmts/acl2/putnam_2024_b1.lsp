;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_b1:
;; the positive integer pairs (n,k) admitting a permutation of the columns
;; whose selected grid entries are exactly 1 through n are precisely
;; (2*l+1,l+1) for natural l. This file contains no proof.

(in-package "ACL2")

;; The hypotheses defining GRID and VALID uniquely determine both objects, so
;; they are eliminated definitionally. A function Fin n -> Fin n is injective
;; exactly when its values, in row order, form a permutation of 0,...,n-1.
;; Enumerating those finite permutations therefore preserves the source's
;; internal existential function witness without exposing it as a parameter.

(defun putnam-2024-b1-indices-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2024-b1-indices-from
           (+ start 1) (- count 1)))))

(defun putnam-2024-b1-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2024-b1-prefix-each item (cdr lists)))))

(defun putnam-2024-b1-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-2024-b1-prefix-each
           (car list)
           (putnam-2024-b1-insert-everywhere
            item (cdr list))))))

(defun putnam-2024-b1-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2024-b1-insert-everywhere item (car lists))
     (putnam-2024-b1-insert-into-each item (cdr lists)))))

(defun putnam-2024-b1-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2024-b1-insert-into-each
     (car list)
     (putnam-2024-b1-permutations (cdr list)))))

(defun putnam-2024-b1-selected-values (permutation row k)
  (if (endp permutation)
      nil
    (cons
     (- (+ (+ row 1) (+ (car permutation) 1)) k)
     (putnam-2024-b1-selected-values
      (cdr permutation) (+ row 1) k))))

(defun putnam-2024-b1-every-member-p (left right)
  (if (endp left)
      (equal left nil)
    (and
     (member-equal (car left) right)
     (putnam-2024-b1-every-member-p (cdr left) right))))

(defun putnam-2024-b1-set-equal-p (left right)
  (and
   (true-listp left)
   (true-listp right)
   (putnam-2024-b1-every-member-p left right)
   (putnam-2024-b1-every-member-p right left)))

(defun putnam-2024-b1-permutation-valid-p
    (permutation n k)
  (putnam-2024-b1-set-equal-p
   (putnam-2024-b1-selected-values permutation 0 k)
   (putnam-2024-b1-indices-from 1 n)))

(defun putnam-2024-b1-valid-permutation-exists-p
    (permutations n k)
  (if (endp permutations)
      nil
    (or
     (putnam-2024-b1-permutation-valid-p
      (car permutations) n k)
     (putnam-2024-b1-valid-permutation-exists-p
      (cdr permutations) n k))))

(defun putnam-2024-b1-valid-p (n k)
  (and
   (natp n)
   (natp k)
   (< 0 n)
   (< 0 k)
   (putnam-2024-b1-valid-permutation-exists-p
    (putnam-2024-b1-permutations
     (putnam-2024-b1-indices-from 0 n))
    n
    k)))

;; Writing l = k-1 shows that this predicate is exactly membership in
;; {(2*l+1,l+1) | l is a natural number}.
(defun putnam-2024-b1-solution-p (n k)
  (and
   (natp n)
   (natp k)
   (< 0 k)
   (equal n (- (* 2 k) 1))))

;; ACL2 universally closes N and K. This pointwise IFF is the source set
;; equality over natural-number pairs.
(defun putnambench-putnam-2024-b1-statement (n k)
  (implies
   (and (natp n)
        (natp k))
   (iff
    (putnam-2024-b1-valid-p n k)
    (putnam-2024-b1-solution-p n k))))

(value-triple :itpeval-statement-checked)
:q
