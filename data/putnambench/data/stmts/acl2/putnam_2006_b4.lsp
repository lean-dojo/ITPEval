;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_b4:
;; the maximum number of Boolean vertices in a k-dimensional real linear
;; subspace of R^n is 2^k. This file contains no proof.

(in-package "ACL2")

;; For a finite set S of Boolean vectors, containment in some k-dimensional
;; real subspace is equivalent (when k <= n) to real row rank at most k.
;; Because the entries are rational, rational row rank equals real row rank:
;; a nonzero rational minor witnesses either rank, while Gaussian elimination
;; over Q supplies all dependencies when the rank is smaller. Thus the
;; universal upper bound below is bidirectionally equivalent to the upper
;; bound over all real subspaces, without replacing R by Q.
;;
;; The elimination routine below is a definition of rational row rank: each
;; pivot step removes one nonzero row after invertible rational row
;; operations, and skipped columns do not change the row span. The attaining
;; point set remains existential rather than being replaced by the canonical
;; coordinate-cube witness.

(defun putnam-2006-b4-bit-p (value)
  (or (equal value 0)
      (equal value 1)))

(defun putnam-2006-b4-boolean-vector-p (vector width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      (equal vector nil)
    (and (consp vector)
         (putnam-2006-b4-bit-p (car vector))
         (putnam-2006-b4-boolean-vector-p
          (cdr vector)
          (- width 1)))))

(defun putnam-2006-b4-boolean-vectors-p (vectors width)
  (if (consp vectors)
      (and (putnam-2006-b4-boolean-vector-p
            (car vectors)
            width)
           (putnam-2006-b4-boolean-vectors-p
            (cdr vectors)
            width))
    (equal vectors nil)))

(defun putnam-2006-b4-first-pivot-row (rows column)
  (if (consp rows)
      (if (equal (nth column (car rows)) 0)
          (putnam-2006-b4-first-pivot-row
           (cdr rows)
           column)
        (car rows))
    nil))

(defun putnam-2006-b4-remove-first-row (row rows)
  (if (consp rows)
      (if (equal row (car rows))
          (cdr rows)
        (cons (car rows)
              (putnam-2006-b4-remove-first-row
               row
               (cdr rows))))
    nil))

(defun putnam-2006-b4-eliminate-vector
    (row pivot factor)
  (if (and (consp row)
           (consp pivot))
      (cons (- (car row)
               (* factor (car pivot)))
            (putnam-2006-b4-eliminate-vector
             (cdr row)
             (cdr pivot)
             factor))
    nil))

(defun putnam-2006-b4-eliminate-rows
    (rows pivot column pivot-entry)
  (if (consp rows)
      (cons
       (putnam-2006-b4-eliminate-vector
        (car rows)
        pivot
        (/ (nth column (car rows))
           pivot-entry))
       (putnam-2006-b4-eliminate-rows
        (cdr rows)
        pivot
        column
        pivot-entry))
    nil))

(defun putnam-2006-b4-row-rank-aux
    (rows column columns-left)
  (declare (xargs :measure (nfix columns-left)))
  (if (or (zp columns-left)
          (endp rows))
      0
    (let ((pivot
           (putnam-2006-b4-first-pivot-row
            rows
            column)))
      (if (not pivot)
          (putnam-2006-b4-row-rank-aux
           rows
           (+ column 1)
           (- columns-left 1))
        (+ 1
           (putnam-2006-b4-row-rank-aux
            (putnam-2006-b4-eliminate-rows
             (putnam-2006-b4-remove-first-row
              pivot
              rows)
             pivot
             column
             (nth column pivot))
            (+ column 1)
            (- columns-left 1)))))))

(defun putnam-2006-b4-row-rank (rows width)
  (putnam-2006-b4-row-rank-aux rows 0 width))

(defun putnam-2006-b4-upper-bound-p
    (n k points)
  (implies
   (and
    (true-listp points)
    (no-duplicatesp-equal points)
    (putnam-2006-b4-boolean-vectors-p points n)
    (<= (putnam-2006-b4-row-rank points n) k))
   (<= (len points)
       (expt 2 k))))

(defun-sk putnam-2006-b4-upper-bound-all-p (n k)
  (forall
   (points)
   (putnam-2006-b4-upper-bound-p n k points)))

(defun-sk putnam-2006-b4-attained-p (n k)
  (exists
   (points)
    (and
     (true-listp points)
     (no-duplicatesp-equal points)
     (putnam-2006-b4-boolean-vectors-p points n)
     (equal (len points)
            (expt 2 k))
     (equal (putnam-2006-b4-row-rank points n)
            k))))

(defun putnambench-putnam-2006-b4-statement
    (n k)
  (implies
   (and
    (natp n)
    (< 0 n)
    (natp k)
   (<= k n))
   (and
    (putnam-2006-b4-upper-bound-all-p n k)
    (putnam-2006-b4-attained-p n k))))

(value-triple :itpeval-statement-checked)
:q
