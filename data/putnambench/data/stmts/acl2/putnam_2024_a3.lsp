;; Statement-only formalization of PutnamBench corpus artifact putnam_2024_a3:
;; among the row- and column-strict bijective fillings of a 3 by 2024 grid
;; by 1 through 6072, two positions have comparison frequency in [1/3,2/3].
;; This file contains no proof.

(in-package "ACL2")

;; Reading a filling in row-major order identifies it with one permutation of
;; 1,...,6072. Conversely, zero-extending such a list outside the grid gives
;; exactly one total source function. Thus filtering all permutations by the
;; adjacent row and column inequalities gives a set in bijection with S.
;; Adjacent strict inequalities are equivalent to StrictMonoOn on each finite
;; interval, and the permutation generator has no duplicate outputs.

(defun putnam-2024-a3-values (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons count
          (putnam-2024-a3-values (- count 1)))))

(defun putnam-2024-a3-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2024-a3-prefix-each item (cdr lists)))))

(defun putnam-2024-a3-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-2024-a3-prefix-each
           (car list)
           (putnam-2024-a3-insert-everywhere
            item (cdr list))))))

(defun putnam-2024-a3-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2024-a3-insert-everywhere item (car lists))
     (putnam-2024-a3-insert-into-each
      item (cdr lists)))))

(defun putnam-2024-a3-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2024-a3-insert-into-each
     (car list)
     (putnam-2024-a3-permutations (cdr list)))))

(defun putnam-2024-a3-row-increasing-p
    (table offset remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining)
          (equal remaining 1))
      t
    (and
     (< (nth offset table)
        (nth (+ offset 1) table))
     (putnam-2024-a3-row-increasing-p
      table (+ offset 1) (- remaining 1)))))

(defun putnam-2024-a3-rows-increasing-p
    (table row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (putnam-2024-a3-row-increasing-p
      table (* row 2024) 2024)
     (putnam-2024-a3-rows-increasing-p
      table (+ row 1) (- remaining 1)))))

(defun putnam-2024-a3-column-increasing-p
    (table column row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining)
          (equal remaining 1))
      t
    (let ((offset (+ (* row 2024) column)))
      (and
       (< (nth offset table)
          (nth (+ offset 2024) table))
       (putnam-2024-a3-column-increasing-p
        table column (+ row 1) (- remaining 1))))))

(defun putnam-2024-a3-columns-increasing-p
    (table column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (putnam-2024-a3-column-increasing-p
      table column 0 3)
     (putnam-2024-a3-columns-increasing-p
      table (+ column 1) (- remaining 1)))))

(defun putnam-2024-a3-table-p (table)
  (and
   (putnam-2024-a3-rows-increasing-p table 0 3)
   (putnam-2024-a3-columns-increasing-p table 0 2024)))

(defun putnam-2024-a3-filter-tables (permutations)
  (if (endp permutations)
      nil
    (if (putnam-2024-a3-table-p (car permutations))
        (cons (car permutations)
              (putnam-2024-a3-filter-tables
               (cdr permutations)))
      (putnam-2024-a3-filter-tables
       (cdr permutations)))))

(defun putnam-2024-a3-entry (table row column)
  (nth (+ (* (- row 1) 2024)
          (- column 1))
       table))

(defun putnam-2024-a3-qualifying-count
    (tables a b c d)
  (if (endp tables)
      0
    (+ (if (< (putnam-2024-a3-entry
               (car tables) a b)
              (putnam-2024-a3-entry
               (car tables) c d))
           1
         0)
       (putnam-2024-a3-qualifying-count
        (cdr tables) a b c d))))

(defun putnam-2024-a3-balanced-p
    (tables total a b c d)
  (let ((fraction
         (/ (putnam-2024-a3-qualifying-count
             tables a b c d)
            total)))
    (and
     (<= (/ 1 3) fraction)
     (<= fraction (/ 2 3)))))

;; The following four finite searches are the source's internal existential
;; quantifiers over a,c in 1..3 and b,d in 1..2024.

(defun putnam-2024-a3-d-exists-p
    (tables total a b c d remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or
     (putnam-2024-a3-balanced-p
      tables total a b c d)
     (putnam-2024-a3-d-exists-p
      tables total a b c (+ d 1) (- remaining 1)))))

(defun putnam-2024-a3-c-exists-p
    (tables total a b c remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or
     (putnam-2024-a3-d-exists-p
      tables total a b c 1 2024)
     (putnam-2024-a3-c-exists-p
      tables total a b (+ c 1) (- remaining 1)))))

(defun putnam-2024-a3-b-exists-p
    (tables total a b remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or
     (putnam-2024-a3-c-exists-p
      tables total a b 1 3)
     (putnam-2024-a3-b-exists-p
      tables total a (+ b 1) (- remaining 1)))))

(defun putnam-2024-a3-a-exists-p
    (tables total a remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (or
     (putnam-2024-a3-b-exists-p
      tables total a 1 2024)
     (putnam-2024-a3-a-exists-p
      tables total (+ a 1) (- remaining 1)))))

;; The source answer is True, so its concluding IFF is definitionally the
;; proposition below after replacing S by the equal set specified by hS.
(defun putnambench-putnam-2024-a3-statement ()
  (let* ((tables
          (putnam-2024-a3-filter-tables
           (putnam-2024-a3-permutations
            (putnam-2024-a3-values 6072))))
         (total (len tables)))
    (putnam-2024-a3-a-exists-p tables total 1 3)))

(value-triple :itpeval-statement-checked)
:q
