;; Statement-only formalization of thousand-theorems artifact Q7660749,
;; "Sylvester's determinant theorem": over every commutative unital ring and
;; for all finite rectangular matrices A and B of mutually transposed shapes,
;; det(I + AB) equals det(I + BA). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ring tags select arbitrary carriers and operations.  All typing and all
;; commutative-ring laws used by the matrix expressions are explicit.

(defstub q7660749-ring-element-p (ring value) t)
(defstub q7660749-ring-zero (ring) t)
(defstub q7660749-ring-one (ring) t)
(defstub q7660749-ring-negate (ring value) t)
(defstub q7660749-ring-add (ring left right) t)
(defstub q7660749-ring-multiply (ring left right) t)

(defun-sk q7660749-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (q7660749-ring-element-p ring x)
      (and
       (q7660749-ring-element-p
        ring (q7660749-ring-negate ring x))
       (equal
        (q7660749-ring-add
         ring x (q7660749-ring-zero ring))
        x)
       (equal
        (q7660749-ring-add
         ring x (q7660749-ring-negate ring x))
        (q7660749-ring-zero ring))
       (equal
        (q7660749-ring-multiply
         ring x (q7660749-ring-one ring))
        x)))
     (implies
      (and
       (q7660749-ring-element-p ring x)
       (q7660749-ring-element-p ring y))
      (and
       (q7660749-ring-element-p
        ring (q7660749-ring-add ring x y))
       (q7660749-ring-element-p
        ring (q7660749-ring-multiply ring x y))
       (equal
        (q7660749-ring-add ring x y)
        (q7660749-ring-add ring y x))
       (equal
        (q7660749-ring-multiply ring x y)
        (q7660749-ring-multiply ring y x))))
     (implies
      (and
       (q7660749-ring-element-p ring x)
       (q7660749-ring-element-p ring y)
       (q7660749-ring-element-p ring z))
      (and
       (equal
        (q7660749-ring-add
         ring (q7660749-ring-add ring x y) z)
        (q7660749-ring-add
         ring x (q7660749-ring-add ring y z)))
       (equal
        (q7660749-ring-multiply
         ring (q7660749-ring-multiply ring x y) z)
        (q7660749-ring-multiply
         ring x (q7660749-ring-multiply ring y z)))
       (equal
        (q7660749-ring-multiply
         ring x (q7660749-ring-add ring y z))
        (q7660749-ring-add
         ring
         (q7660749-ring-multiply ring x y)
         (q7660749-ring-multiply ring x z))))))))

(defun q7660749-commutative-ring-p (ring)
  (and
   (q7660749-ring-element-p
    ring (q7660749-ring-zero ring))
   (q7660749-ring-element-p
    ring (q7660749-ring-one ring))
   (q7660749-ring-laws-p ring)))

;; A matrix over finite index types is represented, after choosing
;; enumerations of those types, by a proper list of proper rows.  The exact
;; row and column lengths and carrier membership make this representation
;; bijective with the source's finite matrix functions.

(defun q7660749-matrix-row-p (ring row column-count)
  (if (zp column-count)
      (equal row nil)
    (and
     (consp row)
     (q7660749-ring-element-p ring (car row))
     (q7660749-matrix-row-p
      ring (cdr row) (- column-count 1)))))

(defun q7660749-matrix-p
    (ring matrix row-count column-count)
  (if (zp row-count)
      (equal matrix nil)
    (and
     (consp matrix)
     (q7660749-matrix-row-p
      ring (car matrix) column-count)
     (q7660749-matrix-p
      ring (cdr matrix) (- row-count 1) column-count))))

(defun q7660749-matrix-entry (matrix row column)
  (nth column (nth row matrix)))

;; Matrix multiplication is the usual finite sum in the selected ring.

(defun q7660749-dot-product-from
    (ring left right row column index remaining)
  (if (zp remaining)
      (q7660749-ring-zero ring)
    (q7660749-ring-add
     ring
     (q7660749-ring-multiply
      ring
      (q7660749-matrix-entry left row index)
      (q7660749-matrix-entry right index column))
     (q7660749-dot-product-from
      ring left right row column
      (+ index 1) (- remaining 1)))))

(defun q7660749-product-entry
    (ring left right row column inner-count)
  (q7660749-dot-product-from
   ring left right row column 0 inner-count))

;; Build I + LR at the square dimension determined by the row count of L.

(defun q7660749-one-add-product-row
    (ring left right inner-count row column remaining)
  (if (zp remaining)
      nil
    (let ((entry
           (q7660749-product-entry
            ring left right row column inner-count)))
      (cons
       (if (equal row column)
           (q7660749-ring-add
            ring (q7660749-ring-one ring) entry)
         entry)
       (q7660749-one-add-product-row
        ring left right inner-count row
        (+ column 1) (- remaining 1))))))

(defun q7660749-one-add-product-rows
    (ring left right dimension inner-count row remaining)
  (if (zp remaining)
      nil
    (cons
     (q7660749-one-add-product-row
      ring left right inner-count row 0 dimension)
     (q7660749-one-add-product-rows
      ring left right dimension inner-count
      (+ row 1) (- remaining 1)))))

(defun q7660749-one-add-product
    (ring left right dimension inner-count)
  (q7660749-one-add-product-rows
   ring left right dimension inner-count 0 dimension))

;; The determinant is the signed Leibniz sum over all permutations.

(defun q7660749-range-from (start count)
  (if (zp count)
      nil
    (cons start
          (q7660749-range-from
           (+ start 1) (- count 1)))))

(defun q7660749-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons
     (cons item (car lists))
     (q7660749-prefix-each item (cdr lists)))))

(defun q7660749-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons
     (cons item list)
     (q7660749-prefix-each
      (car list)
      (q7660749-insert-everywhere item (cdr list))))))

(defun q7660749-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (q7660749-insert-everywhere item (car lists))
     (q7660749-insert-into-each item (cdr lists)))))

(defun q7660749-permutations (list)
  (if (endp list)
      (list nil)
    (q7660749-insert-into-each
     (car list)
     (q7660749-permutations (cdr list)))))

(defun q7660749-count-greater (item list)
  (if (endp list)
      0
    (+ (if (> item (car list)) 1 0)
       (q7660749-count-greater item (cdr list)))))

(defun q7660749-inversion-count (permutation)
  (if (endp permutation)
      0
    (+ (q7660749-count-greater
        (car permutation) (cdr permutation))
       (q7660749-inversion-count (cdr permutation)))))

(defun q7660749-diagonal-product
    (ring matrix permutation row)
  (if (endp permutation)
      (q7660749-ring-one ring)
    (q7660749-ring-multiply
     ring
     (q7660749-matrix-entry
      matrix row (car permutation))
     (q7660749-diagonal-product
      ring matrix (cdr permutation) (+ row 1)))))

(defun q7660749-determinant-sum
    (ring matrix permutations)
  (if (endp permutations)
      (q7660749-ring-zero ring)
    (let* ((permutation (car permutations))
           (product
            (q7660749-diagonal-product
             ring matrix permutation 0))
           (signed-product
            (if (equal
                 (mod
                  (q7660749-inversion-count permutation)
                  2)
                 0)
                product
              (q7660749-ring-negate ring product))))
      (q7660749-ring-add
       ring
       signed-product
       (q7660749-determinant-sum
        ring matrix (cdr permutations))))))

(defun q7660749-determinant (ring matrix dimension)
  (q7660749-determinant-sum
   ring
   matrix
   (q7660749-permutations
    (q7660749-range-from 0 dimension))))

;; This universally quantified predicate is the source proposition.  Replacing
;; finite index types by their cardinalities and enumerated tables preserves
;; both matrix spaces and the determinant identity in both directions.

(defun-sk q7660749-sylvester-determinant-statement ()
  (forall (ring m n a b)
    (implies
     (and
      (natp m)
      (natp n)
      (q7660749-commutative-ring-p ring)
      (q7660749-matrix-p ring a m n)
      (q7660749-matrix-p ring b n m))
     (equal
      (q7660749-determinant
       ring
       (q7660749-one-add-product
        ring a b m n)
       m)
      (q7660749-determinant
       ring
       (q7660749-one-add-product
        ring b a n m)
       n)))))

(value-triple :itpeval-statement-checked)
:q
