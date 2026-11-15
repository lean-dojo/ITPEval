;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_a4:
;; an n by n matrix with entries 1 or -1 and mutually orthogonal rows cannot
;; contain an all-ones a by b submatrix unless a*b is at most n.
;; This file contains no proof.

(in-package "ACL2")

;; Finite matrices are represented extensionally by row lists in canonical
;; index order. Since every H entry is 1 or -1 and every S entry is 1, ACL2's
;; integer operations agree exactly with the corresponding real operations.

(defun putnam-2005-a4-signed-one-row-p (row width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      (equal row nil)
    (and
     (consp row)
     (or (equal (car row) 1)
         (equal (car row) -1))
     (putnam-2005-a4-signed-one-row-p
      (cdr row) (- width 1)))))

(defun putnam-2005-a4-signed-one-matrix-p
    (matrix height width)
  (declare (xargs :measure (nfix height)))
  (if (zp height)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-2005-a4-signed-one-row-p
      (car matrix) width)
     (putnam-2005-a4-signed-one-matrix-p
      (cdr matrix) (- height 1) width))))

(defun putnam-2005-a4-one-row-p (row width)
  (declare (xargs :measure (nfix width)))
  (if (zp width)
      (equal row nil)
    (and
     (consp row)
     (equal (car row) 1)
     (putnam-2005-a4-one-row-p
      (cdr row) (- width 1)))))

(defun putnam-2005-a4-one-matrix-p (matrix height width)
  (declare (xargs :measure (nfix height)))
  (if (zp height)
      (equal matrix nil)
    (and
     (consp matrix)
     (putnam-2005-a4-one-row-p (car matrix) width)
     (putnam-2005-a4-one-matrix-p
      (cdr matrix) (- height 1) width))))

(defun putnam-2005-a4-dot-product (left right)
  (if (or (endp left) (endp right))
      0
    (+ (* (car left) (car right))
       (putnam-2005-a4-dot-product
        (cdr left) (cdr right)))))

(defun putnam-2005-a4-orthogonal-to-rows-p (row rows)
  (if (endp rows)
      t
    (and
     (equal
      (putnam-2005-a4-dot-product row (car rows))
      0)
     (putnam-2005-a4-orthogonal-to-rows-p
      row (cdr rows)))))

(defun putnam-2005-a4-pairwise-orthogonal-rows-p (rows)
  (if (endp rows)
      t
    (and
     (putnam-2005-a4-orthogonal-to-rows-p
      (car rows) (cdr rows))
     (putnam-2005-a4-pairwise-orthogonal-rows-p
      (cdr rows)))))

;; These constructors enumerate every function between the canonical finite
;; carriers. Filtering image lists for duplicates is exactly injectivity, so
;; the searches below implement the two source existential quantifiers without
;; exposing either witness as a statement parameter.

(defun putnam-2005-a4-indices (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-2005-a4-indices (- count 1)))))

(defun putnam-2005-a4-prepend-to-each (value image-lists)
  (if (endp image-lists)
      nil
    (cons
     (cons value (car image-lists))
     (putnam-2005-a4-prepend-to-each
      value (cdr image-lists)))))

(defun putnam-2005-a4-extend-by-each-image
    (codomain image-lists)
  (if (endp codomain)
      nil
    (append
     (putnam-2005-a4-prepend-to-each
      (car codomain) image-lists)
     (putnam-2005-a4-extend-by-each-image
      (cdr codomain) image-lists))))

(defun putnam-2005-a4-function-images (domain codomain)
  (if (endp domain)
      (list nil)
    (putnam-2005-a4-extend-by-each-image
     codomain
     (putnam-2005-a4-function-images
      (cdr domain) codomain))))

(defun putnam-2005-a4-mapped-row-matches-p
    (h-row s-row column-map)
  (if (endp column-map)
      (endp s-row)
    (and
     (consp s-row)
     (equal (car s-row)
            (nth (car column-map) h-row))
     (putnam-2005-a4-mapped-row-matches-p
      h-row (cdr s-row) (cdr column-map)))))

(defun putnam-2005-a4-mapped-submatrix-p
    (h s row-map column-map)
  (if (endp row-map)
      (endp s)
    (and
     (consp s)
     (putnam-2005-a4-mapped-row-matches-p
      (nth (car row-map) h)
      (car s)
      column-map)
     (putnam-2005-a4-mapped-submatrix-p
      h (cdr s) (cdr row-map) column-map))))

(defun putnam-2005-a4-column-map-exists-p
    (h s row-map column-maps)
  (if (endp column-maps)
      nil
    (or
     (and
      (no-duplicatesp-equal (car column-maps))
      (putnam-2005-a4-mapped-submatrix-p
       h s row-map (car column-maps)))
     (putnam-2005-a4-column-map-exists-p
      h s row-map (cdr column-maps)))))

(defun putnam-2005-a4-row-map-exists-p
    (h s row-maps column-maps)
  (if (endp row-maps)
      nil
    (or
     (and
      (no-duplicatesp-equal (car row-maps))
      (putnam-2005-a4-column-map-exists-p
       h s (car row-maps) column-maps))
     (putnam-2005-a4-row-map-exists-p
      h s (cdr row-maps) column-maps))))

(defun putnam-2005-a4-submatrix-exists-p (h s n a b)
  (let* ((index-carrier (putnam-2005-a4-indices n))
         (row-domain (putnam-2005-a4-indices a))
         (column-domain (putnam-2005-a4-indices b))
         (row-maps
          (putnam-2005-a4-function-images
           row-domain index-carrier))
         (column-maps
          (putnam-2005-a4-function-images
           column-domain index-carrier)))
    (putnam-2005-a4-row-map-exists-p
     h s row-maps column-maps)))

(defun putnambench-putnam-2005-a4-statement (n h a b s)
  (implies
   (and
    (natp n)
    (natp a)
    (natp b)
    (<= 1 n)
    (<= 1 a)
    (<= a n)
    (<= 1 b)
    (<= b n)
    (putnam-2005-a4-signed-one-matrix-p h n n)
    (putnam-2005-a4-pairwise-orthogonal-rows-p h)
    (putnam-2005-a4-one-matrix-p s a b)
    (putnam-2005-a4-submatrix-exists-p h s n a b))
   (<= (* a b) n)))

(value-triple :itpeval-statement-checked)
:q
