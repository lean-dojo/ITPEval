;; Statement-only formalization of thousand-theorems artifact Q1551745,
;; "Binomial inverse theorem": over an arbitrary unital ring and finite
;; matrices, the inverse of A + U*C*V has the binomial inverse formula when
;; A, C + C*V*A^{-1}*U*C, and A + U*C*V are invertible. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A ring tag selects an arbitrary carrier and its operations. Lean's Ring
;; permits noncommutative multiplication and the trivial ring, so neither
;; commutativity nor zero /= one is assumed.

(defstub q1551745-ring-element-p (ring value) t)
(defstub q1551745-ring-zero (ring) t)
(defstub q1551745-ring-one (ring) t)
(defstub q1551745-ring-negate (ring value) t)
(defstub q1551745-ring-add (ring left right) t)
(defstub q1551745-ring-multiply (ring left right) t)

(defun-sk q1551745-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (q1551745-ring-element-p ring x)
      (let ((zero (q1551745-ring-zero ring))
            (one (q1551745-ring-one ring))
            (negative (q1551745-ring-negate ring x)))
        (and
         (q1551745-ring-element-p ring negative)
         (equal (q1551745-ring-add ring x zero) x)
         (equal (q1551745-ring-add ring zero x) x)
         (equal (q1551745-ring-add ring x negative) zero)
         (equal (q1551745-ring-add ring negative x) zero)
         (equal (q1551745-ring-multiply ring x one) x)
         (equal (q1551745-ring-multiply ring one x) x)
         (equal (q1551745-ring-multiply ring x zero) zero)
         (equal (q1551745-ring-multiply ring zero x) zero))))
     (implies
      (and
       (q1551745-ring-element-p ring x)
       (q1551745-ring-element-p ring y))
      (and
       (q1551745-ring-element-p
        ring (q1551745-ring-add ring x y))
       (q1551745-ring-element-p
        ring (q1551745-ring-multiply ring x y))
       (equal
        (q1551745-ring-add ring x y)
        (q1551745-ring-add ring y x))))
     (implies
      (and
       (q1551745-ring-element-p ring x)
       (q1551745-ring-element-p ring y)
       (q1551745-ring-element-p ring z))
      (and
       (equal
        (q1551745-ring-add
         ring (q1551745-ring-add ring x y) z)
        (q1551745-ring-add
         ring x (q1551745-ring-add ring y z)))
       (equal
        (q1551745-ring-multiply
         ring (q1551745-ring-multiply ring x y) z)
        (q1551745-ring-multiply
         ring x (q1551745-ring-multiply ring y z)))
       (equal
        (q1551745-ring-multiply
         ring x (q1551745-ring-add ring y z))
        (q1551745-ring-add
         ring
         (q1551745-ring-multiply ring x y)
         (q1551745-ring-multiply ring x z)))
       (equal
        (q1551745-ring-multiply
         ring (q1551745-ring-add ring x y) z)
        (q1551745-ring-add
         ring
         (q1551745-ring-multiply ring x z)
         (q1551745-ring-multiply ring y z))))))))

(defun q1551745-ring-p (ring)
  (and
   (q1551745-ring-element-p
    ring (q1551745-ring-zero ring))
   (q1551745-ring-element-p
    ring (q1551745-ring-one ring))
   (q1551745-ring-laws-p ring)))

;; Choosing enumerations of the two finite Lean index types identifies their
;; matrix function spaces with exact rectangular tables of the corresponding
;; cardinalities. The shape and carrier checks make this representation
;; bidirectionally faithful.

(defun q1551745-matrix-row-p (ring row column-count)
  (declare (xargs :measure (nfix column-count)))
  (if (zp column-count)
      (equal row nil)
    (and
     (consp row)
     (q1551745-ring-element-p ring (car row))
     (q1551745-matrix-row-p
      ring (cdr row) (- column-count 1)))))

(defun q1551745-matrix-p
    (ring matrix row-count column-count)
  (declare (xargs :measure (nfix row-count)))
  (if (zp row-count)
      (equal matrix nil)
    (and
     (consp matrix)
     (q1551745-matrix-row-p
      ring (car matrix) column-count)
     (q1551745-matrix-p
      ring (cdr matrix) (- row-count 1) column-count))))

(defun q1551745-matrix-entry (matrix row column)
  (nth column (nth row matrix)))

(defun q1551745-matrix-add-row (ring left right remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (q1551745-ring-add ring (car left) (car right))
     (q1551745-matrix-add-row
      ring (cdr left) (cdr right) (- remaining 1)))))

(defun q1551745-matrix-add
    (ring left right row-count column-count)
  (declare (xargs :measure (nfix row-count)))
  (if (zp row-count)
      nil
    (cons
     (q1551745-matrix-add-row
      ring (car left) (car right) column-count)
     (q1551745-matrix-add
      ring (cdr left) (cdr right)
      (- row-count 1) column-count))))

(defun q1551745-matrix-negate-row (ring row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (q1551745-ring-negate ring (car row))
     (q1551745-matrix-negate-row
      ring (cdr row) (- remaining 1)))))

(defun q1551745-matrix-negate
    (ring matrix row-count column-count)
  (declare (xargs :measure (nfix row-count)))
  (if (zp row-count)
      nil
    (cons
     (q1551745-matrix-negate-row
      ring (car matrix) column-count)
     (q1551745-matrix-negate
      ring (cdr matrix) (- row-count 1) column-count))))

(defun q1551745-matrix-subtract
    (ring left right row-count column-count)
  (q1551745-matrix-add
   ring
   left
   (q1551745-matrix-negate
    ring right row-count column-count)
   row-count
   column-count))

;; Matrix multiplication uses the source order of multiplication; no
;; commutativity of ring multiplication is introduced.

(defun q1551745-dot-product-from
    (ring left right row column index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (q1551745-ring-zero ring)
    (q1551745-ring-add
     ring
     (q1551745-ring-multiply
      ring
      (q1551745-matrix-entry left row index)
      (q1551745-matrix-entry right index column))
     (q1551745-dot-product-from
      ring left right row column
      (+ index 1) (- remaining 1)))))

(defun q1551745-matrix-product-row
    (ring left right row inner-count column column-count)
  (declare (xargs :measure (nfix column-count)))
  (if (zp column-count)
      nil
    (cons
     (q1551745-dot-product-from
      ring left right row column 0 inner-count)
     (q1551745-matrix-product-row
      ring left right row inner-count
      (+ column 1) (- column-count 1)))))

(defun q1551745-matrix-product-rows
    (ring left right row inner-count
     total-column-count remaining-rows)
  (declare (xargs :measure (nfix remaining-rows)))
  (if (zp remaining-rows)
      nil
    (cons
     (q1551745-matrix-product-row
      ring left right row inner-count 0 total-column-count)
     (q1551745-matrix-product-rows
      ring left right (+ row 1) inner-count
      total-column-count (- remaining-rows 1)))))

(defun q1551745-matrix-multiply
    (ring left right row-count inner-count column-count)
  (q1551745-matrix-product-rows
   ring left right 0 inner-count column-count row-count))

(defun q1551745-identity-row
    (ring row column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (if (equal row column)
         (q1551745-ring-one ring)
       (q1551745-ring-zero ring))
     (q1551745-identity-row
      ring row (+ column 1) (- remaining 1)))))

(defun q1551745-identity-rows
    (ring dimension row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (q1551745-identity-row ring row 0 dimension)
     (q1551745-identity-rows
      ring dimension (+ row 1) (- remaining 1)))))

(defun q1551745-identity-matrix (ring dimension)
  (q1551745-identity-rows ring dimension 0 dimension))

;; This is exactly the data carried by Lean's Invertible instance: a selected
;; inverse with both inverse identities.

(defun q1551745-two-sided-inverse-p
    (ring matrix inverse dimension)
  (and
   (q1551745-matrix-p ring matrix dimension dimension)
   (q1551745-matrix-p ring inverse dimension dimension)
   (equal
    (q1551745-matrix-multiply
     ring inverse matrix dimension dimension dimension)
    (q1551745-identity-matrix ring dimension))
   (equal
    (q1551745-matrix-multiply
     ring matrix inverse dimension dimension dimension)
    (q1551745-identity-matrix ring dimension))))

(defun
    thousand-theorems-q1551745-binomial-inverse-theorem-statement
    (ring n m a u c v a-inverse middle-inverse sum-inverse)
  (let* ((c-times-v
          (q1551745-matrix-multiply ring c v m m n))
         (cv-times-a-inverse
          (q1551745-matrix-multiply
           ring c-times-v a-inverse m n n))
         (cva-inverse-times-u
          (q1551745-matrix-multiply
           ring cv-times-a-inverse u m n m))
         (cva-inverse-u-times-c
          (q1551745-matrix-multiply
           ring cva-inverse-times-u c m m m))
         (middle
          (q1551745-matrix-add
           ring c cva-inverse-u-times-c m m))
         (u-times-c
          (q1551745-matrix-multiply ring u c n m m))
         (uc-times-v
          (q1551745-matrix-multiply ring u-times-c v n m n))
         (sum
          (q1551745-matrix-add ring a uc-times-v n n))
         (a-inverse-times-u
          (q1551745-matrix-multiply
           ring a-inverse u n n m))
         (a-inverse-u-times-c
          (q1551745-matrix-multiply
           ring a-inverse-times-u c n m m))
         (a-inverse-u-c-times-middle-inverse
          (q1551745-matrix-multiply
           ring a-inverse-u-times-c middle-inverse n m m))
         (previous-times-c
          (q1551745-matrix-multiply
           ring a-inverse-u-c-times-middle-inverse c n m m))
         (previous-times-v
          (q1551745-matrix-multiply
           ring previous-times-c v n m n))
         (correction
          (q1551745-matrix-multiply
           ring previous-times-v a-inverse n n n))
         (binomial-inverse
          (q1551745-matrix-subtract
           ring a-inverse correction n n)))
    (implies
     (and
      (natp n)
      (natp m)
      (q1551745-ring-p ring)
      (q1551745-matrix-p ring a n n)
      (q1551745-matrix-p ring u n m)
      (q1551745-matrix-p ring c m m)
      (q1551745-matrix-p ring v m n)
      (q1551745-two-sided-inverse-p
       ring a a-inverse n)
      (q1551745-two-sided-inverse-p
       ring middle middle-inverse m)
      (q1551745-two-sided-inverse-p
       ring sum sum-inverse n))
     (equal sum-inverse binomial-inverse))))

(value-triple :itpeval-statement-checked)
:q
