;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__044, "The Binomial Theorem": in the free
;; commutative semiring on two generators, the coefficient row of (X + Y)^n
;; equals the nth Pascal row. By evaluation at arbitrary elements, and
;; conversely by choosing the free generators, this is equivalent to the
;; binomial expansion in every commutative semiring. This file contains no
;; proof.

(in-package "ACL2")

;; A row (c_0 ... c_d) represents the homogeneous polynomial
;; sum_k c_k * X^k * Y^(d-k). Multiplication is coefficient convolution.
(defun ht044-row-add (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (atom left)
      right
    (if (atom right)
        left
      (cons (+ (car left) (car right))
            (ht044-row-add (cdr left) (cdr right))))))

(defun ht044-row-scale (coefficient row)
  (if (atom row)
      nil
    (cons (* coefficient (car row))
          (ht044-row-scale coefficient (cdr row)))))

(defun ht044-row-convolution (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (atom left)
      nil
    (ht044-row-add
     (ht044-row-scale (car left) right)
     (cons 0
           (ht044-row-convolution (cdr left) right)))))

(defun ht044-x-plus-y-power-row (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 1)
    (ht044-row-convolution
     (list 1 1)
     (ht044-x-plus-y-power-row (- n 1)))))

;; Padding a Pascal row by zero on both sides and adding adjacent
;; coefficients produces its successor row.
(defun ht044-pascal-next-row-aux (row left-neighbor)
  (declare (xargs :measure (acl2-count row)))
  (if (atom row)
      (list left-neighbor)
    (cons (+ left-neighbor (car row))
          (ht044-pascal-next-row-aux
           (cdr row)
           (car row)))))

(defun ht044-pascal-next-row (row)
  (ht044-pascal-next-row-aux row 0))

(defun ht044-pascal-row (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list 1)
    (ht044-pascal-next-row
     (ht044-pascal-row (- n 1)))))

(defun hundred-theorems-044-the-binomial-theorem-statement (n)
  (implies
   (natp n)
   (equal
    (ht044-x-plus-y-power-row n)
    (ht044-pascal-row n))))

(value-triple :itpeval-statement-checked)
:q
