;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_b2:
;; no finite group is the union of two proper subgroups, while the Klein four
;; group is the union of three proper subgroups. This file contains no proof.

(in-package "ACL2")

;; A finite group is represented by a duplicate-free carrier enumeration and
;; total multiplication and inverse tables. Every source finite group yields
;; such data after choosing an enumeration, and every data tuple satisfying
;; the predicates below determines a finite group. The powerset search ranges
;; over every subgroup extensionally, so no subgroup family is externalized.

(defun putnam-1969-b2-subsetp-equal (xs ys)
  (if (endp xs)
      t
    (and
     (member-equal (car xs) ys)
     (putnam-1969-b2-subsetp-equal (cdr xs) ys))))

(defun putnam-1969-b2-product-entry (x y product-table)
  (assoc-equal (list x y) product-table))

(defun putnam-1969-b2-product (x y product-table)
  (cdr (putnam-1969-b2-product-entry x y product-table)))

(defun putnam-1969-b2-inverse-entry (x inverse-table)
  (assoc-equal x inverse-table))

(defun putnam-1969-b2-inverse (x inverse-table)
  (cdr (putnam-1969-b2-inverse-entry x inverse-table)))

(defun putnam-1969-b2-product-row-total-p
    (x ys carrier product-table)
  (if (endp ys)
      t
    (and
     (consp
      (putnam-1969-b2-product-entry
       x (car ys) product-table))
     (member-equal
      (putnam-1969-b2-product
       x (car ys) product-table)
      carrier)
     (putnam-1969-b2-product-row-total-p
      x (cdr ys) carrier product-table))))

(defun putnam-1969-b2-product-total-p
    (xs carrier product-table)
  (if (endp xs)
      t
    (and
     (putnam-1969-b2-product-row-total-p
      (car xs) carrier carrier product-table)
     (putnam-1969-b2-product-total-p
      (cdr xs) carrier product-table))))

(defun putnam-1969-b2-inverse-total-p
    (xs carrier inverse-table)
  (if (endp xs)
      t
    (and
     (consp
      (putnam-1969-b2-inverse-entry
       (car xs) inverse-table))
     (member-equal
      (putnam-1969-b2-inverse
       (car xs) inverse-table)
      carrier)
     (putnam-1969-b2-inverse-total-p
      (cdr xs) carrier inverse-table))))

(defun putnam-1969-b2-associative-third-p
    (x y zs product-table)
  (if (endp zs)
      t
    (and
     (equal
      (putnam-1969-b2-product
       (putnam-1969-b2-product
        x y product-table)
       (car zs)
       product-table)
      (putnam-1969-b2-product
       x
       (putnam-1969-b2-product
        y (car zs) product-table)
       product-table))
     (putnam-1969-b2-associative-third-p
      x y (cdr zs) product-table))))

(defun putnam-1969-b2-associative-second-p
    (x ys carrier product-table)
  (if (endp ys)
      t
    (and
     (putnam-1969-b2-associative-third-p
      x (car ys) carrier product-table)
     (putnam-1969-b2-associative-second-p
      x (cdr ys) carrier product-table))))

(defun putnam-1969-b2-associative-p
    (xs carrier product-table)
  (if (endp xs)
      t
    (and
     (putnam-1969-b2-associative-second-p
      (car xs) carrier carrier product-table)
     (putnam-1969-b2-associative-p
      (cdr xs) carrier product-table))))

(defun putnam-1969-b2-identity-laws-p
    (xs identity product-table)
  (if (endp xs)
      t
    (and
     (equal
      (putnam-1969-b2-product
       identity (car xs) product-table)
      (car xs))
     (equal
      (putnam-1969-b2-product
       (car xs) identity product-table)
      (car xs))
     (putnam-1969-b2-identity-laws-p
      (cdr xs) identity product-table))))

(defun putnam-1969-b2-inverse-laws-p
    (xs identity product-table inverse-table)
  (if (endp xs)
      t
    (let ((x-inverse
           (putnam-1969-b2-inverse
            (car xs) inverse-table)))
      (and
       (equal
        (putnam-1969-b2-product
         (car xs) x-inverse product-table)
        identity)
       (equal
        (putnam-1969-b2-product
         x-inverse (car xs) product-table)
        identity)
       (putnam-1969-b2-inverse-laws-p
        (cdr xs)
        identity
        product-table
        inverse-table)))))

(defun putnam-1969-b2-group-p
    (carrier identity product-table inverse-table)
  (and
   (true-listp carrier)
   (no-duplicatesp-equal carrier)
   (member-equal identity carrier)
   (alistp product-table)
   (alistp inverse-table)
   (putnam-1969-b2-product-total-p
    carrier carrier product-table)
   (putnam-1969-b2-inverse-total-p
    carrier carrier inverse-table)
   (putnam-1969-b2-associative-p
    carrier carrier product-table)
   (putnam-1969-b2-identity-laws-p
    carrier identity product-table)
   (putnam-1969-b2-inverse-laws-p
    carrier identity product-table inverse-table)))

(defun putnam-1969-b2-subgroup-product-row-p
    (x ys subgroup product-table)
  (if (endp ys)
      t
    (and
     (member-equal
      (putnam-1969-b2-product
       x (car ys) product-table)
      subgroup)
     (putnam-1969-b2-subgroup-product-row-p
      x (cdr ys) subgroup product-table))))

(defun putnam-1969-b2-subgroup-product-closed-p
    (xs subgroup product-table)
  (if (endp xs)
      t
    (and
     (putnam-1969-b2-subgroup-product-row-p
      (car xs) subgroup subgroup product-table)
     (putnam-1969-b2-subgroup-product-closed-p
      (cdr xs) subgroup product-table))))

(defun putnam-1969-b2-subgroup-inverse-closed-p
    (xs subgroup inverse-table)
  (if (endp xs)
      t
    (and
     (member-equal
      (putnam-1969-b2-inverse
       (car xs) inverse-table)
      subgroup)
     (putnam-1969-b2-subgroup-inverse-closed-p
      (cdr xs) subgroup inverse-table))))

(defun putnam-1969-b2-subgroup-p
    (subgroup carrier identity product-table inverse-table)
  (and
   (true-listp subgroup)
   (no-duplicatesp-equal subgroup)
   (putnam-1969-b2-subsetp-equal subgroup carrier)
   (member-equal identity subgroup)
   (putnam-1969-b2-subgroup-product-closed-p
    subgroup subgroup product-table)
   (putnam-1969-b2-subgroup-inverse-closed-p
    subgroup subgroup inverse-table)))

(defun putnam-1969-b2-proper-subgroup-p
    (subgroup carrier identity product-table inverse-table)
  (and
   (putnam-1969-b2-subgroup-p
    subgroup carrier identity product-table inverse-table)
   (not
    (putnam-1969-b2-subsetp-equal
     carrier subgroup))))

(defun putnam-1969-b2-adjoin-to-each (element sets)
  (if (endp sets)
      nil
    (cons
     (cons element (car sets))
     (putnam-1969-b2-adjoin-to-each
      element (cdr sets)))))

(defun putnam-1969-b2-powerset (carrier)
  (if (endp carrier)
      (list nil)
    (let ((tail-powerset
           (putnam-1969-b2-powerset (cdr carrier))))
      (append
       tail-powerset
       (putnam-1969-b2-adjoin-to-each
        (car carrier) tail-powerset)))))

(defun putnam-1969-b2-covered-by-two-p
    (remaining left right)
  (if (endp remaining)
      t
    (and
     (or
      (member-equal (car remaining) left)
      (member-equal (car remaining) right))
     (putnam-1969-b2-covered-by-two-p
      (cdr remaining) left right))))

(defun putnam-1969-b2-no-cover-with-left-p
    (left candidates carrier identity product-table inverse-table)
  (if (endp candidates)
      t
    (and
     (implies
      (and
       (putnam-1969-b2-proper-subgroup-p
        left carrier identity product-table inverse-table)
       (putnam-1969-b2-proper-subgroup-p
        (car candidates)
        carrier
        identity
        product-table
        inverse-table))
      (not
       (putnam-1969-b2-covered-by-two-p
        carrier left (car candidates))))
     (putnam-1969-b2-no-cover-with-left-p
      left
      (cdr candidates)
      carrier
      identity
      product-table
      inverse-table))))

(defun putnam-1969-b2-no-two-proper-subgroups-cover-p
    (remaining candidates carrier identity product-table inverse-table)
  (if (endp remaining)
      t
    (and
     (putnam-1969-b2-no-cover-with-left-p
      (car remaining)
      candidates
      carrier
      identity
      product-table
      inverse-table)
     (putnam-1969-b2-no-two-proper-subgroups-cover-p
      (cdr remaining)
      candidates
      carrier
      identity
      product-table
      inverse-table))))

(defun putnam-1969-b2-v4-carrier ()
  '(0 1 2 3))

(defun putnam-1969-b2-v4-product-table ()
  '(((0 0) . 0)
    ((0 1) . 1)
    ((0 2) . 2)
    ((0 3) . 3)
    ((1 0) . 1)
    ((1 1) . 0)
    ((1 2) . 3)
    ((1 3) . 2)
    ((2 0) . 2)
    ((2 1) . 3)
    ((2 2) . 0)
    ((2 3) . 1)
    ((3 0) . 3)
    ((3 1) . 2)
    ((3 2) . 1)
    ((3 3) . 0)))

(defun putnam-1969-b2-v4-inverse-table ()
  '((0 . 0)
    (1 . 1)
    (2 . 2)
    (3 . 3)))

(defun putnam-1969-b2-covered-by-three-p
    (remaining first second third)
  (if (endp remaining)
      t
    (and
     (or
      (member-equal (car remaining) first)
      (member-equal (car remaining) second)
      (member-equal (car remaining) third))
     (putnam-1969-b2-covered-by-three-p
      (cdr remaining) first second third))))

(defun putnam-1969-b2-v4-three-subgroup-counterexample-p ()
  (let ((carrier (putnam-1969-b2-v4-carrier))
        (identity 0)
        (product-table
         (putnam-1969-b2-v4-product-table))
        (inverse-table
         (putnam-1969-b2-v4-inverse-table))
        (first '(0 1))
        (second '(0 2))
        (third '(0 3)))
    (and
     (putnam-1969-b2-group-p
      carrier identity product-table inverse-table)
     (putnam-1969-b2-proper-subgroup-p
      first carrier identity product-table inverse-table)
     (putnam-1969-b2-proper-subgroup-p
      second carrier identity product-table inverse-table)
     (putnam-1969-b2-proper-subgroup-p
      third carrier identity product-table inverse-table)
     (putnam-1969-b2-covered-by-three-p
      carrier first second third))))

(defun putnambench-putnam-1969-b2-statement
    (carrier identity product-table inverse-table)
  (and
   (implies
    (putnam-1969-b2-group-p
     carrier identity product-table inverse-table)
    (let ((all-subsets
           (putnam-1969-b2-powerset carrier)))
      (putnam-1969-b2-no-two-proper-subgroups-cover-p
       all-subsets
       all-subsets
       carrier
       identity
       product-table
       inverse-table)))
   (putnam-1969-b2-v4-three-subgroup-counterexample-p)))

(value-triple :itpeval-statement-checked)
:q
