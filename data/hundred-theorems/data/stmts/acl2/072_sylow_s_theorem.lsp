;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__072, "Sylow's Theorem": for every finite group,
;; prime p, and natural exponent n such that p^n divides the group order,
;; there exists a subgroup of order p^n. Finite carriers are duplicate-free
;; lists of arbitrary ACL2 objects, with operations represented extensionally
;; by lookup tables; an exhaustive subset search keeps the subgroup witness
;; internal to the conclusion. This file contains no proof.

(in-package "ACL2")

(defun ht072-product (x y product-table)
  (if (atom product-table)
      nil
    (let ((entry (car product-table)))
      (if (and (equal x (car entry))
               (equal y (cadr entry)))
          (caddr entry)
        (ht072-product x y (cdr product-table))))))

(defun ht072-inverse (x inverse-table)
  (if (atom inverse-table)
      nil
    (let ((entry (car inverse-table)))
      (if (equal x (car entry))
          (cadr entry)
        (ht072-inverse x (cdr inverse-table))))))

(defun ht072-subsetp-equal (xs ys)
  (if (atom xs)
      t
    (and (member-equal (car xs) ys)
         (ht072-subsetp-equal (cdr xs) ys))))

(defun ht072-product-closed-row-p
    (x ys carrier product-table)
  (if (atom ys)
      t
    (and
     (member-equal
      (ht072-product x (car ys) product-table)
      carrier)
     (ht072-product-closed-row-p
      x (cdr ys) carrier product-table))))

(defun ht072-product-closed-p
    (xs carrier product-table)
  (if (atom xs)
      t
    (and
     (ht072-product-closed-row-p
      (car xs) carrier carrier product-table)
     (ht072-product-closed-p
      (cdr xs) carrier product-table))))

(defun ht072-associative-third-p
    (x y zs product-table)
  (if (atom zs)
      t
    (and
     (equal
      (ht072-product
       x
       (ht072-product y (car zs) product-table)
       product-table)
      (ht072-product
       (ht072-product x y product-table)
       (car zs)
       product-table))
     (ht072-associative-third-p
      x y (cdr zs) product-table))))

(defun ht072-associative-second-p
    (x ys carrier product-table)
  (if (atom ys)
      t
    (and
     (ht072-associative-third-p
      x (car ys) carrier product-table)
     (ht072-associative-second-p
      x (cdr ys) carrier product-table))))

(defun ht072-associative-p
    (xs carrier product-table)
  (if (atom xs)
      t
    (and
     (ht072-associative-second-p
      (car xs) carrier carrier product-table)
     (ht072-associative-p
      (cdr xs) carrier product-table))))

(defun ht072-identity-laws-p
    (xs identity product-table)
  (if (atom xs)
      t
    (and
     (equal
      (ht072-product (car xs) identity product-table)
      (car xs))
     (equal
      (ht072-product identity (car xs) product-table)
      (car xs))
     (ht072-identity-laws-p
      (cdr xs) identity product-table))))

(defun ht072-inverse-laws-p
    (xs carrier identity product-table inverse-table)
  (if (atom xs)
      t
    (let ((x-inverse
           (ht072-inverse (car xs) inverse-table)))
      (and
       (member-equal x-inverse carrier)
       (equal
        (ht072-product (car xs) x-inverse product-table)
        identity)
       (equal
        (ht072-product x-inverse (car xs) product-table)
        identity)
       (ht072-inverse-laws-p
        (cdr xs)
        carrier
        identity
        product-table
        inverse-table)))))

(defun ht072-group-p
    (carrier product-table inverse-table identity)
  (and
   (true-listp carrier)
   (no-duplicatesp-equal carrier)
   (member-equal identity carrier)
   (ht072-product-closed-p
    carrier carrier product-table)
   (ht072-associative-p
    carrier carrier product-table)
   (ht072-identity-laws-p
    carrier identity product-table)
   (ht072-inverse-laws-p
    carrier
    carrier
    identity
    product-table
    inverse-table)))

(defun ht072-subgroup-p
    (subgroup carrier product-table inverse-table identity)
  (and
   (true-listp subgroup)
   (no-duplicatesp-equal subgroup)
   (ht072-subsetp-equal subgroup carrier)
   (ht072-group-p
    subgroup product-table inverse-table identity)))

(defun ht072-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (ht072-no-divisor-from-p n (+ d 1)))
    t))

(defun ht072-primep (n)
  (and (natp n)
       (< 1 n)
       (ht072-no-divisor-from-p n 2)))

(defun ht072-divides-p (d n)
  (and
   (natp d)
   (natp n)
   (if (equal d 0)
       (equal n 0)
     (equal (mod n d) 0))))

(defun ht072-has-subgroup-of-order-p
    (remaining chosen carrier product-table inverse-table identity order)
  (if (atom remaining)
      (and
       (equal (len chosen) order)
       (ht072-subgroup-p
        chosen carrier product-table inverse-table identity))
    (or
     (ht072-has-subgroup-of-order-p
      (cdr remaining)
      (cons (car remaining) chosen)
      carrier
      product-table
      inverse-table
      identity
      order)
     (ht072-has-subgroup-of-order-p
      (cdr remaining)
      chosen
      carrier
      product-table
      inverse-table
      identity
      order))))

(defun hundred-theorems-072-sylows-theorem-statement
    (carrier product-table inverse-table identity p exponent)
  (implies
   (and
    (ht072-group-p
     carrier product-table inverse-table identity)
    (ht072-primep p)
    (natp exponent)
    (ht072-divides-p
     (expt p exponent)
     (len carrier)))
   (ht072-has-subgroup-of-order-p
    carrier
    nil
    carrier
    product-table
    inverse-table
    identity
    (expt p exponent))))

(value-triple :itpeval-statement-checked)
:q
