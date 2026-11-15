;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__071, "Order of a Subgroup (Lagrange's Theorem)":
;; for every finite group and subgroup with the inherited multiplication,
;; inverse, and identity, the subgroup cardinality divides the group
;; cardinality. Finite carriers are duplicate-free lists of arbitrary ACL2
;; objects, with operations represented extensionally by lookup tables. This
;; file contains no proof.

(in-package "ACL2")

(defun ht071-product (x y product-table)
  (if (atom product-table)
      nil
    (let ((entry (car product-table)))
      (if (and (equal x (car entry))
               (equal y (cadr entry)))
          (caddr entry)
        (ht071-product x y (cdr product-table))))))

(defun ht071-inverse (x inverse-table)
  (if (atom inverse-table)
      nil
    (let ((entry (car inverse-table)))
      (if (equal x (car entry))
          (cadr entry)
        (ht071-inverse x (cdr inverse-table))))))

(defun ht071-subsetp-equal (xs ys)
  (if (atom xs)
      t
    (and (member-equal (car xs) ys)
         (ht071-subsetp-equal (cdr xs) ys))))

(defun ht071-product-closed-row-p
    (x ys carrier product-table)
  (if (atom ys)
      t
    (and
     (member-equal
      (ht071-product x (car ys) product-table)
      carrier)
     (ht071-product-closed-row-p
      x (cdr ys) carrier product-table))))

(defun ht071-product-closed-p
    (xs carrier product-table)
  (if (atom xs)
      t
    (and
     (ht071-product-closed-row-p
      (car xs) carrier carrier product-table)
     (ht071-product-closed-p
      (cdr xs) carrier product-table))))

(defun ht071-associative-third-p
    (x y zs product-table)
  (if (atom zs)
      t
    (and
     (equal
      (ht071-product
       x
       (ht071-product y (car zs) product-table)
       product-table)
      (ht071-product
       (ht071-product x y product-table)
       (car zs)
       product-table))
     (ht071-associative-third-p
      x y (cdr zs) product-table))))

(defun ht071-associative-second-p
    (x ys carrier product-table)
  (if (atom ys)
      t
    (and
     (ht071-associative-third-p
      x (car ys) carrier product-table)
     (ht071-associative-second-p
      x (cdr ys) carrier product-table))))

(defun ht071-associative-p
    (xs carrier product-table)
  (if (atom xs)
      t
    (and
     (ht071-associative-second-p
      (car xs) carrier carrier product-table)
     (ht071-associative-p
      (cdr xs) carrier product-table))))

(defun ht071-identity-laws-p
    (xs identity product-table)
  (if (atom xs)
      t
    (and
     (equal
      (ht071-product (car xs) identity product-table)
      (car xs))
     (equal
      (ht071-product identity (car xs) product-table)
      (car xs))
     (ht071-identity-laws-p
      (cdr xs) identity product-table))))

(defun ht071-inverse-laws-p
    (xs carrier identity product-table inverse-table)
  (if (atom xs)
      t
    (let ((x-inverse
           (ht071-inverse (car xs) inverse-table)))
      (and
       (member-equal x-inverse carrier)
       (equal
        (ht071-product (car xs) x-inverse product-table)
        identity)
       (equal
        (ht071-product x-inverse (car xs) product-table)
        identity)
       (ht071-inverse-laws-p
        (cdr xs)
        carrier
        identity
        product-table
        inverse-table)))))

(defun ht071-group-p
    (carrier product-table inverse-table identity)
  (and
   (true-listp carrier)
   (no-duplicatesp-equal carrier)
   (member-equal identity carrier)
   (ht071-product-closed-p
    carrier carrier product-table)
   (ht071-associative-p
    carrier carrier product-table)
   (ht071-identity-laws-p
    carrier identity product-table)
   (ht071-inverse-laws-p
    carrier
    carrier
    identity
    product-table
    inverse-table)))

(defun ht071-subgroup-p
    (subgroup carrier product-table inverse-table identity)
  (and
   (true-listp subgroup)
   (no-duplicatesp-equal subgroup)
   (ht071-subsetp-equal subgroup carrier)
   (ht071-group-p
    subgroup product-table inverse-table identity)))

(defun ht071-divides-p (d n)
  (and
   (natp d)
   (natp n)
   (if (equal d 0)
       (equal n 0)
     (equal (mod n d) 0))))

(defun hundred-theorems-071-order-of-a-subgroup-lagranges-theorem-statement
    (carrier subgroup product-table inverse-table identity)
  (implies
   (and
    (ht071-group-p
     carrier product-table inverse-table identity)
    (ht071-subgroup-p
     subgroup
     carrier
     product-table
     inverse-table
     identity))
   (ht071-divides-p
    (len subgroup)
    (len carrier))))

(value-triple :itpeval-statement-checked)
:q
