;; Statement-only formalization of PutnamBench corpus artifact putnam_1968_b2:
;; in every finite group, a subset containing more than half the elements
;; multiplicatively generates every element as a product of two of its
;; members. This file contains no proof.

(in-package "ACL2")

;; A finite group is represented by a duplicate-free enumeration of its
;; carrier and an extensional multiplication table. Every source finite group
;; yields such an encoding after choosing an enumeration, and every encoding
;; satisfying the predicate below determines a finite group. Likewise, A is a
;; duplicate-free enumeration of the source subset. Forgetting list order
;; recovers the source objects, so this is a bidirectional representation.

(defun putnam-1968-b2-table-has-key-p (key table)
  (if (assoc-equal key table) t nil))

(defun putnam-1968-b2-product (x y product-table)
  (cdr (assoc-equal (list x y) product-table)))

(defun putnam-1968-b2-subsetp-equal (xs ys)
  (if (atom xs)
      t
    (and
     (member-equal (car xs) ys)
     (putnam-1968-b2-subsetp-equal (cdr xs) ys))))

(defun putnam-1968-b2-product-closed-row-p
    (x ys carrier product-table)
  (if (atom ys)
      t
    (and
     (putnam-1968-b2-table-has-key-p
      (list x (car ys))
      product-table)
     (member-equal
      (putnam-1968-b2-product x (car ys) product-table)
      carrier)
     (putnam-1968-b2-product-closed-row-p
      x (cdr ys) carrier product-table))))

(defun putnam-1968-b2-product-closed-p
    (xs carrier product-table)
  (if (atom xs)
      t
    (and
     (putnam-1968-b2-product-closed-row-p
      (car xs) carrier carrier product-table)
     (putnam-1968-b2-product-closed-p
      (cdr xs) carrier product-table))))

(defun putnam-1968-b2-associative-third-p
    (x y zs product-table)
  (if (atom zs)
      t
    (and
     (equal
      (putnam-1968-b2-product
       x
       (putnam-1968-b2-product y (car zs) product-table)
       product-table)
      (putnam-1968-b2-product
       (putnam-1968-b2-product x y product-table)
       (car zs)
       product-table))
     (putnam-1968-b2-associative-third-p
      x y (cdr zs) product-table))))

(defun putnam-1968-b2-associative-second-p
    (x ys carrier product-table)
  (if (atom ys)
      t
    (and
     (putnam-1968-b2-associative-third-p
      x (car ys) carrier product-table)
     (putnam-1968-b2-associative-second-p
      x (cdr ys) carrier product-table))))

(defun putnam-1968-b2-associative-p
    (xs carrier product-table)
  (if (atom xs)
      t
    (and
     (putnam-1968-b2-associative-second-p
      (car xs) carrier carrier product-table)
     (putnam-1968-b2-associative-p
      (cdr xs) carrier product-table))))

(defun putnam-1968-b2-identity-laws-p
    (xs identity product-table)
  (if (atom xs)
      t
    (and
     (equal
      (putnam-1968-b2-product
       identity (car xs) product-table)
      (car xs))
     (equal
      (putnam-1968-b2-product
       (car xs) identity product-table)
      (car xs))
     (putnam-1968-b2-identity-laws-p
      (cdr xs) identity product-table))))

(defun putnam-1968-b2-inverse-exists-p
    (x candidates identity product-table)
  (if (atom candidates)
      nil
    (or
     (and
      (equal
       (putnam-1968-b2-product
        x (car candidates) product-table)
       identity)
      (equal
       (putnam-1968-b2-product
        (car candidates) x product-table)
       identity))
     (putnam-1968-b2-inverse-exists-p
      x (cdr candidates) identity product-table))))

(defun putnam-1968-b2-inverse-laws-p
    (xs carrier identity product-table)
  (if (atom xs)
      t
    (and
     (putnam-1968-b2-inverse-exists-p
      (car xs) carrier identity product-table)
     (putnam-1968-b2-inverse-laws-p
      (cdr xs) carrier identity product-table))))

(defun putnam-1968-b2-group-p
    (carrier identity product-table)
  (and
   (true-listp carrier)
   (no-duplicatesp-equal carrier)
   (member-equal identity carrier)
   (alistp product-table)
   (putnam-1968-b2-product-closed-p
    carrier carrier product-table)
   (putnam-1968-b2-associative-p
    carrier carrier product-table)
   (putnam-1968-b2-identity-laws-p
    carrier identity product-table)
   (putnam-1968-b2-inverse-laws-p
    carrier carrier identity product-table)))

(defun putnam-1968-b2-product-with-left-exists-p
    (target left right-candidates product-table)
  (if (atom right-candidates)
      nil
    (or
     (equal
      target
      (putnam-1968-b2-product
       left (car right-candidates) product-table))
     (putnam-1968-b2-product-with-left-exists-p
      target left (cdr right-candidates) product-table))))

(defun putnam-1968-b2-factorization-exists-p
    (target left-candidates subset product-table)
  (if (atom left-candidates)
      nil
    (or
     (putnam-1968-b2-product-with-left-exists-p
      target (car left-candidates) subset product-table)
     (putnam-1968-b2-factorization-exists-p
      target (cdr left-candidates) subset product-table))))

(defun putnam-1968-b2-every-element-factorizes-p
    (remaining subset product-table)
  (if (atom remaining)
      t
    (and
     (putnam-1968-b2-factorization-exists-p
      (car remaining) subset subset product-table)
     (putnam-1968-b2-every-element-factorizes-p
      (cdr remaining) subset product-table))))

(defun putnambench-putnam-1968-b2-statement
    (carrier identity product-table subset)
  (implies
   (and
    (putnam-1968-b2-group-p
     carrier identity product-table)
    (true-listp subset)
    (no-duplicatesp-equal subset)
    (putnam-1968-b2-subsetp-equal subset carrier)
    (< (len carrier) (* 2 (len subset))))
   (putnam-1968-b2-every-element-factorizes-p
    carrier subset product-table)))

(value-triple :itpeval-statement-checked)
:q
