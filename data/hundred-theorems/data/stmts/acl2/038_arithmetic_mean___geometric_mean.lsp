;; Statement-only formalization of Hundred Theorems artifact 038,
;; "Arithmetic Mean / Geometric Mean." For every nonempty finite family of
;; nonnegative elements of a linearly ordered field, the product is at most
;; the nth power of the arithmetic mean, with equality exactly when all terms
;; are equal. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub ht038-carrier (x) t)
(defstub ht038-add-op (x y) t)
(defstub ht038-multiply-op (x y) t)
(defstub ht038-negate-op (x) t)
(defstub ht038-inverse-op (x) t)
(defstub ht038-less-op (x y) t)

(defun ht038-member-p (x)
  (if (ht038-carrier x) t nil))

(defun ht038-add (x y)
  (ht038-add-op x y))

(defun ht038-multiply (x y)
  (ht038-multiply-op x y))

(defun ht038-negate (x)
  (ht038-negate-op x))

(defun ht038-inverse (x)
  (ht038-inverse-op x))

(defun ht038-less (x y)
  (if (ht038-less-op x y) t nil))

(defun-sk ht038-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht038-member-p x)
      (ht038-member-p y)
      (ht038-member-p z))
     (and
      (ht038-member-p (ht038-add x y))
      (ht038-member-p (ht038-multiply x y))
      (ht038-member-p (ht038-negate x))
      (ht038-member-p (ht038-inverse x))
      (equal (ht038-add (ht038-add x y) z)
             (ht038-add x (ht038-add y z)))
      (equal (ht038-add x y)
             (ht038-add y x))
      (equal (ht038-add x zero) x)
      (equal (ht038-add x (ht038-negate x)) zero)
      (equal (ht038-multiply (ht038-multiply x y) z)
             (ht038-multiply x (ht038-multiply y z)))
      (equal (ht038-multiply x y)
             (ht038-multiply y x))
      (equal (ht038-multiply x one) x)
      (equal
       (ht038-multiply x (ht038-add y z))
       (ht038-add
        (ht038-multiply x y)
        (ht038-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht038-multiply x (ht038-inverse x))
        one))))))

(defun-sk ht038-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht038-member-p x)
      (ht038-member-p y)
      (ht038-member-p z))
     (and
      (not (ht038-less x x))
      (or
       (equal x y)
       (ht038-less x y)
       (ht038-less y x))
      (implies
       (and
        (ht038-less x y)
        (ht038-less y z))
       (ht038-less x z))
      (implies
       (ht038-less x y)
       (ht038-less
        (ht038-add x z)
        (ht038-add y z)))
      (implies
       (and
        (ht038-less zero x)
        (ht038-less zero y))
       (ht038-less zero (ht038-multiply x y)))))))

(defun ht038-ordered-field-p (zero one)
  (and
   (ht038-member-p zero)
   (ht038-member-p one)
   (not (equal zero one))
   (ht038-less zero one)
   (ht038-field-laws-p zero one)
   (ht038-order-laws-p zero)))

(defun ht038-nonnegative-p (zero value)
  (and
   (ht038-member-p value)
   (not (ht038-less value zero))))

(defun ht038-nonnegative-list-p (zero values)
  (if (consp values)
      (and
       (ht038-nonnegative-p zero (car values))
       (ht038-nonnegative-list-p zero (cdr values)))
    (equal values nil)))

(defun ht038-sum (values zero)
  (if (consp values)
      (ht038-add
       (car values)
       (ht038-sum (cdr values) zero))
    zero))

(defun ht038-product (values one)
  (if (consp values)
      (ht038-multiply
       (car values)
       (ht038-product (cdr values) one))
    one))

(defun ht038-natural-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ht038-add
     one
     (ht038-natural-value (- n 1) zero one))))

(defun ht038-power (value n one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (ht038-multiply
     value
     (ht038-power value (- n 1) one))))

(defun ht038-all-equal-to-p (values common-value)
  (if (consp values)
      (and
       (equal (car values) common-value)
       (ht038-all-equal-to-p (cdr values) common-value))
    (equal values nil)))

(defun ht038-am-gm-conclusion-p (values n zero one)
  (let* ((n-value
          (ht038-natural-value n zero one))
         (mean
          (ht038-multiply
           (ht038-sum values zero)
           (ht038-inverse n-value)))
         (product
          (ht038-product values one))
         (mean-to-n
          (ht038-power mean n one))
         (all-equal
          (ht038-all-equal-to-p values (car values))))
    (and
     (not (ht038-less mean-to-n product))
     (iff (equal product mean-to-n)
          all-equal))))

(defun-sk hundred-theorems-038-arithmetic-mean-geometric-mean-statement
    (zero one)
  (forall (values n)
    (implies
     (and
      (ht038-ordered-field-p zero one)
      (natp n)
      (< 0 n)
      (true-listp values)
      (equal (len values) n)
      (ht038-nonnegative-list-p zero values))
     (ht038-am-gm-conclusion-p values n zero one))))

(value-triple :itpeval-statement-checked)
:q
