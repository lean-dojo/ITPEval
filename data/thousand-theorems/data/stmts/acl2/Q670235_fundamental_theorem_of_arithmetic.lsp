;; Statement-only formalization of thousand-theorems corpus artifact Q670235,
;; "Fundamental theorem of arithmetic": every finite list of natural primes
;; whose product is n is a permutation of the canonical increasing
;; prime-factor list of n. This file contains no proof.

(in-package "ACL2")

(defun q670235-least-divisor-from (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (< 1 d)
           (< d n))
      (if (equal (mod n d) 0)
          d
        (q670235-least-divisor-from n (+ d 1)))
    n))

(defun q670235-least-divisor (n)
  (if (and (natp n)
           (< 1 n))
      (q670235-least-divisor-from n 2)
    n))

(defun q670235-primep (n)
  (and (natp n)
       (< 1 n)
       (equal (q670235-least-divisor n) n)))

(defun q670235-prime-factors-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (natp n))
          (< n 2)
          (zp fuel))
      nil
    (let ((p (q670235-least-divisor n)))
      (cons p
            (q670235-prime-factors-aux
             (floor n p)
             (- fuel 1))))))

(defun q670235-prime-factors (n)
  (q670235-prime-factors-aux n n))

(defun q670235-list-product (factors)
  (if (consp factors)
      (* (car factors)
         (q670235-list-product (cdr factors)))
    1))

(defun q670235-prime-list-p (factors)
  (if (consp factors)
      (and (q670235-primep (car factors))
           (q670235-prime-list-p (cdr factors)))
    (null factors)))

(defun q670235-delete-one (x factors)
  (if (consp factors)
      (if (equal x (car factors))
          (cdr factors)
        (cons (car factors)
              (q670235-delete-one x (cdr factors))))
    nil))

(defun q670235-permutation-p (left right)
  (if (consp left)
      (and (member-equal (car left) right)
           (q670235-permutation-p
            (cdr left)
            (q670235-delete-one (car left) right)))
    (null right)))

(defun q670235-fundamental-theorem-of-arithmetic-statement-p
    (n factors)
  (implies
   (and (natp n)
        (q670235-prime-list-p factors)
        (equal (q670235-list-product factors) n))
   (q670235-permutation-p
    factors
    (q670235-prime-factors n))))

(value-triple :itpeval-statement-checked)
:q
