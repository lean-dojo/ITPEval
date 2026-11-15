;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__080, "The Fundamental Theorem of Arithmetic":
;; every positive natural number has a unique nondecreasing list of prime
;; factors whose product is that number. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-080-least-divisor-from (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (< 1 d)
           (< d n))
      (if (equal (mod n d) 0)
          d
        (hundred-theorems-080-least-divisor-from n (+ d 1)))
    n))

(defun hundred-theorems-080-least-divisor (n)
  (if (and (natp n)
           (< 1 n))
      (hundred-theorems-080-least-divisor-from n 2)
    n))

(defun hundred-theorems-080-primep (n)
  (and (natp n)
       (< 1 n)
       (equal (hundred-theorems-080-least-divisor n) n)))

(defun hundred-theorems-080-prime-factors-aux (n fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (not (natp n))
          (< n 2)
          (zp fuel))
      nil
    (let ((p (hundred-theorems-080-least-divisor n)))
      (cons p
            (hundred-theorems-080-prime-factors-aux
             (floor n p)
             (- fuel 1))))))

(defun hundred-theorems-080-prime-factors (n)
  (hundred-theorems-080-prime-factors-aux n n))

(defun hundred-theorems-080-list-product (factors)
  (if (consp factors)
      (* (car factors)
         (hundred-theorems-080-list-product (cdr factors)))
    1))

(defun hundred-theorems-080-prime-list-p (factors)
  (if (consp factors)
      (and (hundred-theorems-080-primep (car factors))
           (hundred-theorems-080-prime-list-p (cdr factors)))
    (null factors)))

(defun hundred-theorems-080-nondecreasing-p (factors)
  (if (and (consp factors)
           (consp (cdr factors)))
      (and (<= (car factors) (cadr factors))
           (hundred-theorems-080-nondecreasing-p (cdr factors)))
    t))

(defun hundred-theorems-080-prime-decomposition-p (n factors)
  (and (natp n)
       (< 0 n)
       (hundred-theorems-080-prime-list-p factors)
       (hundred-theorems-080-nondecreasing-p factors)
       (equal (hundred-theorems-080-list-product factors) n)))

(defun hundred-theorems-080-fundamental-theorem-of-arithmetic-statement
  (n factors)
  (implies
   (and (natp n)
        (< 0 n))
   (let ((canonical
          (hundred-theorems-080-prime-factors n)))
     (and
      (hundred-theorems-080-prime-decomposition-p n canonical)
      (implies
       (hundred-theorems-080-prime-decomposition-p n factors)
       (equal factors canonical))))))

(value-triple :itpeval-statement-checked)
:q
