;; Statement-only formalization of Hundred Theorems artifact
;; hundred-theorems__acl2__051, "Wilson's Theorem": for every natural number
;; n other than 1, n is prime exactly when (n - 1)! is congruent to -1
;; modulo n. This file contains no proof.

(in-package "ACL2")

(defun hundred-theorems-051-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (hundred-theorems-051-factorial (- n 1)))))

(defun hundred-theorems-051-no-divisor-from-p (n d)
  (declare (xargs :measure (nfix (- n d))))
  (if (and (natp n)
           (natp d)
           (<= 2 d)
           (< d n))
      (and (not (equal (mod n d) 0))
           (hundred-theorems-051-no-divisor-from-p n (+ d 1)))
    t))

(defun hundred-theorems-051-primep (n)
  (and (natp n)
       (< 1 n)
       (hundred-theorems-051-no-divisor-from-p n 2)))

(defun hundred-theorems-051-congruent-p (x y n)
  (and (integerp x)
       (integerp y)
       (natp n)
       (if (equal n 0)
           (equal x y)
         (equal (mod x n) (mod y n)))))

(defun hundred-theorems-051-wilsons-theorem-statement (n)
  (implies
   (and (natp n)
        (not (equal n 1)))
   (equal
    (hundred-theorems-051-primep n)
    (hundred-theorems-051-congruent-p
     (hundred-theorems-051-factorial (nfix (- n 1)))
     -1
     n))))

(value-triple :itpeval-statement-checked)
:q
