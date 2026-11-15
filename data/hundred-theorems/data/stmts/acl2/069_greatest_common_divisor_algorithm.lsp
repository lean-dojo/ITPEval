;; Statement-only formalization of Hundred Theorems artifact
;; hundred-theorems__acl2__069, "Greatest Common Divisor Algorithm":
;; for natural numbers, the subtraction-based Euclidean algorithm returns a
;; common divisor divisible by every common divisor. This file contains no
;; proof.

(in-package "ACL2")

(defun hundred-theorems-069-egcd (m n)
  (declare (xargs :measure (+ (nfix m) (nfix n))))
  (if (and (natp m) (natp n))
      (cond ((equal m 0) n)
            ((equal n 0) m)
            ((<= m n)
             (hundred-theorems-069-egcd m (- n m)))
            (t
             (hundred-theorems-069-egcd (- m n) n)))
    0))

(defun hundred-theorems-069-divides-p (d n)
  (and (natp d)
       (natp n)
       (if (equal d 0)
           (equal n 0)
         (equal (mod n d) 0))))

(defun hundred-theorems-069-greatest-common-divisor-algorithm-statement
  (m n d)
  (implies
   (and (natp m)
        (natp n)
        (natp d))
   (let ((g (hundred-theorems-069-egcd m n)))
     (and (hundred-theorems-069-divides-p g m)
          (hundred-theorems-069-divides-p g n)
          (implies
           (and (hundred-theorems-069-divides-p d m)
                (hundred-theorems-069-divides-p d n))
           (hundred-theorems-069-divides-p d g))))))

(value-triple :itpeval-statement-checked)
:q
