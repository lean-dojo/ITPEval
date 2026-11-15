;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__098, "Bertrand's Postulate": for every positive
;; natural number n, there exists a prime p with n < p <= 2n. The bounded
;; search through 2n encodes the existential witness. This file contains no
;; proof.

(in-package "ACL2")

(defun hundred-theorems-098-has-nontrivial-divisor (p d)
  (declare (xargs :measure (nfix d)))
  (if (or (not (natp d))
          (< d 2))
      nil
    (or (equal (mod p d) 0)
        (hundred-theorems-098-has-nontrivial-divisor p (- d 1)))))

(defun hundred-theorems-098-primep (p)
  (and (natp p)
       (< 1 p)
       (not (hundred-theorems-098-has-nontrivial-divisor
             p
             (- p 1)))))

(defun hundred-theorems-098-prime-above-through (n upper)
  (declare (xargs :measure (nfix upper)))
  (if (or (not (natp n))
          (zp upper)
          (<= upper n))
      nil
    (or (hundred-theorems-098-primep upper)
        (hundred-theorems-098-prime-above-through n (- upper 1)))))

(defun hundred-theorems-098-bertrands-postulate-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (hundred-theorems-098-prime-above-through n (* 2 n))))

(value-triple :itpeval-statement-checked)
:q
