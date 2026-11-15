;; Statement-only formalization of thousand-theorems corpus artifact Q632546,
;; "Bertrand's postulate": for every positive natural number n, there exists
;; a prime p with n < p and p <= 2 * n. This file contains no proof.

(in-package "ACL2")

(defun q632546-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (q632546-no-divisor-from-p number (+ divisor 1)))
    t))

(defun q632546-primep (number)
  (and (natp number)
       (< 1 number)
       (q632546-no-divisor-from-p number 2)))

(defun q632546-prime-in-interval-p (lower upper)
  (declare (xargs :measure (nfix upper)))
  (if (or (not (natp lower))
          (not (natp upper))
          (zp upper)
          (< upper lower))
      nil
    (or (q632546-primep upper)
        (q632546-prime-in-interval-p lower (- upper 1)))))

(defun thousand-theorems-q632546-bertrands-postulate-statement (n)
  (implies
   (and (natp n)
        (not (equal n 0)))
   (q632546-prime-in-interval-p (+ n 1) (* 2 n))))

(value-triple :itpeval-statement-checked)
:q
