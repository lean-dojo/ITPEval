;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_aneqprodakp4_anmsqrtanp1eq2: a real sequence beginning with
;; a(0) = 1 and satisfying a(n+1) = product(k=0..n, a(k)) + 4 has
;; a(n) - sqrt(a(n+1)) = 2 for every natural n >= 1. This file contains no
;; proof.
;;
;; The initial value and recurrence uniquely determine the sequence. The
;; prefix product below is integral, induces exactly that real sequence, and
;; therefore eliminates the function parameter without restricting its
;; domain or using a finite table. Its terms are positive; for real x and
;; nonnegative y, x - sqrt(y) = 2 is equivalent to x >= 2 and
;; y = (x-2)^2. The statement uses this exact square-root-free form.

(in-package "ACL2")

(defun numbertheory-aneqprodakp4-prefix-product (n)
  (declare (xargs :measure (nfix n)))
  (if (not (natp n))
      1
    (if (zp n)
        1
      (let ((previous
             (numbertheory-aneqprodakp4-prefix-product (- n 1))))
        (* previous (+ previous 4))))))

(defun numbertheory-aneqprodakp4-sequence (n)
  (if (not (natp n))
      0
    (if (zp n)
        1
      (+ (numbertheory-aneqprodakp4-prefix-product (- n 1))
         4))))

(defun numbertheory-aneqprodakp4-anmsqrtanp1eq2-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (let ((a-n (numbertheory-aneqprodakp4-sequence n))
         (a-next (numbertheory-aneqprodakp4-sequence (+ n 1))))
     (and (<= 2 a-n)
          (equal a-next
                 (* (- a-n 2)
                    (- a-n 2)))))))

(value-triple :itpeval-statement-checked)
:q
