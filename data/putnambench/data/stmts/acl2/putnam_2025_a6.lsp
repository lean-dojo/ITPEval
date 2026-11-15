;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_a6:
;; exact 2-adic divisibility of differences formed from a recursively defined
;; integer sequence. This file contains no proof.

(in-package "ACL2")

;; On natural inputs this is exactly b_0 = 0 and
;; b_(n+1) = 2*b_n^2 + b_n + 1 from the source.
(defun putnam-2025-a6-b (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (let ((previous
           (putnam-2025-a6-b (- n 1))))
      (+ (* 2 previous previous)
         previous
         1))))

;; Both moduli are positive powers of 2, so remainder zero is equivalent to
;; integer divisibility. The second conjunct states exact nondivisibility by
;; the next power.
(defun putnambench-putnam-2025-a6-statement (k)
  (implies
   (and
    (natp k)
    (<= 1 k))
   (let* ((b-at-power
           (putnam-2025-a6-b (expt 2 k)))
          (b-at-next-power
           (putnam-2025-a6-b (expt 2 (+ k 1))))
          (difference
           (- b-at-next-power (* 2 b-at-power)))
          (lower-modulus
           (expt 2 (+ (* 2 k) 2)))
          (upper-modulus
           (expt 2 (+ (* 2 k) 3))))
     (and
      (equal (mod difference lower-modulus) 0)
      (not
       (equal (mod difference upper-modulus) 0))))))

(value-triple :itpeval-statement-checked)
:q
