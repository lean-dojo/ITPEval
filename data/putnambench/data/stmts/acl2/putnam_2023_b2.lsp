;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_b2:
;; the minimum number of ones in the binary representation of a positive
;; multiple of 2023 is 3. This file contains no proof.

(in-package "ACL2")

(defun putnam-2023-b2-count-ones-aux (fuel n)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      0
    (+ (mod (nfix n) 2)
       (putnam-2023-b2-count-ones-aux
        (- fuel 1)
        (floor (nfix n) 2)))))

(defun putnam-2023-b2-count-ones (n)
  (if (natp n)
      (putnam-2023-b2-count-ones-aux
       (integer-length n)
       n)
    0))

;; The closed witness satisfies
;; 2023 * 74698827212965223383 = 2^77 + 2^16 + 1.
(defun putnam-2023-b2-attainment-p ()
  (let ((witness 74698827212965223383))
    (and
     (natp witness)
     (< 0 witness)
     (equal
      (putnam-2023-b2-count-ones (* 2023 witness))
      3))))

;; N is universally closed by the ACL2 statement-corpus convention. The
;; explicit closed witness above keeps the existential attainment internal.
(defun putnambench-putnam-2023-b2-statement (n)
  (and
   (putnam-2023-b2-attainment-p)
   (implies
    (and
     (natp n)
     (< 0 n))
    (<= 3
        (putnam-2023-b2-count-ones (* 2023 n))))))

(value-triple :itpeval-statement-checked)
:q
