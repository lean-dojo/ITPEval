;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_b4:
;; for every Fibonacci index m greater than 2, the remainder modulo F_m of
;; the product of k^k for 1 <= k < F_m is a Fibonacci number. This file
;; contains no proof.

(in-package "ACL2")

;; The source assumptions F_0 = 0, F_1 = 1, and
;; F_(n+2) = F_(n+1) + F_n uniquely determine this function on the naturals.
(defun putnam-2021-b4-fibonacci (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (if (equal n 1)
        1
      (+ (putnam-2021-b4-fibonacci (- n 1))
         (putnam-2021-b4-fibonacci (- n 2))))))

;; This is exactly the finite product of k^k for 1 <= k <= UPPER.
(defun putnam-2021-b4-product-through (upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      1
    (* (putnam-2021-b4-product-through (- upper 1))
       (expt upper upper))))

;; Search internally for an index p from 0 through UPPER whose Fibonacci
;; value is VALUE.
(defun putnam-2021-b4-fibonacci-value-through-p
    (value upper)
  (declare (xargs :measure (nfix upper)))
  (if (zp upper)
      (equal value (putnam-2021-b4-fibonacci 0))
    (or
     (equal value
            (putnam-2021-b4-fibonacci upper))
     (putnam-2021-b4-fibonacci-value-through-p
      value (- upper 1)))))

;; ACL2 universally closes M. For m > 2, the remainder is below F_m, and
;; every Fibonacci value at an index above m is at least F_(m+1) > F_m.
;; Therefore searching p through m is bidirectionally equivalent to the
;; source existential quantifier over every natural p.
(defun putnambench-putnam-2021-b4-statement (m)
  (implies
   (and
    (natp m)
    (< 2 m))
   (let* ((f-m (putnam-2021-b4-fibonacci m))
          (remainder
           (mod
            (putnam-2021-b4-product-through (- f-m 1))
            f-m)))
     (putnam-2021-b4-fibonacci-value-through-p
      remainder m))))

(value-triple :itpeval-statement-checked)
:q
