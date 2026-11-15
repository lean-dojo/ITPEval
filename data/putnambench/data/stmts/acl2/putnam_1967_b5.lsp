;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1967_b5: for every positive natural n, the first n terms of a
;; negative-binomial expansion sum to one half. This file contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1967-b5-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1967-b5-binomial-coefficient (- n 1) k)
       (putnam-1967-b5-binomial-coefficient
        (- n 1) (- k 1)))))

;; This inclusive recursion enumerates i = 0 through upper. Under the
;; statement hypotheses, upper = n-1 and every term is the exact rational
;;
;;   choose(n+i-1,i) / 2^(n+i).
;;
;; This equals the sources' integer negative-power form. Since all terms are
;; rational, ACL2 equality is equivalent to equality of their canonical
;; images in the real and real-closed-field formulations.
(defun putnam-1967-b5-sum-through (n upper)
  (declare (xargs :measure (nfix upper)))
  (let ((term
         (/ (putnam-1967-b5-binomial-coefficient
             (- (+ n upper) 1)
             upper)
            (expt 2 (+ n upper)))))
    (if (zp upper)
        term
      (+ (putnam-1967-b5-sum-through n (- upper 1))
         term))))

(defun putnambench-putnam-1967-b5-statement (n)
  (implies
   (and (natp n)
        (< 0 n))
   (equal
    (/ 1 2)
    (putnam-1967-b5-sum-through n (- n 1)))))

(value-triple :itpeval-statement-checked)
:q
