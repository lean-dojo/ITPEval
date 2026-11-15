;; Statement-only formalization of PutnamBench corpus artifact putnam_1987_b2:
;; for natural r, s, and t with r+s <= t, the finite sum of ratios of
;; binomial coefficients has the stated rational closed form. This file
;; contains no proof.

(in-package "ACL2")

;; Pascal recursion represents the natural-number binomial coefficient.
(defun putnam-1987-b2-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-1987-b2-binomial-coefficient (- n 1) k)
       (putnam-1987-b2-binomial-coefficient
        (- n 1) (- k 1)))))

;; This inclusive recursion enumerates i = 0 through upper. Under the
;; statement hypotheses and upper <= s, r+i <= t, so every denominator is a
;; positive binomial coefficient and ACL2 division is exact rational division.
(defun putnam-1987-b2-sum-through (r s total upper)
  (declare (xargs :measure (nfix upper)))
  (let ((term
         (/ (putnam-1987-b2-binomial-coefficient s upper)
            (putnam-1987-b2-binomial-coefficient
             total (+ r upper)))))
    (if (zp upper)
        term
      (+ (putnam-1987-b2-sum-through
          r s total (- upper 1))
         term))))

(defun putnambench-putnam-1987-b2-statement (r s total)
  (implies
   (and (natp r)
        (natp s)
        (natp total)
        (<= (+ r s) total))
   (equal
    (putnam-1987-b2-sum-through r s total s)
    (/ (+ total 1)
       (* (nfix (- (+ total 1) s))
          (putnam-1987-b2-binomial-coefficient
           (nfix (- total s))
           r))))))

(value-triple :itpeval-statement-checked)
:q
