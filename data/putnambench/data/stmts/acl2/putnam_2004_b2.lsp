;; Statement-only formalization of PutnamBench corpus artifact putnam_2004_b2:
;; for positive natural numbers m and n, the factorial-to-power ratio at
;; m+n is strictly less than the product of the ratios at m and n. This file
;; contains no proof.

(in-package "ACL2")

(defun putnam-2004-b2-factorial (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (* k
       (putnam-2004-b2-factorial (- k 1)))))

;; Under the hypotheses, all powers in the denominators are positive
;; integers. ACL2 therefore computes the displayed ratios as exact rationals,
;; whose strict order agrees with their embeddings into the source reals.
(defun putnambench-putnam-2004-b2-statement (m n)
  (implies
   (and (natp m)
        (< 0 m)
        (natp n)
        (< 0 n))
   (< (/ (putnam-2004-b2-factorial (+ m n))
         (expt (+ m n) (+ m n)))
      (* (/ (putnam-2004-b2-factorial m)
            (expt m m))
         (/ (putnam-2004-b2-factorial n)
            (expt n n))))))

(value-triple :itpeval-statement-checked)
:q
