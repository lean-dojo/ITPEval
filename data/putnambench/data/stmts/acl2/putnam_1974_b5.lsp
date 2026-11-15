;; Statement-only formalization of PutnamBench corpus artifact putnam_1974_b5:
;; the finite exponential-series sum through degree n is greater than half
;; of exp(n) for every natural n. This file contains no proof.

(in-package "ACL2")

;; For natural n, put S_n = sum_(i=0)^n n^i/i!.  The exact rational prefixes
;; below increase to the real number exp(n).  Thus the source inequality
;; exp(n) < 2*S_n implies that every prefix is below 2*S_n.
;;
;; Conversely, if every prefix is below 2*S_n, passage to the limit gives
;; exp(n) <= 2*S_n.  For n > 0, exp(n) is transcendental while 2*S_n is
;; rational, so equality is impossible; for n = 0, exp(0) = 1 < 2*S_0 = 2.
;; Hence universal closure over TERM-COUNT is bidirectionally equivalent to
;; the source strict real inequality, without replacing exp(n) by a rational
;; value or restricting the natural-number domain.

(defun putnam-1974-b5-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1974-b5-factorial (- n 1)))))

(defun putnam-1974-b5-exp-prefix (n term-count)
  (declare (xargs :measure (nfix term-count)))
  (if (zp term-count)
      0
    (let ((index (- term-count 1)))
      (+ (putnam-1974-b5-exp-prefix n index)
         (/ (expt n index)
            (putnam-1974-b5-factorial index))))))

(defun putnam-1974-b5-finite-sum (n)
  (putnam-1974-b5-exp-prefix n (+ n 1)))

(defun putnambench-putnam-1974-b5-statement (n term-count)
  (implies
   (and (natp n)
        (natp term-count))
   (< (putnam-1974-b5-exp-prefix n term-count)
      (* 2 (putnam-1974-b5-finite-sum n)))))

(value-triple :itpeval-statement-checked)
:q
