;; Statement-only formalization of PutnamBench corpus artifact putnam_1978_b4:
;; integer solutions of a symmetric cubic equation with all four coordinates
;; arbitrarily large. This file contains no proof.

(in-package "ACL2")

;; Quantifying over rational thresholds is equivalent to quantifying over real
;; thresholds: the forward direction is immediate, and for any real threshold
;; there is a rational threshold above it. The four integer witnesses remain
;; genuine unbounded existentials through ACL2's defun-sk mechanism.

(defun putnam-1978-b4-equation-p (a b c d)
  (and (integerp a)
       (integerp b)
       (integerp c)
       (integerp d)
       (equal (+ (* a a)
                 (* b b)
                 (* c c)
                 (* d d))
              (+ (* a b c)
                 (* a b d)
                 (* a c d)
                 (* b c d)))))

(defun-sk putnam-1978-b4-witness-exists-p (threshold)
  (exists (a b c d)
    (and (integerp a)
         (integerp b)
         (integerp c)
         (integerp d)
         (< threshold a)
         (< threshold b)
         (< threshold c)
         (< threshold d)
         (putnam-1978-b4-equation-p a b c d))))

(defun putnambench-putnam-1978-b4-statement (threshold)
  (implies
   (rationalp threshold)
   (putnam-1978-b4-witness-exists-p threshold)))

(value-triple :itpeval-statement-checked)
:q
