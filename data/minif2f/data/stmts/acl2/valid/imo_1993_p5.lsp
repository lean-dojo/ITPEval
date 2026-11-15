;; Statement-only formalization of miniF2F corpus artifact imo_1993_p5:
;; there exists a strictly increasing function f on the natural numbers with
;; f(1) = 2 and f(f(n)) = f(n) + n for every natural n. This file contains no
;; proof.
;;
;; ACL2 is first-order, so the existential function is represented by the
;; closed witness f(n) = floor(phi*n + 1/2), where phi = (1+sqrt(5))/2.
;; The bounded search below is exact: k is the first natural for which
;; phi*n + 1/2 < k+1, tested by
;;   5*n^2 < (2*k+1-n)^2 and 0 < 2*k+1-n.
;; Thus no real approximation, finite table, or external function parameter is
;; introduced. The source existential is equivalent to the universally
;; quantified properties of this explicit witness.

(in-package "ACL2")

(defun imo-1993-p5-strict-upper-bound-p (n k)
  (let ((difference (- (+ (* 2 k) 1) n)))
    (and (< 0 difference)
         (< (* 5 n n)
            (* difference difference)))))

(defun imo-1993-p5-floor-phi-plus-half-search (n k fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel)
          (imo-1993-p5-strict-upper-bound-p n k))
      k
    (imo-1993-p5-floor-phi-plus-half-search
     n (+ k 1) (- fuel 1))))

(defun imo-1993-p5-f (n)
  (if (natp n)
      (imo-1993-p5-floor-phi-plus-half-search
       n 0 (+ (* 2 n) 2))
    0))

(defun imo-1993-p5-statement (n)
  (implies
   (natp n)
   (and
    (equal (imo-1993-p5-f 1) 2)
    (equal (imo-1993-p5-f (imo-1993-p5-f n))
           (+ (imo-1993-p5-f n) n))
    (< (imo-1993-p5-f n)
       (imo-1993-p5-f (+ n 1))))))

(value-triple :itpeval-statement-checked)
:q
