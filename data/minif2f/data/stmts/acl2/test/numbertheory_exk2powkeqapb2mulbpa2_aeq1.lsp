;; Statement-only formalization of miniF2F corpus artifact
;; numbertheory_exk2powkeqapb2mulbpa2_aeq1: positive natural numbers a and b
;; satisfying 2^k = (a + b^2)(b + a^2) for some positive natural k have
;; a = 1. This file contains no proof.

(in-package "ACL2")

;; If 2^k = n for positive natural k, then k <= n. Thus searching the
;; positive exponents from n down to 1 is bidirectionally equivalent to the
;; source existential quantifier, while keeping its witness internal.
(defun numbertheory-exk2powkeqapb2mulbpa2-aeq1-witness-through-p
    (n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      nil
    (or
     (equal (expt 2 k) n)
     (numbertheory-exk2powkeqapb2mulbpa2-aeq1-witness-through-p
      n
      (- k 1)))))

(defun numbertheory-exk2powkeqapb2mulbpa2-aeq1-statement (a b)
  (let ((right-hand-side
         (* (+ a (expt b 2))
            (+ b (expt a 2)))))
    (implies
     (and
      (natp a)
      (natp b)
      (< 0 a)
      (< 0 b)
      (numbertheory-exk2powkeqapb2mulbpa2-aeq1-witness-through-p
       right-hand-side
       right-hand-side))
     (equal a 1))))

(value-triple :itpeval-statement-checked)
:q
