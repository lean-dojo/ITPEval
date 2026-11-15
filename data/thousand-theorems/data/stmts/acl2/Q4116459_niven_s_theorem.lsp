;; Statement-only formalization of thousand-theorems corpus artifact Q4116459,
;; "Niven's theorem": the only rational cosine values at rational multiples
;; of pi are -1, -1/2, 0, 1/2, and 1. This file contains no proof.

(in-package "ACL2")

;; For rational q, existence of a rational r with q = cos(pi*r) is
;; bidirectionally equivalent to the internal existence of a positive integer
;; n such that T_n(q) is 1 or -1. Forward, write r = a/n and use
;; T_n(cos(pi*a/n)) = cos(pi*a). Conversely, every real root of
;; T_n(x) = +/-1 is cos(pi*a/n) for an integer a. Thus the predicate below
;; preserves exactly the source hypotheses on theta and its rational cosine.

(defun q4116459-chebyshev-t (n x)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) 1)
   ((equal n 1) x)
   (t
    (-
     (* (* 2 x)
        (q4116459-chebyshev-t (- n 1) x))
     (q4116459-chebyshev-t (- n 2) x)))))

(defun-sk q4116459-rational-cosine-at-rational-multiple-p (q)
  (exists (n)
    (and
     (posp n)
     (or
      (equal (q4116459-chebyshev-t n q) 1)
      (equal (q4116459-chebyshev-t n q) -1)))))

(defun thousand-theorems-q4116459-niven-s-theorem-statement (q)
  (implies
   (and
    (rationalp q)
    (q4116459-rational-cosine-at-rational-multiple-p q))
   (or
    (equal q -1)
    (equal q -1/2)
    (equal q 0)
    (equal q 1/2)
    (equal q 1))))

(value-triple :itpeval-statement-checked)
:q
