;; Statement-only formalization of PutnamBench corpus artifact putnam_1984_b1:
;; the factorial partial sums satisfy a recurrence with the polynomials
;; P(x) = x + 3 and Q(x) = -x - 2. This file contains no proof.

(in-package "ACL2")

(defun putnam-1984-b1-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      1
    (* n
       (putnam-1984-b1-factorial (- n 1)))))

(defun putnam-1984-b1-factorial-sum (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (zp n))
      0
    (+ (putnam-1984-b1-factorial n)
       (putnam-1984-b1-factorial-sum (- n 1)))))

;; These are the evaluations of the source solution polynomials
;; P(x) = x + 3 and Q(x) = -x - 2.
(defun putnam-1984-b1-p (x)
  (+ x 3))

(defun putnam-1984-b1-q (x)
  (- (+ x 2)))

;; The source hypothesis determines f(n) as the factorial sum at every
;; positive natural n, including all three indices in the conclusion.
;; Substituting that definition is therefore bidirectionally equivalent to
;; the source implication for arbitrary such f. The polynomial evaluations
;; and sums are integers, so their equality here is also equivalent to the
;; source equality after embedding those integers into the reals.
(defun putnambench-putnam-1984-b1-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (equal
    (putnam-1984-b1-factorial-sum (+ n 2))
    (+ (* (putnam-1984-b1-p n)
          (putnam-1984-b1-factorial-sum (+ n 1)))
       (* (putnam-1984-b1-q n)
          (putnam-1984-b1-factorial-sum n))))))

(value-triple :itpeval-statement-checked)
:q
