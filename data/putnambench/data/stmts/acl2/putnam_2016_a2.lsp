;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_a2:
;; the greatest positive integer satisfying a binomial inequality, divided by
;; its index, converges to (3 + sqrt(5)) / 2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Pascal recursion gives the natural-number binomial coefficients used in the
;; source. DEFUN-SK keeps the greatest-value, cutoff, and tail quantifiers
;; internal to the statement.

(defun putnam-2016-a2-binomial (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (putnam-2016-a2-binomial (- n 1) k)
       (putnam-2016-a2-binomial
        (- n 1) (- k 1)))))

(defun putnam-2016-a2-qualifies-p (n m)
  (and
   (posp n)
   (posp m)
   (<
    (putnam-2016-a2-binomial (- m 1) n)
    (putnam-2016-a2-binomial m (- n 1)))))

(defun-sk putnam-2016-a2-upper-bound-p (n m)
  (forall (candidate)
    (implies
     (and
      (natp candidate)
      (putnam-2016-a2-qualifies-p n candidate))
     (<= candidate m))))

(defun putnam-2016-a2-greatest-p (n m)
  (and
   (natp m)
   (putnam-2016-a2-qualifies-p n m)
   (putnam-2016-a2-upper-bound-p n m)))

(defun-sk putnam-2016-a2-greatest-exists-at-p (n)
  (exists (m)
    (putnam-2016-a2-greatest-p n m)))

(defun-sk putnam-2016-a2-greatest-values-exist-p ()
  (forall (n)
    (implies
     (posp n)
     (putnam-2016-a2-greatest-exists-at-p n))))

;; ACL2 numbers do not contain irrational reals. For rational x, comparison
;; with alpha = (3 + sqrt(5))/2 is represented exactly using
;; q(x) = x^2 - 3*x + 1:
;;
;;   alpha < x  iff  3/2 < x and 0 < q(x),
;;   x < alpha  iff  x < 3/2 or q(x) < 0.
;;
;; Since every M(n)/n is rational and positive rationals are cofinal among
;; positive real tolerances, quantifying over positive rational epsilon is
;; equivalent to the source real epsilon definition of convergence.

(defun putnam-2016-a2-root-polynomial (x)
  (+ (* x x)
     (- (* 3 x))
     1))

(defun putnam-2016-a2-solution-less-than-p (x)
  (and
   (rationalp x)
   (< 3/2 x)
   (< 0 (putnam-2016-a2-root-polynomial x))))

(defun putnam-2016-a2-less-than-solution-p (x)
  (and
   (rationalp x)
   (or
    (< x 3/2)
    (< (putnam-2016-a2-root-polynomial x) 0))))

(defun putnam-2016-a2-within-solution-p (x epsilon)
  (and
   (rationalp x)
   (rationalp epsilon)
   (< 0 epsilon)
   (putnam-2016-a2-solution-less-than-p
    (+ x epsilon))
   (putnam-2016-a2-less-than-solution-p
    (- x epsilon))))

(defun-sk putnam-2016-a2-limit-tail-p (epsilon cutoff)
  (forall (n m)
    (implies
     (and
      (posp n)
      (natp m)
      (<= cutoff n)
      (putnam-2016-a2-greatest-p n m))
     (putnam-2016-a2-within-solution-p
      (/ m n)
      epsilon))))

(defun-sk putnam-2016-a2-cutoff-exists-p (epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2016-a2-limit-tail-p
      epsilon cutoff))))

(defun-sk putnam-2016-a2-converges-p ()
  (forall (epsilon)
    (implies
     (and
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-2016-a2-cutoff-exists-p epsilon))))

(defun putnambench-putnam-2016-a2-statement ()
  (implies
   (putnam-2016-a2-greatest-values-exist-p)
   (putnam-2016-a2-converges-p)))

(value-triple :itpeval-statement-checked)
:q
