;; Statement-only formalization of PutnamBench corpus artifact putnam_1989_a2:
;; evaluation of a double real integral of the exponential of the maximum of
;; two quadratic terms over a positive rectangle. This file contains no proof.

(in-package "ACL2")

;; For nonnegative rational z, (1+z/n)^n is a rational Cauchy name for exp(z).
(defun putnam-1989-a2-exp-approx (z precision)
  (if (posp precision)
      (expt (+ 1 (/ z precision)) precision)
    0))

(defun putnam-1989-a2-max (x y)
  (if (< x y) y x))

(defun putnam-1989-a2-exponent (a b x y)
  (let ((bx (* b x))
        (ay (* a y)))
    (putnam-1989-a2-max (* bx bx) (* ay ay))))

(defun putnam-1989-a2-row-sum
    (a b x remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((y (/ (* b remaining) subdivisions)))
      (+ (putnam-1989-a2-exp-approx
          (putnam-1989-a2-exponent a b x y)
          subdivisions)
         (putnam-1989-a2-row-sum
          a b x (- remaining 1) subdivisions)))))

(defun putnam-1989-a2-double-sum
    (a b remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((x (/ (* a remaining) subdivisions)))
      (+ (putnam-1989-a2-row-sum
          a b x subdivisions subdivisions)
         (putnam-1989-a2-double-sum
          a b (- remaining 1) subdivisions)))))

;; This right grid sum uses the original source integrand on [0,a] by [0,b].
;; Both the grid and exponential precision are unbounded, so it denotes the
;; source real integral rather than a finite-table approximation.
(defun putnam-1989-a2-integral-approx (a b subdivisions)
  (if (and (rationalp a)
           (< 0 a)
           (rationalp b)
           (< 0 b)
           (posp subdivisions))
      (* (/ a subdivisions)
         (/ b subdivisions)
         (putnam-1989-a2-double-sum
          a b subdivisions subdivisions))
    0))

(defun putnam-1989-a2-solution-approx (a b precision)
  (if (and (rationalp a)
           (< 0 a)
           (rationalp b)
           (< 0 b)
           (posp precision))
      (/ (- (putnam-1989-a2-exp-approx
             (* a a b b)
             precision)
            1)
         (* a b))
    0))

;; Positive rationals are dense in the positive reals, and both sides of the
;; source equality are continuous in a and b there. Positive rational
;; tolerances are cofinal among positive real tolerances. The diagonal grid
;; and exponential approximations converge to the two source expressions.
;; Existential cutoffs state only their equality, without an added rate.
(defun-sk putnam-1989-a2-tail-p
    (a b epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (< (abs
         (- (putnam-1989-a2-integral-approx
             a b subdivisions)
            (putnam-1989-a2-solution-approx
             a b subdivisions)))
        epsilon))))

(defun-sk putnam-1989-a2-cutoff-exists-p
    (a b epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1989-a2-tail-p
      a b epsilon cutoff))))

(defun-sk putnambench-putnam-1989-a2-statement (a b)
  (forall (epsilon)
    (implies
     (and
      (rationalp a)
      (< 0 a)
      (rationalp b)
      (< 0 b)
      (rationalp epsilon)
      (< 0 epsilon))
     (putnam-1989-a2-cutoff-exists-p
      a b epsilon))))

(value-triple :itpeval-statement-checked)
:q
