;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_a3:
;; the integer parameters for which x^4-(2m+4)x^2+(m-2)^2 factors as a
;; product of two nonconstant integer-coefficient polynomials are exactly the
;; integer squares and twice the integer squares. This file contains no proof.

(in-package "ACL2")

;; For a monic quartic, any nontrivial factorization over the integers can be
;; normalized to have a monic factor of degree one or two. If
;; C=(m-2)^2 is nonzero, that factor's constant coefficient divides C and
;; therefore has absolute value at most |C|. If C=0, x is already a factor.
;;
;; For a monic quadratic factor x^2+a*x+b, coefficient comparison forces the
;; other factor to be x^2-a*x+d, where
;;   d = -(2m+4)-b+a^2,
;;   b*d = C, and a*(d-b) = 0.
;; When a is nonzero, d=b and hence
;;   a^2 = 2b+(2m+4).
;; Thus |a| <= 2|C|+|2m+4|. The searches below are consequently equivalent
;; to the source existential quantification over all nonconstant integer
;; polynomial factors; no factor coefficients are external parameters.

(defun putnam-2001-a3-integer-abs (x)
  (if (< x 0) (- x) x))

(defun putnam-2001-a3-constant (m)
  (* (- m 2) (- m 2)))

(defun putnam-2001-a3-quadratic-coefficient (m)
  (- (+ (* 2 m) 4)))

;; The condition says that x+a divides the displayed quartic. Its monic cubic
;; cofactor is forced coefficient by coefficient.
(defun putnam-2001-a3-linear-factor-p (m a)
  (let* ((q (putnam-2001-a3-quadratic-coefficient m))
         (c (putnam-2001-a3-constant m))
         (cubic-linear (+ q (* a a)))
         (cubic-constant (- (* a cubic-linear))))
    (and
     (integerp m)
     (integerp a)
     (equal (* a cubic-constant) c))))

(defun putnam-2001-a3-linear-through-index-p
    (m bound index)
  (declare (xargs :measure (nfix index)))
  (if (and (integerp m)
           (natp bound)
           (natp index))
      (or
       (putnam-2001-a3-linear-factor-p
        m (- index bound))
       (and
        (not (zp index))
        (putnam-2001-a3-linear-through-index-p
         m bound (- index 1))))
    nil))

(defun putnam-2001-a3-linear-factor-exists-p (m)
  (if (integerp m)
      (let ((bound
             (putnam-2001-a3-integer-abs
              (putnam-2001-a3-constant m))))
        (putnam-2001-a3-linear-through-index-p
         m bound (* 2 bound)))
    nil))

(defun putnam-2001-a3-quadratic-factor-p (m a b)
  (let* ((q (putnam-2001-a3-quadratic-coefficient m))
         (c (putnam-2001-a3-constant m))
         (d (+ q (- b) (* a a))))
    (and
     (integerp m)
     (integerp a)
     (integerp b)
     (equal (* b d) c)
     (equal (* a (- d b)) 0))))

(defun putnam-2001-a3-quadratic-a-through-index-p
    (m b a-bound a-index)
  (declare (xargs :measure (nfix a-index)))
  (if (and (integerp m)
           (integerp b)
           (natp a-bound)
           (natp a-index))
      (or
       (putnam-2001-a3-quadratic-factor-p
        m (- a-index a-bound) b)
       (and
        (not (zp a-index))
        (putnam-2001-a3-quadratic-a-through-index-p
         m b a-bound (- a-index 1))))
    nil))

(defun putnam-2001-a3-quadratic-b-through-index-p
    (m b-bound a-bound b-index)
  (declare (xargs :measure (nfix b-index)))
  (if (and (integerp m)
           (natp b-bound)
           (natp a-bound)
           (natp b-index))
      (or
       (putnam-2001-a3-quadratic-a-through-index-p
        m
        (- b-index b-bound)
        a-bound
        (* 2 a-bound))
       (and
        (not (zp b-index))
        (putnam-2001-a3-quadratic-b-through-index-p
         m b-bound a-bound (- b-index 1))))
    nil))

(defun putnam-2001-a3-quadratic-factor-exists-p (m)
  (if (integerp m)
      (let* ((b-bound
              (putnam-2001-a3-integer-abs
               (putnam-2001-a3-constant m)))
             (a-bound
              (+ (* 2 b-bound)
                 (putnam-2001-a3-integer-abs
                  (putnam-2001-a3-quadratic-coefficient m)))))
        (putnam-2001-a3-quadratic-b-through-index-p
         m b-bound a-bound (* 2 b-bound)))
    nil))

(defun putnam-2001-a3-factorization-exists-p (m)
  (and
   (integerp m)
   (or
    (putnam-2001-a3-linear-factor-exists-p m)
    (putnam-2001-a3-quadratic-factor-exists-p m))))

;; For nonnegative m, any integer k with k^2=m or 2*k^2=m satisfies
;; |k| <= m, including the case m=0. Hence this bounded search is exactly the
;; source existential integer witness.
(defun putnam-2001-a3-scaled-square-through-index-p
    (m scale bound index)
  (declare (xargs :measure (nfix index)))
  (if (and (integerp m)
           (posp scale)
           (natp bound)
           (natp index))
      (let ((k (- index bound)))
        (or
         (equal m (* scale k k))
         (and
          (not (zp index))
          (putnam-2001-a3-scaled-square-through-index-p
           m scale bound (- index 1)))))
    nil))

(defun putnam-2001-a3-solution-p (m)
  (and
   (integerp m)
   (<= 0 m)
   (or
    (putnam-2001-a3-scaled-square-through-index-p
     m 1 m (* 2 m))
    (putnam-2001-a3-scaled-square-through-index-p
     m 2 m (* 2 m)))))

(defun putnambench-putnam-2001-a3-statement (m)
  (implies
   (integerp m)
   (equal
    (putnam-2001-a3-factorization-exists-p m)
    (putnam-2001-a3-solution-p m))))

(value-triple :itpeval-statement-checked)
:q
