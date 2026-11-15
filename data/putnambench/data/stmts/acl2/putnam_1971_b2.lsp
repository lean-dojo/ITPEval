;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_b2:
;; the unique real function on R minus {0,1} satisfying a three-cycle
;; functional equation is the specified rational function. This file contains
;; no proof.

(in-package "ACL2")

;; On S = R minus {0,1}, T(x) = (x-1)/x has order three.  Hence the source
;; predicate for a function F is, on each orbit, exactly the three equations
;;
;;   F(x)     + F(T(x))   = 1 + x,
;;   F(T(x))  + F(T^2(x)) = 1 + T(x),
;;   F(T^2(x)) + F(x)     = 1 + T^2(x).
;;
;; The source's singleton-solution assertion is therefore equivalent to the
;; conjunction below: the displayed solution satisfies the equation, and
;; every arbitrary triple satisfying the orbit equations has the displayed
;; value at x.  Conversely, any such triple extends orbitwise to a function,
;; so this local form also implies the original higher-order uniqueness claim.
;;
;; Standard ACL2 has exact rationals rather than a primitive real sort.  This
;; local rational predicate is bidirectionally equivalent to the real
;; statement, not a restriction of its generality.  After solving the three
;; linear equations, both a failure of the solution equation and a failure of
;; uniqueness are nonzero rational-function conditions in x.  Any real
;; failure away from the excluded poles persists at a nearby rational x, and
;; the corresponding three values are rational.  Every rational failure is
;; immediately a real failure.

(defun putnam-1971-b2-transform (x)
  (/ (- x 1) x))

(defun putnam-1971-b2-solution-value (x)
  (/ (- (- (expt x 3)
           (expt x 2))
        1)
     (* 2 x (- x 1))))

(defun putnambench-putnam-1971-b2-statement
    (x value-at-x value-at-tx value-at-t2x)
  (implies
   (and
    (rationalp x)
    (not (equal x 0))
    (not (equal x 1))
    (rationalp value-at-x)
    (rationalp value-at-tx)
    (rationalp value-at-t2x))
   (let* ((tx (putnam-1971-b2-transform x))
          (t2x (putnam-1971-b2-transform tx)))
     (and
      (equal
       (+ (putnam-1971-b2-solution-value x)
          (putnam-1971-b2-solution-value tx))
       (+ 1 x))
      (implies
       (and
        (equal (+ value-at-x value-at-tx)
               (+ 1 x))
        (equal (+ value-at-tx value-at-t2x)
               (+ 1 tx))
        (equal (+ value-at-t2x value-at-x)
               (+ 1 t2x)))
       (equal value-at-x
              (putnam-1971-b2-solution-value x)))))))

(value-triple :itpeval-statement-checked)
:q
