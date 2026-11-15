;; Statement-only formalization of PutnamBench corpus artifact putnam_1986_b4:
;; asymptotic approximation of large real numbers by square roots of integers
;; of the form m^2 + 2*n^2. This file contains no proof.

(in-package "ACL2")

;; The inequalities below are equivalent to
;;
;;   |R - sqrt(M^2 + 2*N^2)| < EPSILON.
;;
;; Splitting at R-EPSILON avoids introducing a square-root function into
;; ordinary ACL2. The radicand is nonnegative because M and N are integers.
(defun putnam-1986-b4-close-square-p (r epsilon m n)
  (let* ((lower (- r epsilon))
         (upper (+ r epsilon))
         (radicand (+ (* m m) (* 2 n n))))
    (and
     (rationalp r)
     (rationalp epsilon)
     (< 0 epsilon)
     (integerp m)
     (integerp n)
     (< 0 upper)
     (or (< lower 0)
         (< (* lower lower) radicand))
     (< radicand (* upper upper)))))

(defun-sk putnam-1986-b4-close-value-exists-p (r epsilon)
  (exists (m n)
    (putnam-1986-b4-close-square-p r epsilon m n)))

(defun-sk putnam-1986-b4-tail-p (epsilon threshold)
  (forall (r)
    (implies
     (and (rationalp r)
          (<= threshold r))
     (putnam-1986-b4-close-value-exists-p r epsilon))))

(defun-sk putnam-1986-b4-epsilon-tail-exists-p (epsilon)
  (exists (threshold)
    (and (rationalp threshold)
         (putnam-1986-b4-tail-p epsilon threshold))))

;; For each fixed real R, the source minimum exists and is less than EPSILON
;; exactly when the existential predicate above holds. Positive rational
;; tolerances are cofinal in the positive reals. Rational R are dense, and
;; distance to a fixed set is 1-Lipschitz, so this rational epsilon-tail
;; statement is equivalent to Tendsto G atTop (nhds 0). In particular, no
;; convergence threshold is supplied by the statement.
(defun-sk putnambench-putnam-1986-b4-statement ()
  (forall (epsilon)
    (implies
     (and (rationalp epsilon)
          (< 0 epsilon))
     (putnam-1986-b4-epsilon-tail-exists-p epsilon))))

(value-triple :itpeval-statement-checked)
:q
