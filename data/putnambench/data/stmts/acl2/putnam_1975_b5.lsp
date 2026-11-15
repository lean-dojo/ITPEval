;; Statement-only formalization of PutnamBench corpus artifact putnam_1975_b5:
;; for f_0(x) = exp(x) and f_(n+1)(x) = x*f_n'(x), the real series
;; sum f_n(1)/n! converges to exp(exp(1)). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive complete-real sort.  These conservative
;; interfaces present an arbitrary Archimedean ordered field, its exponential,
;; the source function sequence, and its totalized derivative.  Every
;; algebraic and analytic property used by the statement remains an explicit
;; hypothesis below.

(defstub p1975b5-scalar-p (x) t)
(defstub p1975b5-add-op (x y) t)
(defstub p1975b5-multiply-op (x y) t)
(defstub p1975b5-negate-op (x) t)
(defstub p1975b5-inverse-op (x) t)
(defstub p1975b5-less-op (x y) t)
(defstub p1975b5-exp-op (x) t)
(defstub p1975b5-f (n x) t)
(defstub p1975b5-deriv (n x) t)

(defun p1975b5-add (x y)
  (p1975b5-add-op x y))

(defun p1975b5-mul (x y)
  (p1975b5-multiply-op x y))

(defun p1975b5-neg (x)
  (p1975b5-negate-op x))

(defun p1975b5-inv (x)
  (p1975b5-inverse-op x))

(defun p1975b5-sub (x y)
  (p1975b5-add x (p1975b5-neg y)))

(defun p1975b5-div (x y)
  (p1975b5-mul x (p1975b5-inv y)))

(defun p1975b5-less (x y)
  (if (p1975b5-less-op x y) t nil))

(defun p1975b5-abs (x zero)
  (if (p1975b5-less x zero)
      (p1975b5-neg x)
    x))

(defun-sk p1975b5-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (p1975b5-scalar-p x)
      (p1975b5-scalar-p y)
      (p1975b5-scalar-p z))
     (and
      (p1975b5-scalar-p (p1975b5-add x y))
      (p1975b5-scalar-p (p1975b5-mul x y))
      (p1975b5-scalar-p (p1975b5-neg x))
      (p1975b5-scalar-p (p1975b5-inv x))
      (equal
       (p1975b5-add (p1975b5-add x y) z)
       (p1975b5-add x (p1975b5-add y z)))
      (equal (p1975b5-add x y)
             (p1975b5-add y x))
      (equal (p1975b5-add x zero) x)
      (equal (p1975b5-add x (p1975b5-neg x))
             zero)
      (equal
       (p1975b5-mul (p1975b5-mul x y) z)
       (p1975b5-mul x (p1975b5-mul y z)))
      (equal (p1975b5-mul x y)
             (p1975b5-mul y x))
      (equal (p1975b5-mul x one) x)
      (implies
       (equal x zero)
       (equal (p1975b5-inv x) zero))
      (implies
       (not (equal x zero))
       (equal (p1975b5-mul x (p1975b5-inv x))
              one))
      (equal
       (p1975b5-mul x (p1975b5-add y z))
       (p1975b5-add
        (p1975b5-mul x y)
        (p1975b5-mul x z)))))))

(defun-sk p1975b5-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (p1975b5-scalar-p x)
      (p1975b5-scalar-p y)
      (p1975b5-scalar-p z))
     (and
      (not (p1975b5-less x x))
      (or
       (equal x y)
       (p1975b5-less x y)
       (p1975b5-less y x))
      (implies
       (and
        (p1975b5-less x y)
        (p1975b5-less y z))
       (p1975b5-less x z))
      (implies
       (p1975b5-less x y)
       (p1975b5-less
        (p1975b5-add x z)
        (p1975b5-add y z)))
      (implies
       (and
        (p1975b5-less zero x)
        (p1975b5-less zero y))
       (p1975b5-less
        zero (p1975b5-mul x y)))))))

(defun p1975b5-r-nat (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (p1975b5-add
     one
     (p1975b5-r-nat (- n 1) zero one))))

(defun-sk p1975b5-archimedean-bound-exists-p
    (x zero one)
  (exists (n)
    (and
     (natp n)
     (p1975b5-less
      x (p1975b5-r-nat n zero one)))))

(defun-sk p1975b5-archimedean-p (zero one)
  (forall (x)
    (implies
     (p1975b5-scalar-p x)
     (p1975b5-archimedean-bound-exists-p
      x zero one))))

(defun p1975b5-real-field-p (zero one)
  (and
   (p1975b5-scalar-p zero)
   (p1975b5-scalar-p one)
   (not (equal zero one))
   (p1975b5-less zero one)
   (p1975b5-field-laws-p zero one)
   (p1975b5-order-laws-p zero)
   (p1975b5-archimedean-p zero one)))

;; The exponential is characterized by its full real Taylor series.

(defun p1975b5-r-power (base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (p1975b5-mul
     base
     (p1975b5-r-power base (- exponent 1) one))))

(defun p1975b5-r-factorial (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      one
    (p1975b5-mul
     (p1975b5-r-nat n zero one)
     (p1975b5-r-factorial (- n 1) zero one))))

(defun p1975b5-exp-prefix (x terms zero one)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let ((index (- terms 1)))
      (p1975b5-add
       (p1975b5-exp-prefix x index zero one)
       (p1975b5-div
        (p1975b5-r-power x index one)
        (p1975b5-r-factorial index zero one))))))

(defun-sk p1975b5-exp-tail-p
    (x epsilon cutoff zero one)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p1975b5-less
      (p1975b5-abs
       (p1975b5-sub
        (p1975b5-exp-prefix x terms zero one)
        (p1975b5-exp-op x))
       zero)
      epsilon))))

(defun-sk p1975b5-exp-cutoff-exists-p
    (x epsilon zero one)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1975b5-exp-tail-p
      x epsilon cutoff zero one))))

(defun-sk p1975b5-exp-converges-p
    (x zero one)
  (forall (epsilon)
    (implies
     (and
      (p1975b5-scalar-p epsilon)
      (p1975b5-less zero epsilon))
     (p1975b5-exp-cutoff-exists-p
      x epsilon zero one))))

(defun-sk p1975b5-exp-correct-p (zero one)
  (forall (x)
    (implies
     (p1975b5-scalar-p x)
     (and
      (p1975b5-scalar-p (p1975b5-exp-op x))
      (p1975b5-exp-converges-p x zero one)))))

;; HAS-DERIVATIVE-AT is the epsilon-remainder definition
;; |f_n(y)-f_n(x)-d*(y-x)| <= epsilon*|y-x| near x.

(defun p1975b5-derivative-error
    (n point value derivative zero)
  (p1975b5-abs
   (p1975b5-sub
    (p1975b5-sub
     (p1975b5-f n value)
     (p1975b5-f n point))
    (p1975b5-mul
     derivative
     (p1975b5-sub value point)))
   zero))

(defun-sk p1975b5-derivative-error-bound-p
    (n point derivative epsilon radius zero)
  (forall (value)
    (implies
     (and
      (p1975b5-scalar-p value)
      (p1975b5-less
       (p1975b5-abs
        (p1975b5-sub value point)
        zero)
       radius))
     (not
      (p1975b5-less
       (p1975b5-mul
        epsilon
        (p1975b5-abs
         (p1975b5-sub value point)
         zero))
       (p1975b5-derivative-error
        n point value derivative zero))))))

(defun-sk p1975b5-derivative-radius-exists-p
    (n point derivative epsilon zero)
  (exists (radius)
    (and
     (p1975b5-scalar-p radius)
     (p1975b5-less zero radius)
     (p1975b5-derivative-error-bound-p
      n point derivative epsilon radius zero))))

(defun-sk p1975b5-has-derivative-at-p
    (n point derivative zero)
  (forall (epsilon)
    (implies
     (and
      (p1975b5-scalar-p epsilon)
      (p1975b5-less zero epsilon))
     (p1975b5-derivative-radius-exists-p
      n point derivative epsilon zero))))

(defun-sk p1975b5-differentiable-at-p
    (n point zero)
  (exists (derivative)
    (and
     (p1975b5-scalar-p derivative)
     (p1975b5-has-derivative-at-p
      n point derivative zero))))

;; This matches the source libraries' totalized DERIV: the derivative where
;; it exists, and zero at a nondifferentiability point.

(defun p1975b5-deriv-value-p
    (n point value zero)
  (and
   (p1975b5-scalar-p value)
   (if (p1975b5-differentiable-at-p n point zero)
       (p1975b5-has-derivative-at-p
        n point value zero)
     (equal value zero))))

(defun-sk p1975b5-f-values-p ()
  (forall (n x)
    (implies
     (and
      (natp n)
      (p1975b5-scalar-p x))
     (p1975b5-scalar-p (p1975b5-f n x)))))

(defun-sk p1975b5-deriv-values-p (zero)
  (forall (n x)
    (implies
     (and
      (natp n)
      (p1975b5-scalar-p x))
     (p1975b5-deriv-value-p
      n x (p1975b5-deriv n x) zero))))

(defun-sk p1975b5-initial-condition-p ()
  (forall (x)
    (implies
     (p1975b5-scalar-p x)
     (equal
      (p1975b5-f 0 x)
      (p1975b5-exp-op x)))))

(defun-sk p1975b5-recurrence-p ()
  (forall (n x)
    (implies
     (and
      (natp n)
      (p1975b5-scalar-p x))
     (equal
      (p1975b5-f (+ n 1) x)
      (p1975b5-mul
       x
       (p1975b5-deriv n x))))))

;; The conclusion is the source infinite sum itself, expressed by its
;; unbounded epsilon-N convergence predicate.

(defun p1975b5-series-prefix
    (terms zero one)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let ((index (- terms 1)))
      (p1975b5-add
       (p1975b5-series-prefix index zero one)
       (p1975b5-div
        (p1975b5-f index one)
        (p1975b5-r-factorial index zero one))))))

(defun p1975b5-target (one)
  (p1975b5-exp-op (p1975b5-exp-op one)))

(defun-sk p1975b5-series-tail-p
    (epsilon cutoff zero one)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p1975b5-less
      (p1975b5-abs
       (p1975b5-sub
        (p1975b5-series-prefix terms zero one)
        (p1975b5-target one))
       zero)
      epsilon))))

(defun-sk p1975b5-series-cutoff-exists-p
    (epsilon zero one)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p1975b5-series-tail-p
      epsilon cutoff zero one))))

(defun-sk p1975b5-series-converges-p
    (zero one)
  (forall (epsilon)
    (implies
     (and
      (p1975b5-scalar-p epsilon)
      (p1975b5-less zero epsilon))
     (p1975b5-series-cutoff-exists-p
      epsilon zero one))))

(defun putnambench-putnam-1975-b5-statement
    (zero one)
  (implies
   (and
    (p1975b5-real-field-p zero one)
    (p1975b5-exp-correct-p zero one)
    (p1975b5-f-values-p)
    (p1975b5-deriv-values-p zero)
    (p1975b5-initial-condition-p)
    (p1975b5-recurrence-p))
   (p1975b5-series-converges-p zero one)))

(value-triple :itpeval-statement-checked)
:q
