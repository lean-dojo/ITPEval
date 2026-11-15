;; Statement-only formalization of thousand-theorems corpus artifact Q834025,
;; "Cauchy integral theorem": the Cauchy integral formula for a complex-valued
;; function continuous on a closed disc and complex differentiable in its
;; interior away from a countable set. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A Dedekind-complete Archimedean ordered field presentation of the real
;; numbers. Sets used by the completeness predicate remain arbitrary and
;; potentially infinite ACL2 objects.

(defstub q834025-r-member-p (real value) t)
(defstub q834025-r-zero (real) t)
(defstub q834025-r-one (real) t)
(defstub q834025-r-add (real left right) t)
(defstub q834025-r-multiply (real left right) t)
(defstub q834025-r-negate (real value) t)
(defstub q834025-r-inverse (real value) t)
(defstub q834025-r-less (real left right) t)
(defstub q834025-r-set-member-p (real set value) t)

(defun q834025-r-subtract (real left right)
  (q834025-r-add
   real left (q834025-r-negate real right)))

(defun q834025-r-leq (real left right)
  (not (q834025-r-less real right left)))

(defun q834025-r-positive-p (real value)
  (and
   (q834025-r-member-p real value)
   (q834025-r-less
    real (q834025-r-zero real) value)))

(defun q834025-r-abs (real value)
  (if (q834025-r-less
       real value (q834025-r-zero real))
      (q834025-r-negate real value)
    value))

(defun q834025-r-natural (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q834025-r-zero real)
    (q834025-r-add
     real
     (q834025-r-one real)
     (q834025-r-natural real (- n 1)))))

(defun q834025-r-power (real value n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q834025-r-one real)
    (q834025-r-multiply
     real value
     (q834025-r-power real value (- n 1)))))

(defun q834025-r-factorial (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q834025-r-one real)
    (q834025-r-multiply
     real
     (q834025-r-natural real n)
     (q834025-r-factorial real (- n 1)))))

(defun-sk q834025-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q834025-r-member-p real x)
      (q834025-r-member-p real y)
      (q834025-r-member-p real z))
     (let* ((zero (q834025-r-zero real))
            (one (q834025-r-one real))
            (xy-add (q834025-r-add real x y))
            (yz-add (q834025-r-add real y z))
            (xy-mul (q834025-r-multiply real x y))
            (yz-mul (q834025-r-multiply real y z))
            (neg-x (q834025-r-negate real x))
            (inv-x (q834025-r-inverse real x)))
       (and
        (q834025-r-member-p real xy-add)
        (q834025-r-member-p real xy-mul)
        (q834025-r-member-p real neg-x)
        (q834025-r-member-p real inv-x)
        (equal
         (q834025-r-add real xy-add z)
         (q834025-r-add real x yz-add))
        (equal xy-add (q834025-r-add real y x))
        (equal (q834025-r-add real x zero) x)
        (equal (q834025-r-add real x neg-x) zero)
        (equal
         (q834025-r-multiply real xy-mul z)
         (q834025-r-multiply real x yz-mul))
        (equal xy-mul (q834025-r-multiply real y x))
        (equal (q834025-r-multiply real x one) x)
        (equal (q834025-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q834025-r-multiply real x inv-x)
          one))
        (equal
         (q834025-r-multiply
          real x (q834025-r-add real y z))
         (q834025-r-add
          real
          (q834025-r-multiply real x y)
          (q834025-r-multiply real x z))))))))

(defun-sk q834025-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q834025-r-member-p real x)
      (q834025-r-member-p real y)
      (q834025-r-member-p real z))
     (let ((zero (q834025-r-zero real)))
       (and
        (not (q834025-r-less real x x))
        (or
         (equal x y)
         (q834025-r-less real x y)
         (q834025-r-less real y x))
        (implies
         (and
          (q834025-r-less real x y)
          (q834025-r-less real y z))
         (q834025-r-less real x z))
        (implies
         (q834025-r-less real x y)
         (q834025-r-less
          real
          (q834025-r-add real x z)
          (q834025-r-add real y z)))
        (implies
         (and
          (q834025-r-less real zero x)
          (q834025-r-less real zero y))
         (q834025-r-less
          real zero
          (q834025-r-multiply real x y))))))))

(defun-sk q834025-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q834025-r-member-p real x)
     (q834025-r-set-member-p real set x))))

(defun-sk q834025-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q834025-r-member-p real x)
      (q834025-r-set-member-p real set x))
     (q834025-r-leq real x bound))))

(defun-sk q834025-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q834025-r-member-p real bound)
     (q834025-r-upper-bound-p real set bound))))

(defun-sk q834025-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q834025-r-member-p real supremum)
     (q834025-r-upper-bound-p real set supremum)
     (implies
      (and
       (q834025-r-member-p real bound)
       (q834025-r-upper-bound-p real set bound))
      (q834025-r-leq real supremum bound)))))

(defun-sk q834025-r-has-supremum-p (real set)
  (exists (supremum)
    (q834025-r-supremum-p real set supremum)))

(defun-sk q834025-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q834025-r-set-nonempty-p real set)
      (q834025-r-bounded-above-p real set))
     (q834025-r-has-supremum-p real set))))

(defun-sk q834025-r-archimedean-bound-exists-p
    (real x)
  (exists (n)
    (and
     (natp n)
     (q834025-r-less
      real x (q834025-r-natural real n)))))

(defun-sk q834025-r-archimedean-p (real)
  (forall (x)
    (implies
     (q834025-r-member-p real x)
     (q834025-r-archimedean-bound-exists-p
      real x))))

(defun q834025-real-field-p (real)
  (let ((zero (q834025-r-zero real))
        (one (q834025-r-one real)))
    (and
     (q834025-r-member-p real zero)
     (q834025-r-member-p real one)
     (not (equal zero one))
     (q834025-r-field-laws-p real)
     (q834025-r-order-laws-p real)
     (q834025-r-less real zero one)
     (q834025-r-dedekind-complete-p real)
     (q834025-r-archimedean-p real))))

;; The nonnegative square root and complex numbers as real/imaginary pairs.

(defstub q834025-r-square-root (real square-root value) t)

(defun-sk q834025-r-square-root-laws-p
    (real square-root)
  (forall (x)
    (implies
     (and
      (q834025-r-member-p real x)
      (q834025-r-leq
       real (q834025-r-zero real) x))
     (let ((root
            (q834025-r-square-root
             real square-root x)))
       (and
        (q834025-r-member-p real root)
        (q834025-r-leq
         real (q834025-r-zero real) root)
        (equal
         (q834025-r-multiply real root root)
         x))))))

(defun q834025-complex-p (real value)
  (and
   (consp value)
   (q834025-r-member-p real (car value))
   (q834025-r-member-p real (cdr value))))

(defun q834025-c-zero (real)
  (cons
   (q834025-r-zero real)
   (q834025-r-zero real)))

(defun q834025-c-one (real)
  (cons
   (q834025-r-one real)
   (q834025-r-zero real)))

(defun q834025-c-i (real)
  (cons
   (q834025-r-zero real)
   (q834025-r-one real)))

(defun q834025-c-of-real (real value)
  (cons value (q834025-r-zero real)))

(defun q834025-c-add (real left right)
  (cons
   (q834025-r-add real (car left) (car right))
   (q834025-r-add real (cdr left) (cdr right))))

(defun q834025-c-negate (real value)
  (cons
   (q834025-r-negate real (car value))
   (q834025-r-negate real (cdr value))))

(defun q834025-c-subtract (real left right)
  (q834025-c-add
   real left (q834025-c-negate real right)))

(defun q834025-c-multiply (real left right)
  (cons
   (q834025-r-subtract
    real
    (q834025-r-multiply
     real (car left) (car right))
    (q834025-r-multiply
     real (cdr left) (cdr right)))
   (q834025-r-add
    real
    (q834025-r-multiply
     real (car left) (cdr right))
    (q834025-r-multiply
     real (cdr left) (car right)))))

(defun q834025-c-norm-square (real value)
  (q834025-r-add
   real
   (q834025-r-multiply
    real (car value) (car value))
   (q834025-r-multiply
    real (cdr value) (cdr value))))

(defun q834025-c-norm (real square-root value)
  (q834025-r-square-root
   real square-root
   (q834025-c-norm-square real value)))

(defun q834025-c-inverse (real value)
  (let ((denominator
         (q834025-c-norm-square real value)))
    (cons
     (q834025-r-multiply
      real
      (car value)
      (q834025-r-inverse real denominator))
     (q834025-r-multiply
      real
      (q834025-r-negate real (cdr value))
      (q834025-r-inverse real denominator)))))

(defun q834025-c-divide (real numerator denominator)
  (q834025-c-multiply
   real numerator
   (q834025-c-inverse real denominator)))

(defun q834025-c-distance
    (real square-root left right)
  (q834025-c-norm
   real square-root
   (q834025-c-subtract real left right)))

(defun q834025-open-ball-member-p
    (real square-root center radius value)
  (and
   (q834025-complex-p real value)
   (q834025-r-less
    real
    (q834025-c-distance
     real square-root value center)
    radius)))

(defun q834025-closed-ball-member-p
    (real square-root center radius value)
  (and
   (q834025-complex-p real value)
   (q834025-r-leq
    real
    (q834025-c-distance
     real square-root value center)
    radius)))

;; Arbitrary complex-valued functions and arbitrary subsets of C.

(defstub q834025-function-value (function argument) t)
(defstub q834025-set-member-p (set value) t)
(defstub q834025-enumerator-value (enumerator index) t)

(defun-sk q834025-function-typed-p (real function)
  (forall (z)
    (implies
     (q834025-complex-p real z)
     (q834025-complex-p
      real (q834025-function-value function z)))))

(defun-sk q834025-enumerator-typed-p
    (real enumerator)
  (forall (n)
    (implies
     (natp n)
     (q834025-complex-p
      real
      (q834025-enumerator-value enumerator n)))))

(defun-sk q834025-enumerator-index-exists-p
    (enumerator z)
  (exists (n)
    (and
     (natp n)
     (equal
      (q834025-enumerator-value enumerator n)
      z))))

(defun-sk q834025-enumerator-covers-p
    (set enumerator)
  (forall (z)
    (implies
     (q834025-set-member-p set z)
     (q834025-enumerator-index-exists-p
      enumerator z))))

(defun-sk q834025-countable-set-p (real set)
  (exists (enumerator)
    (and
     (q834025-enumerator-typed-p real enumerator)
     (q834025-enumerator-covers-p set enumerator))))

;; Continuity on the closed ball, with the subspace quantifier preserved.

(defun-sk q834025-continuity-delta-p
    (real square-root function center radius point epsilon delta)
  (forall (z)
    (implies
     (and
      (q834025-closed-ball-member-p
       real square-root center radius z)
      (q834025-r-less
       real
       (q834025-c-distance
        real square-root z point)
       delta))
     (q834025-r-less
      real
      (q834025-c-distance
       real square-root
       (q834025-function-value function z)
       (q834025-function-value function point))
      epsilon))))

(defun-sk q834025-continuity-delta-exists-p
    (real square-root function center radius point epsilon)
  (exists (delta)
    (and
     (q834025-r-positive-p real delta)
     (q834025-continuity-delta-p
      real square-root function center radius
      point epsilon delta))))

(defun-sk q834025-continuous-within-at-p
    (real square-root function center radius point)
  (forall (epsilon)
    (implies
     (q834025-r-positive-p real epsilon)
     (q834025-continuity-delta-exists-p
      real square-root function center radius
      point epsilon))))

(defun-sk q834025-continuous-on-closed-ball-p
    (real square-root function center radius)
  (forall (point)
    (implies
     (q834025-closed-ball-member-p
      real square-root center radius point)
     (q834025-continuous-within-at-p
      real square-root function center radius point))))

;; Complex Frechet differentiability at a point. For C -> C, every
;; complex-linear derivative is multiplication by one complex number.

(defun-sk q834025-derivative-radius-p
    (real square-root function point derivative epsilon radius)
  (forall (z)
    (implies
     (and
      (q834025-complex-p real z)
      (q834025-r-less
       real
       (q834025-c-distance
        real square-root z point)
       radius))
     (let* ((increment
             (q834025-c-subtract real z point))
            (remainder
             (q834025-c-subtract
              real
              (q834025-c-subtract
               real
               (q834025-function-value function z)
               (q834025-function-value function point))
              (q834025-c-multiply
               real derivative increment))))
       (q834025-r-leq
        real
        (q834025-c-norm
         real square-root remainder)
        (q834025-r-multiply
         real epsilon
         (q834025-c-norm
          real square-root increment)))))))

(defun-sk q834025-derivative-radius-exists-p
    (real square-root function point derivative epsilon)
  (exists (radius)
    (and
     (q834025-r-positive-p real radius)
     (q834025-derivative-radius-p
      real square-root function point derivative
      epsilon radius))))

(defun-sk q834025-has-derivative-at-p
    (real square-root function point derivative)
  (forall (epsilon)
    (implies
     (q834025-r-positive-p real epsilon)
     (q834025-derivative-radius-exists-p
      real square-root function point derivative epsilon))))

(defun-sk q834025-differentiable-at-p
    (real square-root function point)
  (exists (derivative)
    (and
     (q834025-complex-p real derivative)
     (q834025-has-derivative-at-p
      real square-root function point derivative))))

(defun-sk q834025-differentiable-off-countable-p
    (real square-root function center radius set)
  (forall (z)
    (implies
     (and
      (q834025-open-ball-member-p
       real square-root center radius z)
      (not (q834025-set-member-p set z)))
     (q834025-differentiable-at-p
      real square-root function z))))

;; Sine and cosine are characterized by their full real power-series limits.
;; Pi is the least positive zero of sine and has cosine -1 there.

(defstub q834025-r-sine (trigonometry value) t)
(defstub q834025-r-cosine (trigonometry value) t)

(defun q834025-r-sine-term (real value k)
  (let* ((degree (+ (* 2 (nfix k)) 1))
         (unsigned
          (q834025-r-multiply
           real
           (q834025-r-power real value degree)
           (q834025-r-inverse
            real
            (q834025-r-factorial real degree)))))
    (if (evenp k)
        unsigned
      (q834025-r-negate real unsigned))))

(defun q834025-r-cosine-term (real value k)
  (let* ((degree (* 2 (nfix k)))
         (unsigned
          (q834025-r-multiply
           real
           (q834025-r-power real value degree)
           (q834025-r-inverse
            real
            (q834025-r-factorial real degree)))))
    (if (evenp k)
        unsigned
      (q834025-r-negate real unsigned))))

(defun q834025-r-sine-partial-sum (real value terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (q834025-r-zero real)
    (q834025-r-add
     real
     (q834025-r-sine-partial-sum
      real value (- terms 1))
     (q834025-r-sine-term
      real value (- terms 1)))))

(defun q834025-r-cosine-partial-sum (real value terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (q834025-r-zero real)
    (q834025-r-add
     real
     (q834025-r-cosine-partial-sum
      real value (- terms 1))
     (q834025-r-cosine-term
      real value (- terms 1)))))

(defun-sk q834025-r-sequence-close-after-p
    (real kind value limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (q834025-r-less
      real
      (q834025-r-abs
       real
       (q834025-r-subtract
        real
        (if (equal kind 'sine)
            (q834025-r-sine-partial-sum
             real value terms)
          (q834025-r-cosine-partial-sum
           real value terms))
        limit))
      epsilon))))

(defun-sk q834025-r-series-cutoff-exists-p
    (real kind value limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q834025-r-sequence-close-after-p
      real kind value limit epsilon cutoff))))

(defun-sk q834025-r-series-limit-p
    (real kind value limit)
  (forall (epsilon)
    (implies
     (q834025-r-positive-p real epsilon)
     (q834025-r-series-cutoff-exists-p
      real kind value limit epsilon))))

(defun-sk q834025-trigonometry-laws-p
    (real trigonometry)
  (forall (value)
    (implies
     (q834025-r-member-p real value)
     (and
      (q834025-r-member-p
       real
       (q834025-r-sine trigonometry value))
      (q834025-r-member-p
       real
       (q834025-r-cosine trigonometry value))
      (q834025-r-series-limit-p
       real 'sine value
       (q834025-r-sine trigonometry value))
      (q834025-r-series-limit-p
       real 'cosine value
       (q834025-r-cosine trigonometry value))))))

(defun-sk q834025-pi-least-positive-zero-p
    (real trigonometry pi-value)
  (forall (value)
    (implies
     (and
      (q834025-r-positive-p real value)
      (q834025-r-less real value pi-value))
     (not
      (equal
       (q834025-r-sine trigonometry value)
       (q834025-r-zero real))))))

(defun q834025-pi-laws-p
    (real trigonometry pi-value)
  (and
   (q834025-r-positive-p real pi-value)
   (equal
    (q834025-r-sine trigonometry pi-value)
    (q834025-r-zero real))
   (equal
    (q834025-r-cosine trigonometry pi-value)
    (q834025-r-negate
     real (q834025-r-one real)))
   (q834025-pi-least-positive-zero-p
    real trigonometry pi-value)))

;; The standard counterclockwise circle map and its derivative.

(defun q834025-circle-point
    (real trigonometry center radius theta)
  (q834025-c-add
   real center
   (cons
    (q834025-r-multiply
     real radius
     (q834025-r-cosine trigonometry theta))
    (q834025-r-multiply
     real radius
     (q834025-r-sine trigonometry theta)))))

(defun q834025-circle-derivative
    (real trigonometry radius theta)
  (cons
   (q834025-r-negate
    real
    (q834025-r-multiply
     real radius
     (q834025-r-sine trigonometry theta)))
   (q834025-r-multiply
    real radius
    (q834025-r-cosine trigonometry theta))))

(defun q834025-circle-integrand
    (real trigonometry function center radius point theta)
  (let ((z
         (q834025-circle-point
          real trigonometry center radius theta)))
    (q834025-c-multiply
     real
     (q834025-c-divide
      real
      (q834025-function-value function z)
      (q834025-c-subtract real z point))
     (q834025-circle-derivative
      real trigonometry radius theta))))

;; Uniform left Riemann sums define the interval integral from 0 to 2*pi.
;; Under the statement's continuity and interior-point hypotheses, this is
;; definitionally equivalent to Mathlib's circle integral.

(defun q834025-circle-sum-aux
    (real trigonometry function center radius point
          step remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (q834025-c-zero real)
    (q834025-c-add
     real
     (q834025-circle-integrand
      real trigonometry function center radius point
      (q834025-r-multiply
       real step
       (q834025-r-natural real index)))
     (q834025-circle-sum-aux
      real trigonometry function center radius point
      step (- remaining 1) (+ index 1)))))

(defun q834025-circle-riemann-sum
    (real trigonometry pi-value function center radius point pieces)
  (let* ((two-pi
          (q834025-r-add real pi-value pi-value))
         (step
          (q834025-r-multiply
           real two-pi
           (q834025-r-inverse
            real
            (q834025-r-natural real pieces)))))
    (q834025-c-multiply
     real
     (q834025-c-of-real real step)
     (q834025-circle-sum-aux
      real trigonometry function center radius point
      step pieces 0))))

(defun-sk q834025-circle-integral-close-after-p
    (real square-root trigonometry pi-value function
          center radius point value epsilon cutoff)
  (forall (pieces)
    (implies
     (and
      (natp pieces)
      (< 0 pieces)
      (natp cutoff)
      (<= cutoff pieces))
     (q834025-r-less
      real
      (q834025-c-distance
       real square-root
       (q834025-circle-riemann-sum
        real trigonometry pi-value function
        center radius point pieces)
       value)
      epsilon))))

(defun-sk q834025-circle-integral-cutoff-exists-p
    (real square-root trigonometry pi-value function
          center radius point value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (< 0 cutoff)
     (q834025-circle-integral-close-after-p
      real square-root trigonometry pi-value function
      center radius point value epsilon cutoff))))

(defun-sk q834025-circle-integral-value-p
    (real square-root trigonometry pi-value function
          center radius point value)
  (forall (epsilon)
    (implies
     (q834025-r-positive-p real epsilon)
     (q834025-circle-integral-cutoff-exists-p
      real square-root trigonometry pi-value function
      center radius point value epsilon))))

(defun q834025-cauchy-value
    (real pi-value function point)
  (q834025-c-multiply
   real
   (q834025-c-of-real
    real (q834025-r-add real pi-value pi-value))
   (q834025-c-multiply
    real
    (q834025-c-i real)
    (q834025-function-value function point))))

(defun-sk
    thousand-theorems-q834025-cauchy-integral-theorem-statement
    ()
  (forall
    (real square-root trigonometry pi-value
          function set center point radius)
    (implies
     (and
      (q834025-real-field-p real)
      (q834025-r-square-root-laws-p
       real square-root)
      (q834025-trigonometry-laws-p
       real trigonometry)
      (q834025-pi-laws-p
       real trigonometry pi-value)
      (q834025-function-typed-p real function)
      (q834025-complex-p real center)
      (q834025-complex-p real point)
      (q834025-r-member-p real radius)
      (q834025-countable-set-p real set)
      (q834025-open-ball-member-p
       real square-root center radius point)
      (q834025-continuous-on-closed-ball-p
       real square-root function center radius)
      (q834025-differentiable-off-countable-p
       real square-root function center radius set))
     (q834025-circle-integral-value-p
      real square-root trigonometry pi-value function
      center radius point
      (q834025-cauchy-value
       real pi-value function point)))))

(value-triple :itpeval-statement-checked)
:q
