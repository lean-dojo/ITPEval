;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_a2:
;; the greatest real coefficient a and least real coefficient b satisfying
;; a*x*(pi-x) <= sin(x) <= b*x*(pi-x) on [0,pi] are 1/pi and 4/pi^2.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; REAL-TYPE presents a Dedekind-complete ordered field, hence a copy of the
;; real numbers.  The conservative interfaces below supply no facts: every
;; field, order, completeness, pi, and sine property is an explicit hypothesis
;; of the final predicate.  Pi is fixed independently by Machin's arctangent
;; series, and sine is fixed by its full Taylor series.  Under the unique
;; ordered-field isomorphism with R, these characterizations preserve pi,
;; sine, the interval [0,pi], and both extremality predicates.  Thus the final
;; biconditional is bidirectionally equivalent to the source proposition.

(defstub p25a2-real-p (real-type value) t)
(defstub p25a2-zero (real-type) t)
(defstub p25a2-one (real-type) t)
(defstub p25a2-add (real-type left right) t)
(defstub p25a2-multiply (real-type left right) t)
(defstub p25a2-negate (real-type value) t)
(defstub p25a2-inverse (real-type value) t)
(defstub p25a2-less (real-type left right) t)
(defstub p25a2-pi (real-type) t)
(defstub p25a2-sine (real-type value) t)

(defstub p25a2-real-set-p (real-type set) t)
(defstub p25a2-real-set-member-p (real-type set value) t)
(defstub p25a2-supremum (real-type set) t)

(defun p25a2-leq (real-type left right)
  (not (p25a2-less real-type right left)))

(defun p25a2-positive-p (real-type value)
  (and
   (p25a2-real-p real-type value)
   (p25a2-less
    real-type (p25a2-zero real-type) value)))

(defun p25a2-subtract (real-type left right)
  (p25a2-add
   real-type left (p25a2-negate real-type right)))

(defun p25a2-divide (real-type numerator denominator)
  (p25a2-multiply
   real-type numerator (p25a2-inverse real-type denominator)))

(defun p25a2-absolute-value (real-type value)
  (if (p25a2-less
       real-type value (p25a2-zero real-type))
      (p25a2-negate real-type value)
    value))

(defun p25a2-natural (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p25a2-zero real-type)
    (p25a2-add
     real-type
     (p25a2-one real-type)
     (p25a2-natural real-type (1- n)))))

(defun p25a2-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p25a2-one real-type)
    (p25a2-multiply
     real-type
     base
     (p25a2-power real-type base (1- exponent)))))

(defun p25a2-factorial (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p25a2-one real-type)
    (p25a2-multiply
     real-type
     (p25a2-natural real-type n)
     (p25a2-factorial real-type (1- n)))))

(defun-sk p25a2-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p25a2-real-p real-type x)
      (p25a2-real-p real-type y)
      (p25a2-real-p real-type z))
     (let* ((zero (p25a2-zero real-type))
            (one (p25a2-one real-type))
            (x-plus-y (p25a2-add real-type x y))
            (y-plus-z (p25a2-add real-type y z))
            (x-times-y (p25a2-multiply real-type x y))
            (y-times-z (p25a2-multiply real-type y z))
            (negative-x (p25a2-negate real-type x))
            (inverse-x (p25a2-inverse real-type x)))
       (and
        (p25a2-real-p real-type x-plus-y)
        (p25a2-real-p real-type x-times-y)
        (p25a2-real-p real-type negative-x)
        (p25a2-real-p real-type inverse-x)
        (equal
         (p25a2-add real-type x-plus-y z)
         (p25a2-add real-type x y-plus-z))
        (equal x-plus-y (p25a2-add real-type y x))
        (equal (p25a2-add real-type x zero) x)
        (equal (p25a2-add real-type x negative-x) zero)
        (equal
         (p25a2-multiply real-type x-times-y z)
         (p25a2-multiply real-type x y-times-z))
        (equal x-times-y (p25a2-multiply real-type y x))
        (equal (p25a2-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p25a2-multiply real-type x inverse-x)
          one))
        (equal
         (p25a2-multiply real-type x y-plus-z)
         (p25a2-add
          real-type
          (p25a2-multiply real-type x y)
          (p25a2-multiply real-type x z))))))))

(defun-sk p25a2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p25a2-real-p real-type x)
      (p25a2-real-p real-type y)
      (p25a2-real-p real-type z))
     (let ((zero (p25a2-zero real-type)))
       (and
        (not (p25a2-less real-type x x))
        (or
         (p25a2-less real-type x y)
         (equal x y)
         (p25a2-less real-type y x))
        (implies
         (and
          (p25a2-less real-type x y)
          (p25a2-less real-type y z))
         (p25a2-less real-type x z))
        (implies
         (p25a2-less real-type x y)
         (p25a2-less
          real-type
          (p25a2-add real-type x z)
          (p25a2-add real-type y z)))
        (implies
         (and
          (p25a2-less real-type zero x)
          (p25a2-less real-type zero y))
         (p25a2-less
          real-type
          zero
          (p25a2-multiply real-type x y))))))))

(defun-sk p25a2-upper-bound-p
    (real-type set upper)
  (forall (x)
    (implies
     (and
      (p25a2-real-p real-type x)
      (p25a2-real-set-member-p real-type set x))
     (p25a2-leq real-type x upper))))

(defun-sk p25a2-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (p25a2-real-p real-type x)
     (p25a2-real-set-member-p real-type set x))))

(defun-sk p25a2-set-bounded-above-p
    (real-type set)
  (exists (upper)
    (and
     (p25a2-real-p real-type upper)
     (p25a2-upper-bound-p real-type set upper))))

(defun-sk p25a2-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (p25a2-real-p real-type upper)
      (p25a2-upper-bound-p real-type set upper))
     (p25a2-leq real-type supremum upper))))

(defun-sk p25a2-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (p25a2-real-set-p real-type set)
      (p25a2-set-nonempty-p real-type set)
      (p25a2-set-bounded-above-p real-type set))
     (let ((supremum (p25a2-supremum real-type set)))
       (and
        (p25a2-real-p real-type supremum)
        (p25a2-upper-bound-p real-type set supremum)
        (p25a2-least-upper-bound-p
         real-type set supremum))))))

(defun-sk p25a2-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (p25a2-less
      real-type value (p25a2-natural real-type n)))))

(defun-sk p25a2-archimedean-p (real-type)
  (forall (value)
    (implies
     (p25a2-real-p real-type value)
     (p25a2-archimedean-bound-exists-p
      real-type value))))

(defun p25a2-real-field-p (real-type)
  (let ((zero (p25a2-zero real-type))
        (one (p25a2-one real-type)))
    (and
     (p25a2-real-p real-type zero)
     (p25a2-real-p real-type one)
     (not (equal zero one))
     (p25a2-field-laws-p real-type)
     (p25a2-order-laws-p real-type)
     (p25a2-less real-type zero one)
     (p25a2-completeness-p real-type)
     (p25a2-archimedean-p real-type))))

;; Machin's identity fixes pi without referring to the theorem's inequalities:
;; pi = 16*arctan(1/5) - 4*arctan(1/239).

(defun p25a2-arctan-prefix (real-type z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p25a2-zero real-type)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned
            (p25a2-divide
             real-type
             (p25a2-power real-type z exponent)
             (p25a2-natural real-type exponent)))
           (term
            (if (equal (mod index 2) 0)
                unsigned
              (p25a2-negate real-type unsigned))))
      (p25a2-add
       real-type
       (p25a2-arctan-prefix real-type z index)
       term))))

(defun p25a2-pi-prefix (real-type terms)
  (let* ((one (p25a2-one real-type))
         (five (p25a2-natural real-type 5))
         (two-hundred-thirty-nine
          (p25a2-natural real-type 239))
         (sixteen (p25a2-natural real-type 16))
         (four (p25a2-natural real-type 4)))
    (p25a2-subtract
     real-type
     (p25a2-multiply
      real-type
      sixteen
      (p25a2-arctan-prefix
       real-type
       (p25a2-divide real-type one five)
       terms))
     (p25a2-multiply
      real-type
      four
      (p25a2-arctan-prefix
       real-type
       (p25a2-divide
        real-type one two-hundred-thirty-nine)
       terms)))))

(defun-sk p25a2-pi-tail-p
    (real-type epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p25a2-less
      real-type
      (p25a2-absolute-value
       real-type
       (p25a2-subtract
        real-type
        (p25a2-pi-prefix real-type terms)
        (p25a2-pi real-type)))
      epsilon))))

(defun-sk p25a2-pi-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p25a2-pi-tail-p
      real-type epsilon cutoff))))

(defun-sk p25a2-pi-series-p (real-type)
  (forall (epsilon)
    (implies
     (p25a2-positive-p real-type epsilon)
     (p25a2-pi-cutoff-exists-p
      real-type epsilon))))

(defun p25a2-exact-pi-p (real-type)
  (and
   (p25a2-real-p real-type (p25a2-pi real-type))
   (p25a2-positive-p real-type (p25a2-pi real-type))
   (p25a2-pi-series-p real-type)))

;; The sine interface is exactly the limit of the complete Taylor series at
;; every real argument, not a finite prefix or an error-slackened inequality.

(defun p25a2-sine-term (real-type x index)
  (let* ((exponent (+ (* 2 index) 1))
         (unsigned
          (p25a2-divide
           real-type
           (p25a2-power real-type x exponent)
           (p25a2-factorial real-type exponent))))
    (if (equal (mod index 2) 0)
        unsigned
      (p25a2-negate real-type unsigned))))

(defun p25a2-sine-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p25a2-zero real-type)
    (let ((index (1- terms)))
      (p25a2-add
       real-type
       (p25a2-sine-prefix real-type x index)
       (p25a2-sine-term real-type x index)))))

(defun-sk p25a2-sine-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p25a2-less
      real-type
      (p25a2-absolute-value
       real-type
       (p25a2-subtract
        real-type
        (p25a2-sine-prefix real-type x terms)
        (p25a2-sine real-type x)))
      epsilon))))

(defun-sk p25a2-sine-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p25a2-sine-tail-p
      real-type x epsilon cutoff))))

(defun-sk p25a2-sine-series-at-p (real-type x)
  (forall (epsilon)
    (implies
     (p25a2-positive-p real-type epsilon)
     (p25a2-sine-cutoff-exists-p
      real-type x epsilon))))

(defun-sk p25a2-exact-sine-p (real-type)
  (forall (x)
    (implies
     (p25a2-real-p real-type x)
     (and
      (p25a2-real-p
       real-type (p25a2-sine real-type x))
      (p25a2-sine-series-at-p real-type x)))))

;; These predicates are the source sets of admissible lower and upper
;; coefficients, quantified over every real x in the full interval [0,pi].

(defun p25a2-in-closed-interval-p
    (real-type x)
  (and
   (p25a2-real-p real-type x)
   (p25a2-leq real-type (p25a2-zero real-type) x)
   (p25a2-leq real-type x (p25a2-pi real-type))))

(defun p25a2-quadratic-factor
    (real-type x)
  (p25a2-multiply
   real-type
   x
   (p25a2-subtract
    real-type (p25a2-pi real-type) x)))

(defun-sk p25a2-lower-admissible-p
    (real-type coefficient)
  (forall (x)
    (implies
     (p25a2-in-closed-interval-p real-type x)
     (p25a2-leq
      real-type
      (p25a2-multiply
       real-type
       coefficient
       (p25a2-quadratic-factor real-type x))
      (p25a2-sine real-type x)))))

(defun-sk p25a2-upper-admissible-p
    (real-type coefficient)
  (forall (x)
    (implies
     (p25a2-in-closed-interval-p real-type x)
     (p25a2-leq
      real-type
      (p25a2-sine real-type x)
      (p25a2-multiply
       real-type
       coefficient
       (p25a2-quadratic-factor real-type x))))))

(defun-sk p25a2-greatest-lower-coefficient-p
    (real-type coefficient)
  (forall (candidate)
    (and
     (p25a2-real-p real-type coefficient)
     (p25a2-lower-admissible-p real-type coefficient)
     (implies
      (and
       (p25a2-real-p real-type candidate)
       (p25a2-lower-admissible-p
        real-type candidate))
      (p25a2-leq
       real-type candidate coefficient)))))

(defun-sk p25a2-least-upper-coefficient-p
    (real-type coefficient)
  (forall (candidate)
    (and
     (p25a2-real-p real-type coefficient)
     (p25a2-upper-admissible-p real-type coefficient)
     (implies
      (and
       (p25a2-real-p real-type candidate)
       (p25a2-upper-admissible-p
        real-type candidate))
      (p25a2-leq
       real-type coefficient candidate)))))

(defun p25a2-solution-p (real-type a b)
  (let* ((pi-value (p25a2-pi real-type))
         (four (p25a2-natural real-type 4))
         (pi-squared
          (p25a2-multiply real-type pi-value pi-value)))
    (and
     (equal a (p25a2-inverse real-type pi-value))
     (equal
      b
      (p25a2-divide
       real-type four pi-squared)))))

(defun putnambench-putnam-2025-a2-statement
    (real-type a b)
  (implies
   (and
    (p25a2-real-field-p real-type)
    (p25a2-exact-pi-p real-type)
    (p25a2-exact-sine-p real-type)
    (p25a2-real-p real-type a)
    (p25a2-real-p real-type b))
   (iff
    (p25a2-solution-p real-type a b)
    (and
     (p25a2-greatest-lower-coefficient-p
      real-type a)
     (p25a2-least-upper-coefficient-p
      real-type b)))))

(value-triple :itpeval-statement-checked)
:q
