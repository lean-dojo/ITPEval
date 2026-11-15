;; Statement-only formalization of thousand-theorems corpus artifact Q2734084,
;; "Bohr–Mollerup theorem": every positive log-convex real function normalized
;; at one and satisfying the Gamma recurrence equals the Gamma function on the
;; positive reals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; An arbitrary Dedekind-complete ordered field presents the real numbers.
;; The standard exponential is its full power-series limit, logarithm is the
;; inverse of exponential on the positive reals, and Gamma on the positive
;; reals is its full Euler-limit value
;;
;;   lim_m m! * m^x / (x * (x+1) * ... * (x+m)).
;;
;; Thus no real is replaced by a rational value or finite approximation.
;; FUNCTION-VALUE retains the source's arbitrary function argument, while all
;; hypotheses and the equality conclusion remain under their source scopes.

(defstub q2734084-r-member-p (real value) t)
(defstub q2734084-r-zero (real) t)
(defstub q2734084-r-one (real) t)
(defstub q2734084-r-add (real left right) t)
(defstub q2734084-r-multiply (real left right) t)
(defstub q2734084-r-negate (real value) t)
(defstub q2734084-r-inverse (real value) t)
(defstub q2734084-r-less (real left right) t)
(defstub q2734084-r-generic-set-member-p (real set value) t)

(defstub q2734084-r-exponential (real value) t)
(defstub q2734084-r-logarithm (real value) t)
(defstub q2734084-r-gamma (real value) t)
(defstub q2734084-function-value (real function argument) t)

(defun q2734084-r-subtract (real left right)
  (q2734084-r-add
   real left (q2734084-r-negate real right)))

(defun q2734084-r-divide (real numerator denominator)
  (q2734084-r-multiply
   real numerator (q2734084-r-inverse real denominator)))

(defun q2734084-r-leq (real left right)
  (not (q2734084-r-less real right left)))

(defun q2734084-r-absolute-value (real value)
  (if (q2734084-r-less
       real value (q2734084-r-zero real))
      (q2734084-r-negate real value)
    value))

(defun q2734084-r-positive-p (real value)
  (and
   (q2734084-r-member-p real value)
   (q2734084-r-less
    real (q2734084-r-zero real) value)))

(defun q2734084-r-nonnegative-p (real value)
  (and
   (q2734084-r-member-p real value)
   (q2734084-r-leq
    real (q2734084-r-zero real) value)))

;; Complete ordered-field presentation.

(defun-sk q2734084-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2734084-r-member-p real x)
      (q2734084-r-member-p real y)
      (q2734084-r-member-p real z))
     (let* ((zero (q2734084-r-zero real))
            (one (q2734084-r-one real))
            (xy-add (q2734084-r-add real x y))
            (yz-add (q2734084-r-add real y z))
            (xy-mul (q2734084-r-multiply real x y))
            (yz-mul (q2734084-r-multiply real y z))
            (neg-x (q2734084-r-negate real x))
            (inv-x (q2734084-r-inverse real x)))
       (and
        (q2734084-r-member-p real zero)
        (q2734084-r-member-p real one)
        (q2734084-r-member-p real xy-add)
        (q2734084-r-member-p real xy-mul)
        (q2734084-r-member-p real neg-x)
        (q2734084-r-member-p real inv-x)
        (equal
         (q2734084-r-add real xy-add z)
         (q2734084-r-add real x yz-add))
        (equal xy-add (q2734084-r-add real y x))
        (equal (q2734084-r-add real x zero) x)
        (equal (q2734084-r-add real x neg-x) zero)
        (equal
         (q2734084-r-multiply real xy-mul z)
         (q2734084-r-multiply real x yz-mul))
        (equal xy-mul (q2734084-r-multiply real y x))
        (equal (q2734084-r-multiply real x one) x)
        (equal (q2734084-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q2734084-r-multiply real x inv-x)
          one))
        (equal
         (q2734084-r-multiply
          real x (q2734084-r-add real y z))
         (q2734084-r-add
          real
          (q2734084-r-multiply real x y)
          (q2734084-r-multiply real x z))))))))

(defun-sk q2734084-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q2734084-r-member-p real x)
      (q2734084-r-member-p real y)
      (q2734084-r-member-p real z))
     (let ((zero (q2734084-r-zero real)))
       (and
        (not (q2734084-r-less real x x))
        (or
         (equal x y)
         (q2734084-r-less real x y)
         (q2734084-r-less real y x))
        (implies
         (and
          (q2734084-r-less real x y)
          (q2734084-r-less real y z))
         (q2734084-r-less real x z))
        (implies
         (q2734084-r-less real x y)
         (q2734084-r-less
          real
          (q2734084-r-add real x z)
          (q2734084-r-add real y z)))
        (implies
         (and
          (q2734084-r-less real zero x)
          (q2734084-r-less real zero y))
         (q2734084-r-less
          real zero
          (q2734084-r-multiply real x y))))))))

(defun q2734084-r-singleton-set (real value)
  (list :q2734084-singleton real value))

(defun q2734084-r-set-member-p (real set value)
  (if
      (and
       (true-listp set)
       (equal (len set) 3)
       (equal (car set) :q2734084-singleton)
       (equal (cadr set) real))
      (equal value (caddr set))
    (q2734084-r-generic-set-member-p real set value)))

(defun-sk q2734084-r-valid-set-p (real set)
  (forall (x)
    (implies
     (q2734084-r-set-member-p real set x)
     (q2734084-r-member-p real x))))

(defun-sk q2734084-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q2734084-r-member-p real x)
     (q2734084-r-set-member-p real set x))))

(defun-sk q2734084-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q2734084-r-member-p real x)
      (q2734084-r-set-member-p real set x))
     (q2734084-r-leq real x bound))))

(defun-sk q2734084-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q2734084-r-member-p real bound)
     (q2734084-r-upper-bound-p real set bound))))

(defun-sk q2734084-r-least-upper-bound-p
    (real set supremum)
  (forall (bound)
    (and
     (q2734084-r-member-p real supremum)
     (q2734084-r-upper-bound-p real set supremum)
     (implies
      (and
       (q2734084-r-member-p real bound)
       (q2734084-r-upper-bound-p real set bound))
      (q2734084-r-leq real supremum bound)))))

(defun-sk q2734084-r-supremum-exists-p (real set)
  (exists (supremum)
    (q2734084-r-least-upper-bound-p
     real set supremum)))

(defun-sk q2734084-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q2734084-r-valid-set-p real set)
      (q2734084-r-set-nonempty-p real set)
      (q2734084-r-bounded-above-p real set))
     (q2734084-r-supremum-exists-p real set))))

(defun q2734084-real-field-p (real)
  (let ((zero (q2734084-r-zero real))
        (one (q2734084-r-one real)))
    (and
     (q2734084-r-member-p real zero)
     (q2734084-r-member-p real one)
     (not (equal zero one))
     (q2734084-r-field-laws-p real)
     (q2734084-r-order-laws-p real)
     (q2734084-r-less real zero one)
     (q2734084-r-set-nonempty-p
      real (q2734084-r-singleton-set real zero))
     (q2734084-r-dedekind-complete-p real))))

;; Standard exponential and logarithm.

(defun q2734084-natural-cast (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2734084-r-zero real)
    (q2734084-r-add
     real
     (q2734084-natural-cast real (1- n))
     (q2734084-r-one real))))

(defun q2734084-natural-factorial (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2734084-r-one real)
    (q2734084-r-multiply
     real
     (q2734084-natural-cast real n)
     (q2734084-natural-factorial real (1- n)))))

(defun q2734084-natural-power (real x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2734084-r-one real)
    (q2734084-r-multiply
     real x
     (q2734084-natural-power real x (1- n)))))

(defun q2734084-exponential-partial-sum (real x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q2734084-r-one real)
    (q2734084-r-add
     real
     (q2734084-exponential-partial-sum real x (1- n))
     (q2734084-r-divide
      real
      (q2734084-natural-power real x n)
      (q2734084-natural-factorial real n)))))

(defun-sk q2734084-exponential-tail-close-p
    (real x value epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (q2734084-r-less
      real
      (q2734084-r-absolute-value
       real
       (q2734084-r-subtract
        real
        (q2734084-exponential-partial-sum real x n)
        value))
      epsilon))))

(defun-sk q2734084-exponential-cutoff-exists-p
    (real x value epsilon)
  (exists (start)
    (and
     (natp start)
     (q2734084-exponential-tail-close-p
      real x value epsilon start))))

(defun-sk q2734084-exponential-limit-p
    (real x value)
  (forall (epsilon)
    (implies
     (q2734084-r-positive-p real epsilon)
     (q2734084-exponential-cutoff-exists-p
      real x value epsilon))))

(defun-sk q2734084-standard-exponential-p (real)
  (forall (x)
    (implies
     (q2734084-r-member-p real x)
     (and
      (q2734084-r-positive-p
       real (q2734084-r-exponential real x))
      (q2734084-exponential-limit-p
       real x (q2734084-r-exponential real x))))))

(defun-sk q2734084-standard-logarithm-p (real)
  (forall (x)
    (and
     (implies
      (q2734084-r-member-p real x)
      (equal
       (q2734084-r-logarithm
        real (q2734084-r-exponential real x))
       x))
     (implies
      (q2734084-r-positive-p real x)
      (and
       (q2734084-r-member-p
        real (q2734084-r-logarithm real x))
       (equal
        (q2734084-r-exponential
         real (q2734084-r-logarithm real x))
        x))))))

;; The standard Gamma function on the positive reals via Euler's limit.

(defun q2734084-rising-product (real x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      x
    (q2734084-r-multiply
     real
     (q2734084-rising-product real x (1- n))
     (q2734084-r-add
      real x (q2734084-natural-cast real n)))))

(defun q2734084-euler-gamma-term (real x n)
  (let* ((m (+ 1 (nfix n)))
         (m-real (q2734084-natural-cast real m))
         (m-to-x
          (q2734084-r-exponential
           real
           (q2734084-r-multiply
            real x (q2734084-r-logarithm real m-real)))))
    (q2734084-r-divide
     real
     (q2734084-r-multiply
      real
      (q2734084-natural-factorial real m)
      m-to-x)
     (q2734084-rising-product real x m))))

(defun-sk q2734084-gamma-tail-close-p
    (real x value epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (q2734084-r-less
      real
      (q2734084-r-absolute-value
       real
       (q2734084-r-subtract
        real
        (q2734084-euler-gamma-term real x n)
        value))
      epsilon))))

(defun-sk q2734084-gamma-cutoff-exists-p
    (real x value epsilon)
  (exists (start)
    (and
     (natp start)
     (q2734084-gamma-tail-close-p
      real x value epsilon start))))

(defun-sk q2734084-gamma-limit-p (real x value)
  (forall (epsilon)
    (implies
     (q2734084-r-positive-p real epsilon)
     (q2734084-gamma-cutoff-exists-p
      real x value epsilon))))

(defun-sk q2734084-standard-gamma-p (real)
  (forall (x)
    (implies
     (q2734084-r-positive-p real x)
     (and
      (q2734084-r-positive-p
       real (q2734084-r-gamma real x))
      (q2734084-gamma-limit-p
       real x (q2734084-r-gamma real x))))))

;; Exact translation of the four hypotheses and EqOn conclusion.

(defun-sk q2734084-real-function-p (real function)
  (forall (x)
    (implies
     (q2734084-r-member-p real x)
     (q2734084-r-member-p
      real
      (q2734084-function-value real function x)))))

(defun-sk q2734084-log-convex-on-positive-p
    (real function)
  (forall (x y a b)
    (implies
     (and
      (q2734084-r-positive-p real x)
      (q2734084-r-positive-p real y)
      (q2734084-r-nonnegative-p real a)
      (q2734084-r-nonnegative-p real b)
      (equal
       (q2734084-r-add real a b)
       (q2734084-r-one real)))
     (let* ((ax
             (q2734084-r-multiply real a x))
            (by
             (q2734084-r-multiply real b y))
            (combination
             (q2734084-r-add real ax by))
            (log-combination
             (q2734084-r-logarithm
              real
              (q2734084-function-value
               real function combination)))
            (weighted-logs
             (q2734084-r-add
              real
              (q2734084-r-multiply
               real a
               (q2734084-r-logarithm
                real
                (q2734084-function-value
                 real function x)))
              (q2734084-r-multiply
               real b
               (q2734084-r-logarithm
                real
                (q2734084-function-value
                 real function y))))))
       (and
        (q2734084-r-positive-p real combination)
        (q2734084-r-leq
         real log-combination weighted-logs))))))

(defun-sk q2734084-recurrence-p (real function)
  (forall (y)
    (implies
     (q2734084-r-positive-p real y)
     (equal
      (q2734084-function-value
       real function
       (q2734084-r-add
        real y (q2734084-r-one real)))
      (q2734084-r-multiply
       real y
       (q2734084-function-value
        real function y))))))

(defun-sk q2734084-positive-valued-p (real function)
  (forall (y)
    (implies
     (q2734084-r-positive-p real y)
     (q2734084-r-positive-p
      real
      (q2734084-function-value real function y)))))

(defun-sk q2734084-equal-gamma-on-positive-p
    (real function)
  (forall (x)
    (implies
     (q2734084-r-positive-p real x)
     (equal
      (q2734084-function-value real function x)
      (q2734084-r-gamma real x)))))

(defun-sk
    thousand-theorems-q2734084-bohr-mollerup-theorem-statement
    ()
  (forall (real function)
    (implies
     (and
      (q2734084-real-field-p real)
      (q2734084-standard-exponential-p real)
      (q2734084-standard-logarithm-p real)
      (q2734084-standard-gamma-p real)
      (q2734084-real-function-p real function)
      (q2734084-log-convex-on-positive-p real function)
      (q2734084-recurrence-p real function)
      (q2734084-positive-valued-p real function)
      (equal
       (q2734084-function-value
        real function (q2734084-r-one real))
       (q2734084-r-one real)))
     (q2734084-equal-gamma-on-positive-p
      real function))))

(value-triple :itpeval-statement-checked)
:q
