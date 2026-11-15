;; Statement-only formalization of the PutnamBench corpus artifact
;; putnam_1982_a3: the improper real integral of
;; (arctan(pi*x) - arctan(x))/x equals (pi/2)*log(pi). This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative interfaces below present an arbitrary real carrier,
;; its ordered-field operations, arbitrary subsets, and the distinguished
;; analytic functions occurring in the statement.

(defstub putnam-1982-a3-real-p (real-type value) t)
(defstub putnam-1982-a3-zero (real-type) t)
(defstub putnam-1982-a3-one (real-type) t)
(defstub putnam-1982-a3-add (real-type left right) t)
(defstub putnam-1982-a3-mul (real-type left right) t)
(defstub putnam-1982-a3-neg (real-type value) t)
(defstub putnam-1982-a3-inv (real-type value) t)
(defstub putnam-1982-a3-lt (real-type left right) t)

(defstub putnam-1982-a3-set-member-p (real-type set value) t)

(defstub putnam-1982-a3-pi (real-type) t)
(defstub putnam-1982-a3-arctan (real-type value) t)
(defstub putnam-1982-a3-log (real-type value) t)
(defstub putnam-1982-a3-prefix-integral (real-type upper) t)

(defun putnam-1982-a3-sub (real-type x y)
  (putnam-1982-a3-add
   real-type x (putnam-1982-a3-neg real-type y)))

(defun putnam-1982-a3-le (real-type x y)
  (not (putnam-1982-a3-lt real-type y x)))

(defun putnam-1982-a3-div (real-type x y)
  (putnam-1982-a3-mul
   real-type x (putnam-1982-a3-inv real-type y)))

(defun putnam-1982-a3-abs (real-type x)
  (if (putnam-1982-a3-lt
       real-type x (putnam-1982-a3-zero real-type))
      (putnam-1982-a3-neg real-type x)
    x))

(defun putnam-1982-a3-two (real-type)
  (putnam-1982-a3-add
   real-type
   (putnam-1982-a3-one real-type)
   (putnam-1982-a3-one real-type)))

(defun putnam-1982-a3-four (real-type)
  (putnam-1982-a3-add
   real-type
   (putnam-1982-a3-two real-type)
   (putnam-1982-a3-two real-type)))

(defun putnam-1982-a3-nat-value (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-1982-a3-zero real-type)
    (putnam-1982-a3-add
     real-type
     (putnam-1982-a3-one real-type)
     (putnam-1982-a3-nat-value real-type (1- n)))))

;; A complete Archimedean ordered-field presentation of the real numbers.

(defun-sk putnam-1982-a3-operation-closure-p (real-type)
  (forall (x y)
    (and
     (putnam-1982-a3-real-p
      real-type (putnam-1982-a3-zero real-type))
     (putnam-1982-a3-real-p
      real-type (putnam-1982-a3-one real-type))
     (implies
      (putnam-1982-a3-real-p real-type x)
      (and
       (putnam-1982-a3-real-p
        real-type (putnam-1982-a3-neg real-type x))
       (putnam-1982-a3-real-p
        real-type (putnam-1982-a3-inv real-type x))))
     (implies
      (and
       (putnam-1982-a3-real-p real-type x)
       (putnam-1982-a3-real-p real-type y))
      (and
       (putnam-1982-a3-real-p
        real-type (putnam-1982-a3-add real-type x y))
       (putnam-1982-a3-real-p
        real-type (putnam-1982-a3-mul real-type x y)))))))

(defun-sk putnam-1982-a3-unary-field-laws-p (real-type)
  (forall (x)
    (implies
     (putnam-1982-a3-real-p real-type x)
     (let ((zero (putnam-1982-a3-zero real-type))
           (one (putnam-1982-a3-one real-type)))
       (and
        (equal (putnam-1982-a3-add real-type zero x) x)
        (equal (putnam-1982-a3-add real-type x zero) x)
        (equal
         (putnam-1982-a3-add
          real-type x (putnam-1982-a3-neg real-type x))
         zero)
        (equal (putnam-1982-a3-mul real-type one x) x)
        (equal (putnam-1982-a3-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal (putnam-1982-a3-inv real-type x) zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1982-a3-mul
           real-type x (putnam-1982-a3-inv real-type x))
          one)))))))

(defun-sk putnam-1982-a3-binary-field-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (putnam-1982-a3-real-p real-type x)
      (putnam-1982-a3-real-p real-type y))
     (and
      (equal
       (putnam-1982-a3-add real-type x y)
       (putnam-1982-a3-add real-type y x))
      (equal
       (putnam-1982-a3-mul real-type x y)
       (putnam-1982-a3-mul real-type y x))))))

(defun-sk putnam-1982-a3-ternary-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1982-a3-real-p real-type x)
      (putnam-1982-a3-real-p real-type y)
      (putnam-1982-a3-real-p real-type z))
     (and
      (equal
       (putnam-1982-a3-add
        real-type (putnam-1982-a3-add real-type x y) z)
       (putnam-1982-a3-add
        real-type x (putnam-1982-a3-add real-type y z)))
      (equal
       (putnam-1982-a3-mul
        real-type (putnam-1982-a3-mul real-type x y) z)
       (putnam-1982-a3-mul
        real-type x (putnam-1982-a3-mul real-type y z)))
      (equal
       (putnam-1982-a3-mul
        real-type x (putnam-1982-a3-add real-type y z))
       (putnam-1982-a3-add
        real-type
        (putnam-1982-a3-mul real-type x y)
        (putnam-1982-a3-mul real-type x z)))))))

(defun-sk putnam-1982-a3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1982-a3-real-p real-type x)
      (putnam-1982-a3-real-p real-type y)
      (putnam-1982-a3-real-p real-type z))
     (and
      (not (putnam-1982-a3-lt real-type x x))
      (implies
       (and
        (putnam-1982-a3-lt real-type x y)
        (putnam-1982-a3-lt real-type y z))
       (putnam-1982-a3-lt real-type x z))
      (or
       (putnam-1982-a3-lt real-type x y)
       (equal x y)
       (putnam-1982-a3-lt real-type y x))
      (implies
       (putnam-1982-a3-lt real-type x y)
       (putnam-1982-a3-lt
        real-type
        (putnam-1982-a3-add real-type x z)
        (putnam-1982-a3-add real-type y z)))
      (implies
       (and
        (putnam-1982-a3-lt
         real-type (putnam-1982-a3-zero real-type) x)
        (putnam-1982-a3-lt
         real-type (putnam-1982-a3-zero real-type) y))
       (putnam-1982-a3-lt
        real-type
        (putnam-1982-a3-zero real-type)
        (putnam-1982-a3-mul real-type x y)))))))

(defun-sk putnam-1982-a3-valid-real-set-p (real-type set)
  (forall (x)
    (implies
     (putnam-1982-a3-set-member-p real-type set x)
     (putnam-1982-a3-real-p real-type x))))

(defun-sk putnam-1982-a3-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (putnam-1982-a3-real-p real-type x)
     (putnam-1982-a3-set-member-p real-type set x))))

(defun-sk putnam-1982-a3-upper-bound-p (real-type set bound)
  (forall (x)
    (implies
     (putnam-1982-a3-set-member-p real-type set x)
     (putnam-1982-a3-le real-type x bound))))

(defun-sk putnam-1982-a3-bounded-above-p (real-type set)
  (exists (bound)
    (and
     (putnam-1982-a3-real-p real-type bound)
     (putnam-1982-a3-upper-bound-p real-type set bound))))

(defun-sk putnam-1982-a3-least-upper-bound-p
    (real-type set supremum)
  (forall (bound)
    (and
     (putnam-1982-a3-real-p real-type supremum)
     (putnam-1982-a3-upper-bound-p real-type set supremum)
     (implies
      (and
       (putnam-1982-a3-real-p real-type bound)
       (putnam-1982-a3-upper-bound-p real-type set bound))
      (putnam-1982-a3-le real-type supremum bound)))))

(defun-sk putnam-1982-a3-supremum-exists-p (real-type set)
  (exists (supremum)
    (putnam-1982-a3-least-upper-bound-p
     real-type set supremum)))

(defun-sk putnam-1982-a3-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (putnam-1982-a3-valid-real-set-p real-type set)
      (putnam-1982-a3-set-nonempty-p real-type set)
      (putnam-1982-a3-bounded-above-p real-type set))
     (putnam-1982-a3-supremum-exists-p real-type set))))

(defun-sk putnam-1982-a3-archimedean-witness-p
    (real-type x)
  (exists (n)
    (and
     (natp n)
     (putnam-1982-a3-lt
      real-type x (putnam-1982-a3-nat-value real-type n)))))

(defun-sk putnam-1982-a3-archimedean-p (real-type)
  (forall (x)
    (implies
     (putnam-1982-a3-real-p real-type x)
     (putnam-1982-a3-archimedean-witness-p real-type x))))

(defun putnam-1982-a3-real-structure-p (real-type)
  (and
   (putnam-1982-a3-operation-closure-p real-type)
   (putnam-1982-a3-unary-field-laws-p real-type)
   (putnam-1982-a3-binary-field-laws-p real-type)
   (putnam-1982-a3-ternary-field-laws-p real-type)
   (putnam-1982-a3-order-laws-p real-type)
   (not
    (equal
     (putnam-1982-a3-zero real-type)
     (putnam-1982-a3-one real-type)))
   (putnam-1982-a3-lt
    real-type
    (putnam-1982-a3-zero real-type)
    (putnam-1982-a3-one real-type))
   (putnam-1982-a3-dedekind-complete-p real-type)
   (putnam-1982-a3-archimedean-p real-type)))

;; Exact compact-interval integrals are represented by convergence of uniform
;; midpoint Riemann sums. This gives every integral a concrete, nonvacuous
;; approximation sequence without quantifying over coded gauge functions.

(defun putnam-1982-a3-integrand-value
    (real-type kind x)
  (cond
   ((equal kind :arctan-kernel)
    (putnam-1982-a3-inv
     real-type
     (putnam-1982-a3-add
      real-type
      (putnam-1982-a3-one real-type)
      (putnam-1982-a3-mul
       real-type x x))))
   ((equal kind :log-kernel)
    (putnam-1982-a3-inv real-type x))
   ((equal kind :main-integrand)
    (putnam-1982-a3-div
     real-type
     (putnam-1982-a3-sub
      real-type
      (putnam-1982-a3-arctan
       real-type
       (putnam-1982-a3-mul
        real-type
        (putnam-1982-a3-pi real-type)
        x))
      (putnam-1982-a3-arctan real-type x))
     x))
   (t (putnam-1982-a3-zero real-type))))

(defun putnam-1982-a3-midpoint
    (real-type a b index subdivisions)
  (putnam-1982-a3-add
   real-type
   a
   (putnam-1982-a3-mul
    real-type
    (putnam-1982-a3-sub real-type b a)
    (putnam-1982-a3-div
     real-type
     (putnam-1982-a3-nat-value
      real-type (+ (* 2 index) 1))
     (putnam-1982-a3-nat-value
      real-type (* 2 subdivisions))))))

(defun putnam-1982-a3-midpoint-sum-aux
    (real-type kind a b remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (putnam-1982-a3-zero real-type)
    (let* ((index (- remaining 1))
           (x (putnam-1982-a3-midpoint
               real-type a b index subdivisions))
           (width
            (putnam-1982-a3-div
             real-type
             (putnam-1982-a3-sub real-type b a)
             (putnam-1982-a3-nat-value
              real-type subdivisions))))
      (putnam-1982-a3-add
       real-type
       (putnam-1982-a3-mul
        real-type
        (putnam-1982-a3-integrand-value
         real-type kind x)
        width)
       (putnam-1982-a3-midpoint-sum-aux
        real-type kind a b index subdivisions)))))

(defun putnam-1982-a3-riemann-sum
    (real-type kind a b subdivisions)
  (if (posp subdivisions)
      (putnam-1982-a3-midpoint-sum-aux
       real-type kind a b subdivisions subdivisions)
    (putnam-1982-a3-zero real-type)))

(defun-sk putnam-1982-a3-integral-sums-tail-p
    (real-type kind integral a b epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (putnam-1982-a3-lt
      real-type
      (putnam-1982-a3-abs
       real-type
       (putnam-1982-a3-sub
        real-type
        (putnam-1982-a3-riemann-sum
         real-type kind a b subdivisions)
        integral))
      epsilon))))

(defun-sk putnam-1982-a3-integral-cutoff-exists-p
    (real-type kind integral a b epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (putnam-1982-a3-integral-sums-tail-p
      real-type kind integral a b epsilon cutoff))))

(defun-sk putnam-1982-a3-integral-sums-converge-p
    (real-type kind integral a b)
  (forall (epsilon)
    (implies
     (and
      (putnam-1982-a3-real-p real-type epsilon)
      (putnam-1982-a3-lt
       real-type
       (putnam-1982-a3-zero real-type)
       epsilon))
     (putnam-1982-a3-integral-cutoff-exists-p
      real-type kind integral a b epsilon))))

(defun putnam-1982-a3-has-midpoint-integral-p
    (real-type kind integral a b)
  (and
   (putnam-1982-a3-real-p real-type a)
   (putnam-1982-a3-real-p real-type b)
   (putnam-1982-a3-le real-type a b)
   (putnam-1982-a3-real-p real-type integral)
   (putnam-1982-a3-integral-sums-converge-p
    real-type kind integral a b)))

;; Exact definitions of the source constants and functions. On the positive
;; arguments used here, arctan(y) is the integral of 1/(1+x^2) from 0 to y,
;; pi is 4*arctan(1), and log(y) is the integral of 1/x from 1 to y.

(defun-sk putnam-1982-a3-arctan-definition-p (real-type)
  (forall (y)
    (implies
     (and
      (putnam-1982-a3-real-p real-type y)
      (putnam-1982-a3-le
       real-type (putnam-1982-a3-zero real-type) y))
     (putnam-1982-a3-has-midpoint-integral-p
      real-type
      :arctan-kernel
      (putnam-1982-a3-arctan real-type y)
      (putnam-1982-a3-zero real-type)
      y))))

(defun putnam-1982-a3-pi-definition-p (real-type)
  (let ((pi-value (putnam-1982-a3-pi real-type))
        (one (putnam-1982-a3-one real-type)))
    (and
     (putnam-1982-a3-real-p real-type pi-value)
     (putnam-1982-a3-lt real-type one pi-value)
     (equal
      pi-value
      (putnam-1982-a3-mul
       real-type
       (putnam-1982-a3-four real-type)
       (putnam-1982-a3-arctan real-type one))))))

(defun-sk putnam-1982-a3-log-definition-p (real-type)
  (forall (y)
    (implies
     (and
      (putnam-1982-a3-real-p real-type y)
      (putnam-1982-a3-le
       real-type (putnam-1982-a3-one real-type) y))
     (putnam-1982-a3-has-midpoint-integral-p
      real-type
      :log-kernel
      (putnam-1982-a3-log real-type y)
      (putnam-1982-a3-one real-type)
      y))))

(defun-sk putnam-1982-a3-prefix-definition-p (real-type)
  (forall (upper)
    (implies
     (and
      (putnam-1982-a3-real-p real-type upper)
      (putnam-1982-a3-le
       real-type (putnam-1982-a3-zero real-type) upper))
     (putnam-1982-a3-has-midpoint-integral-p
      real-type
      :main-integrand
      (putnam-1982-a3-prefix-integral real-type upper)
      (putnam-1982-a3-zero real-type)
      upper))))

(defun putnam-1982-a3-solution (real-type)
  (putnam-1982-a3-div
   real-type
   (putnam-1982-a3-mul
    real-type
    (putnam-1982-a3-pi real-type)
    (putnam-1982-a3-log
     real-type (putnam-1982-a3-pi real-type)))
   (putnam-1982-a3-two real-type)))

;; The source at-top convergence quantifier, over all real upper endpoints.

(defun-sk putnam-1982-a3-eventually-close-p
    (real-type epsilon threshold)
  (forall (upper)
    (implies
     (and
      (putnam-1982-a3-real-p real-type upper)
      (putnam-1982-a3-le real-type threshold upper))
     (putnam-1982-a3-lt
      real-type
      (putnam-1982-a3-abs
       real-type
       (putnam-1982-a3-sub
        real-type
        (putnam-1982-a3-prefix-integral real-type upper)
        (putnam-1982-a3-solution real-type)))
      epsilon))))

(defun-sk putnam-1982-a3-threshold-exists-p
    (real-type epsilon)
  (exists (threshold)
    (and
     (putnam-1982-a3-real-p real-type threshold)
     (putnam-1982-a3-le
      real-type (putnam-1982-a3-zero real-type) threshold)
     (putnam-1982-a3-eventually-close-p
      real-type epsilon threshold))))

(defun-sk putnam-1982-a3-improper-limit-p (real-type)
  (forall (epsilon)
    (implies
     (and
      (putnam-1982-a3-real-p real-type epsilon)
      (putnam-1982-a3-lt
       real-type
       (putnam-1982-a3-zero real-type)
       epsilon))
     (putnam-1982-a3-threshold-exists-p
      real-type epsilon))))

(defun-sk putnambench-putnam-1982-a3-statement ()
  (forall (real-type)
    (implies
     (and
      (putnam-1982-a3-real-structure-p real-type)
      (putnam-1982-a3-arctan-definition-p real-type)
      (putnam-1982-a3-pi-definition-p real-type)
      (putnam-1982-a3-log-definition-p real-type)
      (putnam-1982-a3-prefix-definition-p real-type))
     (putnam-1982-a3-improper-limit-p real-type))))

(value-triple :itpeval-statement-checked)
:q
