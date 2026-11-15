;; Statement-only formalization of thousand-theorems corpus artifact Q3229335,
;; "Borel–Carathéodory theorem": a complex-differentiable function on an open
;; ball whose real part is bounded above satisfies the canonical
;; Borel–Carathéodory norm bound at every point of the ball. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; A Dedekind-complete ordered-field presentation of the real numbers. The
;; carrier, operations, order, and arbitrary subsets remain unbounded ACL2
;; objects; no finite carrier or table is used.

(defstub q3229335-r-member-p (real value) t)
(defstub q3229335-r-zero (real) t)
(defstub q3229335-r-one (real) t)
(defstub q3229335-r-add (real left right) t)
(defstub q3229335-r-multiply (real left right) t)
(defstub q3229335-r-negate (real value) t)
(defstub q3229335-r-inverse (real value) t)
(defstub q3229335-r-less (real left right) t)
(defstub q3229335-r-set-member-p (real set value) t)

(defun q3229335-r-subtract (real left right)
  (q3229335-r-add
   real left (q3229335-r-negate real right)))

(defun q3229335-r-leq (real left right)
  (not (q3229335-r-less real right left)))

(defun q3229335-r-positive-p (real value)
  (and
   (q3229335-r-member-p real value)
   (q3229335-r-less
    real (q3229335-r-zero real) value)))

(defun q3229335-r-divide (real numerator denominator)
  (q3229335-r-multiply
   real numerator (q3229335-r-inverse real denominator)))

(defun q3229335-r-two (real)
  (q3229335-r-add
   real
   (q3229335-r-one real)
   (q3229335-r-one real)))

(defun-sk q3229335-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3229335-r-member-p real x)
      (q3229335-r-member-p real y)
      (q3229335-r-member-p real z))
     (let* ((zero (q3229335-r-zero real))
            (one (q3229335-r-one real))
            (xy-add (q3229335-r-add real x y))
            (yz-add (q3229335-r-add real y z))
            (xy-mul (q3229335-r-multiply real x y))
            (yz-mul (q3229335-r-multiply real y z))
            (neg-x (q3229335-r-negate real x))
            (inv-x (q3229335-r-inverse real x)))
       (and
        (q3229335-r-member-p real xy-add)
        (q3229335-r-member-p real xy-mul)
        (q3229335-r-member-p real neg-x)
        (q3229335-r-member-p real inv-x)
        (equal
         (q3229335-r-add real xy-add z)
         (q3229335-r-add real x yz-add))
        (equal xy-add (q3229335-r-add real y x))
        (equal (q3229335-r-add real x zero) x)
        (equal (q3229335-r-add real x neg-x) zero)
        (equal
         (q3229335-r-multiply real xy-mul z)
         (q3229335-r-multiply real x yz-mul))
        (equal xy-mul (q3229335-r-multiply real y x))
        (equal (q3229335-r-multiply real x one) x)
        (equal (q3229335-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q3229335-r-multiply real x inv-x)
          one))
        (equal
         (q3229335-r-multiply
          real x (q3229335-r-add real y z))
         (q3229335-r-add
          real
          (q3229335-r-multiply real x y)
          (q3229335-r-multiply real x z))))))))

(defun-sk q3229335-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q3229335-r-member-p real x)
      (q3229335-r-member-p real y)
      (q3229335-r-member-p real z))
     (let ((zero (q3229335-r-zero real)))
       (and
        (not (q3229335-r-less real x x))
        (or
         (equal x y)
         (q3229335-r-less real x y)
         (q3229335-r-less real y x))
        (implies
         (and
          (q3229335-r-less real x y)
          (q3229335-r-less real y z))
         (q3229335-r-less real x z))
        (implies
         (q3229335-r-less real x y)
         (q3229335-r-less
          real
          (q3229335-r-add real x z)
          (q3229335-r-add real y z)))
        (implies
         (and
          (q3229335-r-less real zero x)
          (q3229335-r-less real zero y))
         (q3229335-r-less
          real zero
          (q3229335-r-multiply real x y))))))))

(defun-sk q3229335-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q3229335-r-member-p real x)
     (q3229335-r-set-member-p real set x))))

(defun-sk q3229335-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q3229335-r-member-p real x)
      (q3229335-r-set-member-p real set x))
     (q3229335-r-leq real x bound))))

(defun-sk q3229335-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q3229335-r-member-p real bound)
     (q3229335-r-upper-bound-p real set bound))))

(defun-sk q3229335-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q3229335-r-member-p real supremum)
     (q3229335-r-upper-bound-p real set supremum)
     (implies
      (and
       (q3229335-r-member-p real bound)
       (q3229335-r-upper-bound-p real set bound))
      (q3229335-r-leq real supremum bound)))))

(defun-sk q3229335-r-has-supremum-p (real set)
  (exists (supremum)
    (q3229335-r-supremum-p real set supremum)))

(defun-sk q3229335-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q3229335-r-set-nonempty-p real set)
      (q3229335-r-bounded-above-p real set))
     (q3229335-r-has-supremum-p real set))))

(defun q3229335-real-field-p (real)
  (let ((zero (q3229335-r-zero real))
        (one (q3229335-r-one real)))
    (and
     (q3229335-r-member-p real zero)
     (q3229335-r-member-p real one)
     (not (equal zero one))
     (q3229335-r-field-laws-p real)
     (q3229335-r-order-laws-p real)
     (q3229335-r-less real zero one)
     (q3229335-r-dedekind-complete-p real))))

;; The nonnegative square root and the standard complex field represented by
;; real/imaginary coordinate pairs.

(defstub q3229335-r-square-root (real square-root value) t)

(defun-sk q3229335-r-square-root-laws-p
    (real square-root)
  (forall (x)
    (implies
     (and
      (q3229335-r-member-p real x)
      (q3229335-r-leq
       real (q3229335-r-zero real) x))
     (let ((root
            (q3229335-r-square-root
             real square-root x)))
       (and
        (q3229335-r-member-p real root)
        (q3229335-r-leq
         real (q3229335-r-zero real) root)
        (equal
         (q3229335-r-multiply real root root)
         x))))))

(defun q3229335-complex-p (real value)
  (and
   (consp value)
   (q3229335-r-member-p real (car value))
   (q3229335-r-member-p real (cdr value))))

(defun q3229335-c-zero (real)
  (cons
   (q3229335-r-zero real)
   (q3229335-r-zero real)))

(defun q3229335-c-add (real left right)
  (cons
   (q3229335-r-add real (car left) (car right))
   (q3229335-r-add real (cdr left) (cdr right))))

(defun q3229335-c-negate (real value)
  (cons
   (q3229335-r-negate real (car value))
   (q3229335-r-negate real (cdr value))))

(defun q3229335-c-subtract (real left right)
  (q3229335-c-add
   real left (q3229335-c-negate real right)))

(defun q3229335-c-multiply (real left right)
  (cons
   (q3229335-r-subtract
    real
    (q3229335-r-multiply
     real (car left) (car right))
    (q3229335-r-multiply
     real (cdr left) (cdr right)))
   (q3229335-r-add
    real
    (q3229335-r-multiply
     real (car left) (cdr right))
    (q3229335-r-multiply
     real (cdr left) (car right)))))

(defun q3229335-c-norm-square (real value)
  (q3229335-r-add
   real
   (q3229335-r-multiply
    real (car value) (car value))
   (q3229335-r-multiply
    real (cdr value) (cdr value))))

(defun q3229335-c-norm (real square-root value)
  (q3229335-r-square-root
   real square-root
   (q3229335-c-norm-square real value)))

(defun q3229335-c-distance
    (real square-root left right)
  (q3229335-c-norm
   real square-root
   (q3229335-c-subtract real left right)))

;; Arbitrary total functions C -> C and the source open ball centered at zero.

(defstub q3229335-function-value (function argument) t)

(defun-sk q3229335-function-typed-p (real function)
  (forall (x)
    (implies
     (q3229335-complex-p real x)
     (q3229335-complex-p
      real (q3229335-function-value function x)))))

(defun q3229335-open-ball-member-p
    (real square-root radius x)
  (and
   (q3229335-complex-p real x)
   (q3229335-r-less
    real
    (q3229335-c-norm real square-root x)
    radius)))

;; This is exactly MapsTo f (ball 0 R) {w | w.re <= M}.

(defun-sk q3229335-real-part-bounded-on-ball-p
    (real square-root function radius bound)
  (forall (x)
    (implies
     (q3229335-open-ball-member-p
      real square-root radius x)
     (q3229335-r-leq
      real
      (car (q3229335-function-value function x))
      bound))))

;; Complex Frechet differentiability within the open ball. For C -> C, every
;; complex-linear derivative is multiplication by one complex number. The
;; epsilon-delta remainder condition is the standard equivalent definition of
;; HasFDerivWithinAt, with the within-ball quantifier retained.

(defun-sk q3229335-derivative-within-radius-p
    (real square-root function ball-radius point
          derivative epsilon delta)
  (forall (y)
    (implies
     (and
      (q3229335-open-ball-member-p
       real square-root ball-radius y)
      (q3229335-r-less
       real
       (q3229335-c-distance
        real square-root y point)
       delta))
     (let* ((increment
             (q3229335-c-subtract real y point))
            (remainder
             (q3229335-c-subtract
              real
              (q3229335-c-subtract
               real
               (q3229335-function-value function y)
               (q3229335-function-value function point))
              (q3229335-c-multiply
               real derivative increment))))
       (q3229335-r-leq
        real
        (q3229335-c-norm
         real square-root remainder)
        (q3229335-r-multiply
         real epsilon
         (q3229335-c-norm
          real square-root increment)))))))

(defun-sk q3229335-derivative-within-delta-exists-p
    (real square-root function ball-radius point
          derivative epsilon)
  (exists (delta)
    (and
     (q3229335-r-positive-p real delta)
     (q3229335-derivative-within-radius-p
      real square-root function ball-radius point
      derivative epsilon delta))))

(defun-sk q3229335-has-derivative-within-at-p
    (real square-root function ball-radius point derivative)
  (forall (epsilon)
    (implies
     (q3229335-r-positive-p real epsilon)
     (q3229335-derivative-within-delta-exists-p
      real square-root function ball-radius point
      derivative epsilon))))

(defun-sk q3229335-differentiable-within-at-p
    (real square-root function ball-radius point)
  (exists (derivative)
    (and
     (q3229335-complex-p real derivative)
     (q3229335-has-derivative-within-at-p
      real square-root function ball-radius point derivative))))

(defun-sk q3229335-differentiable-on-ball-p
    (real square-root function radius)
  (forall (point)
    (implies
     (q3229335-open-ball-member-p
      real square-root radius point)
     (q3229335-differentiable-within-at-p
      real square-root function radius point))))

(defun q3229335-bound-right-hand-side
    (real square-root function radius bound z)
  (let* ((norm-z
          (q3229335-c-norm real square-root z))
         (denominator
          (q3229335-r-subtract real radius norm-z))
         (first-numerator
          (q3229335-r-multiply
           real
           (q3229335-r-multiply
            real
            (q3229335-r-two real)
            bound)
           norm-z))
         (second-numerator
          (q3229335-r-multiply
           real
           (q3229335-c-norm
            real square-root
            (q3229335-function-value
             function (q3229335-c-zero real)))
           (q3229335-r-add real radius norm-z))))
    (q3229335-r-add
     real
     (q3229335-r-divide
      real first-numerator denominator)
     (q3229335-r-divide
      real second-numerator denominator))))

(defun-sk
    thousand-theorems-q3229335-borel-caratheodory-theorem-statement
    ()
  (forall (real square-root function bound radius z)
    (implies
     (and
      (q3229335-real-field-p real)
      (q3229335-r-square-root-laws-p
       real square-root)
      (q3229335-function-typed-p real function)
      (q3229335-r-positive-p real bound)
      (q3229335-r-positive-p real radius)
      (q3229335-complex-p real z)
      (q3229335-differentiable-on-ball-p
       real square-root function radius)
      (q3229335-real-part-bounded-on-ball-p
       real square-root function radius bound)
      (q3229335-open-ball-member-p
       real square-root radius z))
     (q3229335-r-leq
      real
      (q3229335-c-norm
       real square-root
       (q3229335-function-value function z))
      (q3229335-bound-right-hand-side
       real square-root function radius bound z)))))

(value-triple :itpeval-statement-checked)
:q
