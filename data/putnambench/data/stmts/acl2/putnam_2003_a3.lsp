;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_a3:
;; the exact minimum over real x of
;; |sin(x)+cos(x)+tan(x)+cot(x)+sec(x)+csc(x)| is 2*sqrt(2)-1.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no primitive completed-real carrier.  The conservative
;; interfaces below present one without replacing it by ACL2's rationals.
;; Every ordered-field, completeness, Archimedean, square-root, sine, and
;; cosine condition used to identify the standard real operations is an
;; explicit hypothesis of the final predicate.

(defstub putnam-2003-a3-real-p (real-type value) t)
(defstub putnam-2003-a3-zero (real-type) t)
(defstub putnam-2003-a3-one (real-type) t)
(defstub putnam-2003-a3-add (real-type left right) t)
(defstub putnam-2003-a3-mul (real-type left right) t)
(defstub putnam-2003-a3-neg (real-type value) t)
(defstub putnam-2003-a3-inv (real-type value) t)
(defstub putnam-2003-a3-less (real-type left right) t)
(defstub putnam-2003-a3-sin (real-type value) t)
(defstub putnam-2003-a3-cos (real-type value) t)
(defstub putnam-2003-a3-sqrt (real-type value) t)

(defstub putnam-2003-a3-supremum (real-type set) t)

;; Tame unary ACL2 function objects are the repository's unbounded predicate
;; representation for scalar subsets.  Membership is restricted to the real
;; carrier, so completeness is not weakened by an unconstrained family-of-
;; sets tag.

(defun putnam-2003-a3-scalar-set-p (real-type set)
  (declare (ignore real-type))
  (tamep-functionp set))

(defun putnam-2003-a3-scalar-set-member-p
    (real-type set value)
  (and
   (putnam-2003-a3-real-p real-type value)
   (if (apply$ set (list value)) t nil)))

(defun putnam-2003-a3-leq (real-type left right)
  (not (putnam-2003-a3-less real-type right left)))

(defun putnam-2003-a3-positive-p (real-type value)
  (and
   (putnam-2003-a3-real-p real-type value)
   (putnam-2003-a3-less
    real-type (putnam-2003-a3-zero real-type) value)))

(defun putnam-2003-a3-sub (real-type left right)
  (putnam-2003-a3-add
   real-type left (putnam-2003-a3-neg real-type right)))

(defun putnam-2003-a3-div (real-type numerator denominator)
  (putnam-2003-a3-mul
   real-type
   numerator
   (putnam-2003-a3-inv real-type denominator)))

(defun putnam-2003-a3-abs (real-type value)
  (if (putnam-2003-a3-less
       real-type value (putnam-2003-a3-zero real-type))
      (putnam-2003-a3-neg real-type value)
    value))

(defun putnam-2003-a3-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-2003-a3-zero real-type)
    (putnam-2003-a3-add
     real-type
     (putnam-2003-a3-one real-type)
     (putnam-2003-a3-nat real-type (1- n)))))

(defun putnam-2003-a3-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-2003-a3-one real-type)
    (putnam-2003-a3-mul
     real-type
     base
     (putnam-2003-a3-power real-type base (1- exponent)))))

(defun putnam-2003-a3-factorial (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-2003-a3-one real-type)
    (putnam-2003-a3-mul
     real-type
     (putnam-2003-a3-nat real-type n)
     (putnam-2003-a3-factorial real-type (1- n)))))

;; A Dedekind-complete Archimedean ordered field is, up to its unique ordered
;; field isomorphism, the real field.  The inverse is totalized at zero, as in
;; the source provers.

(defun-sk putnam-2003-a3-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-2003-a3-real-p real-type x)
      (putnam-2003-a3-real-p real-type y)
      (putnam-2003-a3-real-p real-type z))
     (let* ((zero (putnam-2003-a3-zero real-type))
            (one (putnam-2003-a3-one real-type))
            (xy-add (putnam-2003-a3-add real-type x y))
            (yz-add (putnam-2003-a3-add real-type y z))
            (xy-mul (putnam-2003-a3-mul real-type x y))
            (yz-mul (putnam-2003-a3-mul real-type y z))
            (neg-x (putnam-2003-a3-neg real-type x))
            (inv-x (putnam-2003-a3-inv real-type x)))
       (and
        (putnam-2003-a3-real-p real-type xy-add)
        (putnam-2003-a3-real-p real-type xy-mul)
        (putnam-2003-a3-real-p real-type neg-x)
        (putnam-2003-a3-real-p real-type inv-x)
        (equal
         (putnam-2003-a3-add real-type xy-add z)
         (putnam-2003-a3-add real-type x yz-add))
        (equal xy-add (putnam-2003-a3-add real-type y x))
        (equal (putnam-2003-a3-add real-type x zero) x)
        (equal (putnam-2003-a3-add real-type x neg-x) zero)
        (equal
         (putnam-2003-a3-mul real-type xy-mul z)
         (putnam-2003-a3-mul real-type x yz-mul))
        (equal xy-mul (putnam-2003-a3-mul real-type y x))
        (equal (putnam-2003-a3-mul real-type x one) x)
        (implies (equal x zero) (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-2003-a3-mul real-type x inv-x)
          one))
        (equal
         (putnam-2003-a3-mul real-type x yz-add)
         (putnam-2003-a3-add
          real-type
          (putnam-2003-a3-mul real-type x y)
          (putnam-2003-a3-mul real-type x z))))))))

(defun-sk putnam-2003-a3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-2003-a3-real-p real-type x)
      (putnam-2003-a3-real-p real-type y)
      (putnam-2003-a3-real-p real-type z))
     (let ((zero (putnam-2003-a3-zero real-type)))
       (and
        (not (putnam-2003-a3-less real-type x x))
        (or
         (putnam-2003-a3-less real-type x y)
         (equal x y)
         (putnam-2003-a3-less real-type y x))
        (implies
         (and
          (putnam-2003-a3-less real-type x y)
          (putnam-2003-a3-less real-type y z))
         (putnam-2003-a3-less real-type x z))
        (implies
         (putnam-2003-a3-less real-type x y)
         (putnam-2003-a3-less
          real-type
          (putnam-2003-a3-add real-type x z)
          (putnam-2003-a3-add real-type y z)))
        (implies
         (and
          (putnam-2003-a3-less real-type zero x)
          (putnam-2003-a3-less real-type zero y))
         (putnam-2003-a3-less
          real-type
          zero
          (putnam-2003-a3-mul real-type x y))))))))

(defun-sk putnam-2003-a3-upper-bound-p
    (real-type set upper)
  (forall (x)
    (implies
     (and
      (putnam-2003-a3-real-p real-type x)
      (putnam-2003-a3-scalar-set-member-p real-type set x))
     (putnam-2003-a3-leq real-type x upper))))

(defun-sk putnam-2003-a3-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (putnam-2003-a3-real-p real-type x)
     (putnam-2003-a3-scalar-set-member-p real-type set x))))

(defun-sk putnam-2003-a3-set-bounded-above-p
    (real-type set)
  (exists (upper)
    (and
     (putnam-2003-a3-real-p real-type upper)
     (putnam-2003-a3-upper-bound-p real-type set upper))))

(defun-sk putnam-2003-a3-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-2003-a3-real-p real-type upper)
      (putnam-2003-a3-upper-bound-p real-type set upper))
     (putnam-2003-a3-leq real-type supremum upper))))

(defun-sk putnam-2003-a3-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (putnam-2003-a3-scalar-set-p real-type set)
      (putnam-2003-a3-set-nonempty-p real-type set)
      (putnam-2003-a3-set-bounded-above-p real-type set))
     (let ((supremum
            (putnam-2003-a3-supremum real-type set)))
       (and
        (putnam-2003-a3-real-p real-type supremum)
        (putnam-2003-a3-upper-bound-p
         real-type set supremum)
        (putnam-2003-a3-least-upper-bound-p
         real-type set supremum))))))

(defun-sk putnam-2003-a3-archimedean-bound-exists-p
    (real-type x)
  (exists (n)
    (and
     (natp n)
     (putnam-2003-a3-less
      real-type x (putnam-2003-a3-nat real-type n)))))

(defun-sk putnam-2003-a3-archimedean-p (real-type)
  (forall (x)
    (implies
     (putnam-2003-a3-real-p real-type x)
     (putnam-2003-a3-archimedean-bound-exists-p
      real-type x))))

(defun putnam-2003-a3-real-field-p (real-type)
  (let ((zero (putnam-2003-a3-zero real-type))
        (one (putnam-2003-a3-one real-type)))
    (and
     (putnam-2003-a3-real-p real-type zero)
     (putnam-2003-a3-real-p real-type one)
     (not (equal zero one))
     (putnam-2003-a3-field-laws-p real-type)
     (putnam-2003-a3-order-laws-p real-type)
     (putnam-2003-a3-less real-type zero one)
     (putnam-2003-a3-completeness-p real-type)
     (putnam-2003-a3-archimedean-p real-type))))

;; Sine and cosine are characterized as the limits of their exact Taylor
;; partial sums.  Quantification over every positive real epsilon makes these
;; equalities exact rather than numerical approximations.

(defun putnam-2003-a3-sin-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (putnam-2003-a3-zero real-type)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned
            (putnam-2003-a3-div
             real-type
             (putnam-2003-a3-power real-type x exponent)
             (putnam-2003-a3-factorial
              real-type exponent)))
           (term
            (if (evenp index)
                unsigned
              (putnam-2003-a3-neg real-type unsigned))))
      (putnam-2003-a3-add
       real-type
       (putnam-2003-a3-sin-prefix real-type x index)
       term))))

(defun putnam-2003-a3-cos-prefix (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (putnam-2003-a3-zero real-type)
    (let* ((index (1- terms))
           (exponent (* 2 index))
           (unsigned
            (putnam-2003-a3-div
             real-type
             (putnam-2003-a3-power real-type x exponent)
             (putnam-2003-a3-factorial
              real-type exponent)))
           (term
            (if (evenp index)
                unsigned
              (putnam-2003-a3-neg real-type unsigned))))
      (putnam-2003-a3-add
       real-type
       (putnam-2003-a3-cos-prefix real-type x index)
       term))))

(defun-sk putnam-2003-a3-sin-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (putnam-2003-a3-less
      real-type
      (putnam-2003-a3-abs
       real-type
       (putnam-2003-a3-sub
        real-type
        (putnam-2003-a3-sin-prefix real-type x terms)
        (putnam-2003-a3-sin real-type x)))
      epsilon))))

(defun-sk putnam-2003-a3-cos-tail-p
    (real-type x epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (putnam-2003-a3-less
      real-type
      (putnam-2003-a3-abs
       real-type
       (putnam-2003-a3-sub
        real-type
        (putnam-2003-a3-cos-prefix real-type x terms)
        (putnam-2003-a3-cos real-type x)))
      epsilon))))

(defun-sk putnam-2003-a3-sin-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2003-a3-sin-tail-p
      real-type x epsilon cutoff))))

(defun-sk putnam-2003-a3-cos-cutoff-exists-p
    (real-type x epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2003-a3-cos-tail-p
      real-type x epsilon cutoff))))

(defun-sk putnam-2003-a3-analytic-functions-p (real-type)
  (forall (x epsilon)
    (implies
     (putnam-2003-a3-real-p real-type x)
     (and
      (putnam-2003-a3-real-p
       real-type (putnam-2003-a3-sin real-type x))
      (putnam-2003-a3-real-p
       real-type (putnam-2003-a3-cos real-type x))
      (implies
       (putnam-2003-a3-positive-p real-type epsilon)
       (and
        (putnam-2003-a3-sin-cutoff-exists-p
         real-type x epsilon)
        (putnam-2003-a3-cos-cutoff-exists-p
         real-type x epsilon)))))))

;; The square-root interface is the source provers' total nonnegative square
;; root, including value zero on negative inputs.

(defun-sk putnam-2003-a3-square-root-p (real-type)
  (forall (x)
    (implies
     (putnam-2003-a3-real-p real-type x)
     (let ((zero (putnam-2003-a3-zero real-type))
           (root (putnam-2003-a3-sqrt real-type x)))
       (and
        (putnam-2003-a3-real-p real-type root)
        (implies
         (putnam-2003-a3-less real-type x zero)
         (equal root zero))
        (implies
         (not (putnam-2003-a3-less real-type x zero))
         (and
          (putnam-2003-a3-leq real-type zero root)
          (equal
           (putnam-2003-a3-mul real-type root root)
           x))))))))

(defun putnam-2003-a3-context-p (real-type)
  (and
   (putnam-2003-a3-real-field-p real-type)
   (putnam-2003-a3-analytic-functions-p real-type)
   (putnam-2003-a3-square-root-p real-type)))

;; This is the source expression itself.  TAN is SIN/COS, while COT, SEC,
;; and CSC are respectively 1/TAN, 1/COS, and 1/SIN.  Totalized inverse at
;; zero matches Lean, Isabelle, and Rocq.

(defun putnam-2003-a3-value (real-type x)
  (let* ((one (putnam-2003-a3-one real-type))
         (sine (putnam-2003-a3-sin real-type x))
         (cosine (putnam-2003-a3-cos real-type x))
         (tangent
          (putnam-2003-a3-div real-type sine cosine))
         (cotangent
          (putnam-2003-a3-div real-type one tangent))
         (secant
          (putnam-2003-a3-div real-type one cosine))
         (cosecant
          (putnam-2003-a3-div real-type one sine)))
    (putnam-2003-a3-abs
     real-type
     (putnam-2003-a3-add
      real-type
      sine
      (putnam-2003-a3-add
       real-type
       cosine
       (putnam-2003-a3-add
        real-type
        tangent
        (putnam-2003-a3-add
         real-type
         cotangent
         (putnam-2003-a3-add
          real-type secant cosecant))))))))

(defun-sk putnam-2003-a3-attained-p
    (real-type solution)
  (exists (x)
    (and
     (putnam-2003-a3-real-p real-type x)
     (equal
      (putnam-2003-a3-value real-type x)
      solution))))

(defun-sk putnam-2003-a3-lower-bound-p
    (real-type solution)
  (forall (x)
    (implies
     (putnam-2003-a3-real-p real-type x)
     (putnam-2003-a3-leq
      real-type
      solution
      (putnam-2003-a3-value real-type x)))))

;; The conclusion is exactly IsLeast(range f, 2*sqrt(2)-1): the first clause
;; states membership in the range, and the second compares the same exact
;; value with every real input.

(defun-sk putnambench-putnam-2003-a3-statement ()
  (forall (real-type)
    (implies
     (putnam-2003-a3-context-p real-type)
     (let* ((one (putnam-2003-a3-one real-type))
            (two (putnam-2003-a3-add real-type one one))
            (sqrt-two
             (putnam-2003-a3-sqrt real-type two))
            (solution
             (putnam-2003-a3-sub
              real-type
              (putnam-2003-a3-mul
               real-type two sqrt-two)
              one)))
       (and
        (putnam-2003-a3-real-p real-type solution)
        (putnam-2003-a3-attained-p real-type solution)
        (putnam-2003-a3-lower-bound-p
         real-type solution))))))

(value-triple :itpeval-statement-checked)
:q
