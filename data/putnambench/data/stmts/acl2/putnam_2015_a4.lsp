;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_a4:
;; the greatest lower bound is 4/7 for the binary series whose nth term is
;; 2^(-n) when floor(n*x) is even, over all real x in [0,1).
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no primitive carrier containing every real number.  The
;; conservative interfaces below present an arbitrary Archimedean
;; Dedekind-complete ordered field, hence the real field up to its unique
;; order-preserving field isomorphism.  The floor and series-value interfaces
;; are constrained in the statement by their exact defining properties.  No
;; real input is replaced by a rational, and no infinite sum is replaced by a
;; finite approximant.

(defstub putnam-2015-a4-real-p (real-type value) t)
(defstub putnam-2015-a4-zero (real-type) t)
(defstub putnam-2015-a4-one (real-type) t)
(defstub putnam-2015-a4-add (real-type left right) t)
(defstub putnam-2015-a4-mul (real-type left right) t)
(defstub putnam-2015-a4-neg (real-type value) t)
(defstub putnam-2015-a4-inv (real-type value) t)
(defstub putnam-2015-a4-less (real-type left right) t)
(defstub putnam-2015-a4-supremum (real-type set) t)
(defstub putnam-2015-a4-floor (real-type value) t)
(defstub putnam-2015-a4-series-value (real-type value) t)

(defun putnam-2015-a4-leq (real-type left right)
  (not (putnam-2015-a4-less real-type right left)))

(defun putnam-2015-a4-sub (real-type left right)
  (putnam-2015-a4-add
   real-type
   left
   (putnam-2015-a4-neg real-type right)))

(defun putnam-2015-a4-div (real-type numerator denominator)
  (putnam-2015-a4-mul
   real-type
   numerator
   (putnam-2015-a4-inv real-type denominator)))

(defun putnam-2015-a4-abs (real-type value)
  (if (putnam-2015-a4-less
       real-type value (putnam-2015-a4-zero real-type))
      (putnam-2015-a4-neg real-type value)
    value))

(defun putnam-2015-a4-positive-p (real-type value)
  (and
   (putnam-2015-a4-real-p real-type value)
   (putnam-2015-a4-less
    real-type
    (putnam-2015-a4-zero real-type)
    value)))

(defun putnam-2015-a4-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-2015-a4-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (putnam-2015-a4-real-set-member-p set value)
     (putnam-2015-a4-real-p real-type value))))

;; Complete ordered-field structure.

(defun-sk putnam-2015-a4-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-2015-a4-real-p real-type x)
      (putnam-2015-a4-real-p real-type y)
      (putnam-2015-a4-real-p real-type z))
     (let* ((zero (putnam-2015-a4-zero real-type))
            (one (putnam-2015-a4-one real-type))
            (xy-add (putnam-2015-a4-add real-type x y))
            (yz-add (putnam-2015-a4-add real-type y z))
            (xy-mul (putnam-2015-a4-mul real-type x y))
            (yz-mul (putnam-2015-a4-mul real-type y z))
            (neg-x (putnam-2015-a4-neg real-type x))
            (inv-x (putnam-2015-a4-inv real-type x)))
       (and
        (putnam-2015-a4-real-p real-type xy-add)
        (putnam-2015-a4-real-p real-type xy-mul)
        (putnam-2015-a4-real-p real-type neg-x)
        (putnam-2015-a4-real-p real-type inv-x)
        (equal
         (putnam-2015-a4-add real-type xy-add z)
         (putnam-2015-a4-add real-type x yz-add))
        (equal xy-add (putnam-2015-a4-add real-type y x))
        (equal (putnam-2015-a4-add real-type x zero) x)
        (equal (putnam-2015-a4-add real-type x neg-x) zero)
        (equal
         (putnam-2015-a4-mul real-type xy-mul z)
         (putnam-2015-a4-mul real-type x yz-mul))
        (equal xy-mul (putnam-2015-a4-mul real-type y x))
        (equal (putnam-2015-a4-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-2015-a4-mul real-type x inv-x)
          one))
        (equal
         (putnam-2015-a4-mul real-type x yz-add)
         (putnam-2015-a4-add
          real-type
          (putnam-2015-a4-mul real-type x y)
          (putnam-2015-a4-mul real-type x z))))))))

(defun-sk putnam-2015-a4-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-2015-a4-real-p real-type x)
      (putnam-2015-a4-real-p real-type y)
      (putnam-2015-a4-real-p real-type z))
     (let ((zero (putnam-2015-a4-zero real-type)))
       (and
        (not (putnam-2015-a4-less real-type x x))
        (or
         (putnam-2015-a4-less real-type x y)
         (equal x y)
         (putnam-2015-a4-less real-type y x))
        (implies
         (and
          (putnam-2015-a4-less real-type x y)
          (putnam-2015-a4-less real-type y z))
         (putnam-2015-a4-less real-type x z))
        (implies
         (putnam-2015-a4-less real-type x y)
         (putnam-2015-a4-less
          real-type
          (putnam-2015-a4-add real-type x z)
          (putnam-2015-a4-add real-type y z)))
        (implies
         (and
          (putnam-2015-a4-less real-type zero x)
          (putnam-2015-a4-less real-type zero y))
         (putnam-2015-a4-less
          real-type
          zero
          (putnam-2015-a4-mul real-type x y))))))))

(defun-sk putnam-2015-a4-upper-bound-p
    (real-type set upper)
  (forall (x)
    (implies
     (and
      (putnam-2015-a4-real-p real-type x)
      (putnam-2015-a4-real-set-member-p set x))
     (putnam-2015-a4-leq real-type x upper))))

(defun-sk putnam-2015-a4-real-set-nonempty-p
    (real-type set)
  (exists (x)
    (and
     (putnam-2015-a4-real-p real-type x)
     (putnam-2015-a4-real-set-member-p set x))))

(defun-sk putnam-2015-a4-real-set-bounded-p
    (real-type set)
  (exists (upper)
    (and
     (putnam-2015-a4-real-p real-type upper)
     (putnam-2015-a4-upper-bound-p
      real-type set upper))))

(defun-sk putnam-2015-a4-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-2015-a4-real-p real-type upper)
      (putnam-2015-a4-upper-bound-p
       real-type set upper))
     (putnam-2015-a4-leq
      real-type supremum upper))))

(defun-sk putnam-2015-a4-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-2015-a4-valid-real-set-p real-type set)
      (putnam-2015-a4-real-set-nonempty-p real-type set)
      (putnam-2015-a4-real-set-bounded-p real-type set))
     (let ((supremum
            (putnam-2015-a4-supremum real-type set)))
       (and
        (putnam-2015-a4-real-p real-type supremum)
        (putnam-2015-a4-upper-bound-p
         real-type set supremum)
        (putnam-2015-a4-least-upper-bound-p
         real-type set supremum))))))

(defun putnam-2015-a4-r-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (putnam-2015-a4-zero real-type)
    (putnam-2015-a4-add
     real-type
     (putnam-2015-a4-one real-type)
     (putnam-2015-a4-r-nat real-type (1- n)))))

(defun putnam-2015-a4-r-int (real-type integer)
  (if (integerp integer)
      (if (< integer 0)
          (putnam-2015-a4-neg
           real-type
           (putnam-2015-a4-r-nat real-type (- integer)))
        (putnam-2015-a4-r-nat real-type integer))
    (putnam-2015-a4-zero real-type)))

(defun-sk putnam-2015-a4-archimedean-witness-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-2015-a4-less
      real-type
      value
      (putnam-2015-a4-r-nat real-type n)))))

(defun-sk putnam-2015-a4-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-2015-a4-real-p real-type value)
     (putnam-2015-a4-archimedean-witness-p
      real-type value))))

(defun putnam-2015-a4-real-field-p (real-type)
  (let ((zero (putnam-2015-a4-zero real-type))
        (one (putnam-2015-a4-one real-type)))
    (and
     (putnam-2015-a4-real-p real-type zero)
     (putnam-2015-a4-real-p real-type one)
     (not (equal zero one))
     (putnam-2015-a4-field-laws-p real-type)
     (putnam-2015-a4-order-laws-p real-type)
     (putnam-2015-a4-less real-type zero one)
     (putnam-2015-a4-completeness-p real-type)
     (putnam-2015-a4-archimedean-p real-type))))

;; The integer returned by FLOOR is characterized by
;; embed(k) <= x < embed(k + 1), which uniquely defines the usual floor.

(defun-sk putnam-2015-a4-floor-laws-p (real-type)
  (forall (x)
    (implies
     (putnam-2015-a4-real-p real-type x)
     (let ((integer
            (putnam-2015-a4-floor real-type x)))
       (and
        (integerp integer)
        (putnam-2015-a4-leq
         real-type
         (putnam-2015-a4-r-int real-type integer)
         x)
        (putnam-2015-a4-less
         real-type
         x
         (putnam-2015-a4-r-int
          real-type
          (+ integer 1))))))))

(defun putnam-2015-a4-r-power
    (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-2015-a4-one real-type)
    (putnam-2015-a4-mul
     real-type
     base
     (putnam-2015-a4-r-power
      real-type base (1- exponent)))))

(defun putnam-2015-a4-series-term
    (real-type x n)
  (if (posp n)
      (let* ((nx
              (putnam-2015-a4-mul
               real-type
               (putnam-2015-a4-r-nat real-type n)
               x))
             (floor-nx
              (putnam-2015-a4-floor real-type nx)))
        (if (equal (mod floor-nx 2) 0)
            (putnam-2015-a4-div
             real-type
             (putnam-2015-a4-one real-type)
             (putnam-2015-a4-r-power
              real-type
              (putnam-2015-a4-r-nat real-type 2)
              n))
          (putnam-2015-a4-zero real-type)))
    (putnam-2015-a4-zero real-type)))

;; Sum of the exact source terms with 1 <= n <= TERMS.

(defun putnam-2015-a4-prefix-sum
    (real-type x terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (putnam-2015-a4-zero real-type)
    (putnam-2015-a4-add
     real-type
     (putnam-2015-a4-prefix-sum
      real-type x (1- terms))
     (putnam-2015-a4-series-term
      real-type x terms))))

;; Literal epsilon-N convergence of the partial sums.  This characterizes the
;; same infinite sum used by the source, rather than a bounded approximation.

(defun-sk putnam-2015-a4-limit-tail-p
    (real-type x limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (putnam-2015-a4-less
      real-type
      (putnam-2015-a4-abs
       real-type
       (putnam-2015-a4-sub
        real-type
        (putnam-2015-a4-prefix-sum
         real-type x terms)
        limit))
      epsilon))))

(defun-sk putnam-2015-a4-limit-cutoff-p
    (real-type x limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (putnam-2015-a4-limit-tail-p
      real-type x limit epsilon cutoff))))

(defun-sk putnam-2015-a4-converges-to-p
    (real-type x limit)
  (forall (epsilon)
    (implies
     (putnam-2015-a4-positive-p real-type epsilon)
     (putnam-2015-a4-limit-cutoff-p
      real-type x limit epsilon))))

(defun-sk putnam-2015-a4-series-value-laws-p
    (real-type)
  (forall (x)
    (implies
     (putnam-2015-a4-real-p real-type x)
     (let ((value
            (putnam-2015-a4-series-value real-type x)))
       (and
        (putnam-2015-a4-real-p real-type value)
        (putnam-2015-a4-converges-to-p
         real-type x value))))))

(defun putnam-2015-a4-admissible-p (real-type x)
  (and
   (putnam-2015-a4-real-p real-type x)
   (putnam-2015-a4-leq
    real-type
    (putnam-2015-a4-zero real-type)
    x)
   (putnam-2015-a4-less
    real-type
    x
    (putnam-2015-a4-one real-type))))

(defun-sk putnam-2015-a4-lower-bound-p
    (real-type bound)
  (forall (x)
    (implies
     (putnam-2015-a4-admissible-p real-type x)
     (putnam-2015-a4-leq
      real-type
      bound
      (putnam-2015-a4-series-value real-type x)))))

(defun-sk putnam-2015-a4-greatest-lower-bound-p
    (real-type candidate)
  (forall (bound)
    (implies
     (and
      (putnam-2015-a4-real-p real-type bound)
      (putnam-2015-a4-lower-bound-p real-type bound))
     (putnam-2015-a4-leq
      real-type bound candidate))))

(defun putnam-2015-a4-solution (real-type)
  (putnam-2015-a4-div
   real-type
   (putnam-2015-a4-r-nat real-type 4)
   (putnam-2015-a4-r-nat real-type 7)))

;; Membership of 4/7 in the lower-bound predicate together with maximality is
;; exactly IsGreatest for the source predicate p.

(defun putnambench-putnam-2015-a4-statement (real-type)
  (implies
   (and
    (putnam-2015-a4-real-field-p real-type)
    (putnam-2015-a4-floor-laws-p real-type)
    (putnam-2015-a4-series-value-laws-p real-type))
   (let ((solution
          (putnam-2015-a4-solution real-type)))
     (and
      (putnam-2015-a4-real-p real-type solution)
      (putnam-2015-a4-lower-bound-p
       real-type solution)
      (putnam-2015-a4-greatest-lower-bound-p
       real-type solution)))))

(value-triple :itpeval-statement-checked)
:q
