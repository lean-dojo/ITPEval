;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__066, "Sum of a Geometric Series": in the real
;; numbers, the first n terms of a geometric progression have their standard
;; closed form, and if |r| < 1 then the series sum of a*r^n converges to
;; a/(1-r). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 has no native real-number carrier. Following the corpus convention for
;; generic mathematical structures, these conservative interfaces describe an
;; arbitrary carrier together with the operations of a Dedekind-complete
;; Archimedean ordered field, hence the real field up to ordered-field
;; isomorphism. Subsets are unary tame APPLY$ predicates, so completeness ranges
;; over predicate-valued set representations rather than over a fixed finite
;; collection of set tags. The carrier is not enumerated or replaced by ACL2
;; rationals.

(defstub ht066-real-p (real-type value) t)
(defstub ht066-zero (real-type) t)
(defstub ht066-one (real-type) t)
(defstub ht066-add (real-type left right) t)
(defstub ht066-mul (real-type left right) t)
(defstub ht066-neg (real-type value) t)
(defstub ht066-inv (real-type value) t)
(defstub ht066-less (real-type left right) t)

(defstub ht066-supremum (real-type set) t)

(defun ht066-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk ht066-valid-real-set-p (real-type set)
  (forall (value)
    (implies
     (ht066-real-set-member-p set value)
     (ht066-real-p real-type value))))

(defun ht066-leq (real-type left right)
  (not (ht066-less real-type right left)))

(defun ht066-sub (real-type left right)
  (ht066-add real-type left (ht066-neg real-type right)))

(defun ht066-div (real-type numerator denominator)
  (ht066-mul real-type numerator (ht066-inv real-type denominator)))

(defun ht066-abs (real-type value)
  (if (ht066-less real-type value (ht066-zero real-type))
      (ht066-neg real-type value)
    value))

(defun ht066-positive-p (real-type value)
  (and
   (ht066-real-p real-type value)
   (ht066-less real-type (ht066-zero real-type) value)))

(defun ht066-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht066-zero real-type)
    (ht066-add
     real-type
     (ht066-one real-type)
     (ht066-nat real-type (1- n)))))

(defun ht066-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht066-one real-type)
    (ht066-mul
     real-type
     base
     (ht066-power real-type base (1- exponent)))))

(defun ht066-geometric-prefix (real-type a r terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht066-zero real-type)
    (let ((index (1- terms)))
      (ht066-add
       real-type
       (ht066-geometric-prefix real-type a r index)
       (ht066-mul
        real-type
        a
        (ht066-power real-type r index))))))

(defun-sk ht066-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (ht066-real-p real-type x)
      (ht066-real-p real-type y)
      (ht066-real-p real-type z))
     (let* ((zero (ht066-zero real-type))
            (one (ht066-one real-type))
            (xy-add (ht066-add real-type x y))
            (yz-add (ht066-add real-type y z))
            (xy-mul (ht066-mul real-type x y))
            (yz-mul (ht066-mul real-type y z))
            (neg-x (ht066-neg real-type x))
            (inv-x (ht066-inv real-type x)))
       (and
        (ht066-real-p real-type xy-add)
        (ht066-real-p real-type xy-mul)
        (ht066-real-p real-type neg-x)
        (ht066-real-p real-type inv-x)
        (equal
         (ht066-add real-type xy-add z)
         (ht066-add real-type x yz-add))
        (equal xy-add (ht066-add real-type y x))
        (equal (ht066-add real-type x zero) x)
        (equal (ht066-add real-type x neg-x) zero)
        (equal
         (ht066-mul real-type xy-mul z)
         (ht066-mul real-type x yz-mul))
        (equal xy-mul (ht066-mul real-type y x))
        (equal (ht066-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (ht066-mul real-type x inv-x) one))
        (equal
         (ht066-mul real-type x yz-add)
         (ht066-add
          real-type
          (ht066-mul real-type x y)
          (ht066-mul real-type x z))))))))

(defun-sk ht066-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (ht066-real-p real-type x)
      (ht066-real-p real-type y)
      (ht066-real-p real-type z))
     (let ((zero (ht066-zero real-type)))
       (and
        (not (ht066-less real-type x x))
        (or
         (ht066-less real-type x y)
         (equal x y)
         (ht066-less real-type y x))
        (implies
         (and
          (ht066-less real-type x y)
          (ht066-less real-type y z))
         (ht066-less real-type x z))
        (implies
         (ht066-less real-type x y)
         (ht066-less
          real-type
          (ht066-add real-type x z)
          (ht066-add real-type y z)))
        (implies
         (and
          (ht066-less real-type zero x)
          (ht066-less real-type zero y))
         (ht066-less
          real-type
          zero
          (ht066-mul real-type x y))))))))

(defun-sk ht066-upper-bound-p (real-type set upper)
  (forall (x)
    (implies
     (and
      (ht066-real-p real-type x)
      (ht066-real-set-member-p set x))
     (ht066-leq real-type x upper))))

(defun-sk ht066-real-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (ht066-real-p real-type x)
     (ht066-real-set-member-p set x))))

(defun-sk ht066-real-set-bounded-p (real-type set)
  (exists (upper)
    (and
     (ht066-real-p real-type upper)
     (ht066-upper-bound-p real-type set upper))))

(defun-sk ht066-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (ht066-real-p real-type upper)
      (ht066-upper-bound-p real-type set upper))
     (ht066-leq real-type supremum upper))))

(defun-sk ht066-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (ht066-valid-real-set-p real-type set)
      (ht066-real-set-nonempty-p real-type set)
      (ht066-real-set-bounded-p real-type set))
     (let ((supremum (ht066-supremum real-type set)))
       (and
        (ht066-real-p real-type supremum)
        (ht066-upper-bound-p real-type set supremum)
        (ht066-least-upper-bound-p
         real-type set supremum))))))

(defun-sk ht066-archimedean-witness-exists-p
    (real-type x)
  (exists (n)
    (and
     (natp n)
     (ht066-less real-type x (ht066-nat real-type n)))))

(defun-sk ht066-archimedean-p (real-type)
  (forall (x)
    (implies
     (ht066-real-p real-type x)
     (ht066-archimedean-witness-exists-p real-type x))))

(defun ht066-real-field-p (real-type)
  (let ((zero (ht066-zero real-type))
        (one (ht066-one real-type)))
    (and
     (ht066-real-p real-type zero)
     (ht066-real-p real-type one)
     (not (equal zero one))
     (ht066-field-laws-p real-type)
     (ht066-order-laws-p real-type)
     (ht066-less real-type zero one)
     (ht066-completeness-p real-type)
     (ht066-archimedean-p real-type))))

;; This is
;;   sum_{i < n} a*r^i = a*(1-r^n)/(1-r)
;; for every natural n and every r different from 1.

(defun-sk ht066-finite-geometric-identity-p (real-type)
  (forall (a r terms)
    (implies
     (and
      (ht066-real-p real-type a)
      (ht066-real-p real-type r)
      (natp terms)
      (not (equal r (ht066-one real-type))))
     (equal
      (ht066-geometric-prefix real-type a r terms)
      (ht066-div
       real-type
       (ht066-mul
        real-type
        a
        (ht066-sub
         real-type
         (ht066-one real-type)
         (ht066-power real-type r terms)))
       (ht066-sub
        real-type
        (ht066-one real-type)
        r))))))

;; The next three predicates are the literal epsilon-N definition that the
;; partial sums of a*r^n converge to the supplied limit.

(defun-sk ht066-geometric-tail-p
    (real-type a r limit epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (ht066-less
      real-type
      (ht066-abs
       real-type
       (ht066-sub
        real-type
        (ht066-geometric-prefix real-type a r terms)
        limit))
      epsilon))))

(defun-sk ht066-geometric-cutoff-exists-p
    (real-type a r limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht066-geometric-tail-p
      real-type a r limit epsilon cutoff))))

(defun-sk ht066-geometric-limit-p
    (real-type a r limit)
  (forall (epsilon)
    (implies
     (ht066-positive-p real-type epsilon)
     (ht066-geometric-cutoff-exists-p
      real-type a r limit epsilon))))

;; For every real a and r with |r| < 1, the geometric series converges to the
;; field quotient a/(1-r), with no cutoff supplied as an external parameter.

(defun-sk ht066-geometric-series-convergence-p (real-type)
  (forall (a r)
    (implies
     (and
      (ht066-real-p real-type a)
      (ht066-real-p real-type r)
      (ht066-less
       real-type
       (ht066-abs real-type r)
       (ht066-one real-type)))
     (ht066-geometric-limit-p
      real-type
      a
      r
      (ht066-div
       real-type
       a
       (ht066-sub
        real-type
        (ht066-one real-type)
        r))))))

(defun hundred-theorems-066-sum-of-a-geometric-series-statement
    (real-type)
  (implies
   (ht066-real-field-p real-type)
   (and
    (ht066-finite-geometric-identity-p real-type)
    (ht066-geometric-series-convergence-p real-type))))

(value-triple :itpeval-statement-checked)
:q
