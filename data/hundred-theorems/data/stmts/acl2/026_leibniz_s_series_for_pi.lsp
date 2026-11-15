;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__026, "Leibniz's Series for Pi": over the real
;; numbers, the alternating series of reciprocals of the positive odd
;; integers converges to pi/4. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative symbols present an unbounded complete ordered field.
;; The distinguished pi value is fixed independently by convergence of
;; Machin's arctangent series, rather than by the Leibniz series whose limit
;; is the conclusion.

(defstub ht026-real-p (real-type value) t)
(defstub ht026-zero (real-type) t)
(defstub ht026-one (real-type) t)
(defstub ht026-add (real-type left right) t)
(defstub ht026-mul (real-type left right) t)
(defstub ht026-neg (real-type value) t)
(defstub ht026-inv (real-type value) t)
(defstub ht026-less (real-type left right) t)
(defstub ht026-pi (real-type) t)

(defstub ht026-real-set-p (real-type set) t)
(defstub ht026-real-set-member-p (real-type set value) t)
(defstub ht026-supremum (real-type set) t)

(defun ht026-leq (real-type left right)
  (not (ht026-less real-type right left)))

(defun ht026-positive-p (real-type value)
  (and (ht026-real-p real-type value)
       (ht026-less real-type (ht026-zero real-type) value)))

(defun ht026-sub (real-type left right)
  (ht026-add real-type left (ht026-neg real-type right)))

(defun ht026-div (real-type numerator denominator)
  (ht026-mul real-type numerator (ht026-inv real-type denominator)))

(defun ht026-abs (real-type value)
  (if (ht026-less real-type value (ht026-zero real-type))
      (ht026-neg real-type value)
    value))

(defun ht026-nat (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht026-zero real-type)
    (ht026-add real-type
               (ht026-one real-type)
               (ht026-nat real-type (1- n)))))

(defun ht026-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht026-one real-type)
    (ht026-mul real-type
               base
               (ht026-power real-type base (1- exponent)))))

(defun-sk ht026-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and (ht026-real-p real-type x)
          (ht026-real-p real-type y)
          (ht026-real-p real-type z))
     (let* ((zero (ht026-zero real-type))
            (one (ht026-one real-type))
            (xy-add (ht026-add real-type x y))
            (yz-add (ht026-add real-type y z))
            (xy-mul (ht026-mul real-type x y))
            (yz-mul (ht026-mul real-type y z))
            (neg-x (ht026-neg real-type x))
            (inv-x (ht026-inv real-type x)))
       (and
        (ht026-real-p real-type xy-add)
        (ht026-real-p real-type xy-mul)
        (ht026-real-p real-type neg-x)
        (ht026-real-p real-type inv-x)
        (equal (ht026-add real-type xy-add z)
               (ht026-add real-type x yz-add))
        (equal xy-add (ht026-add real-type y x))
        (equal (ht026-add real-type x zero) x)
        (equal (ht026-add real-type x neg-x) zero)
        (equal (ht026-mul real-type xy-mul z)
               (ht026-mul real-type x yz-mul))
        (equal xy-mul (ht026-mul real-type y x))
        (equal (ht026-mul real-type x one) x)
        (implies (equal x zero)
                 (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (ht026-mul real-type x inv-x) one))
        (equal
         (ht026-mul real-type x yz-add)
         (ht026-add real-type
                    (ht026-mul real-type x y)
                    (ht026-mul real-type x z))))))))

(defun-sk ht026-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and (ht026-real-p real-type x)
          (ht026-real-p real-type y)
          (ht026-real-p real-type z))
     (let ((zero (ht026-zero real-type)))
       (and
        (not (ht026-less real-type x x))
        (or (ht026-less real-type x y)
            (equal x y)
            (ht026-less real-type y x))
        (implies
         (and (ht026-less real-type x y)
              (ht026-less real-type y z))
         (ht026-less real-type x z))
        (implies
         (ht026-less real-type x y)
         (ht026-less
          real-type
          (ht026-add real-type x z)
          (ht026-add real-type y z)))
        (implies
         (and (ht026-less real-type zero x)
              (ht026-less real-type zero y))
         (ht026-less
          real-type zero (ht026-mul real-type x y))))))))

(defun-sk ht026-upper-bound-p (real-type set upper)
  (forall (x)
    (implies
     (and (ht026-real-p real-type x)
          (ht026-real-set-member-p real-type set x))
     (ht026-leq real-type x upper))))

(defun-sk ht026-real-set-nonempty-p (real-type set)
  (exists (x)
    (and (ht026-real-p real-type x)
         (ht026-real-set-member-p real-type set x))))

(defun-sk ht026-real-set-bounded-p (real-type set)
  (exists (upper)
    (and (ht026-real-p real-type upper)
         (ht026-upper-bound-p real-type set upper))))

(defun-sk ht026-least-upper-bound-p (real-type set supremum)
  (forall (upper)
    (implies
     (and (ht026-real-p real-type upper)
          (ht026-upper-bound-p real-type set upper))
     (ht026-leq real-type supremum upper))))

(defun-sk ht026-completeness-p (real-type)
  (forall (set)
    (implies
     (and (ht026-real-set-p real-type set)
          (ht026-real-set-nonempty-p real-type set)
          (ht026-real-set-bounded-p real-type set))
     (let ((supremum (ht026-supremum real-type set)))
       (and
        (ht026-real-p real-type supremum)
        (ht026-upper-bound-p real-type set supremum)
        (ht026-least-upper-bound-p
         real-type set supremum))))))

(defun ht026-real-field-p (real-type)
  (let ((zero (ht026-zero real-type))
        (one (ht026-one real-type)))
    (and
     (ht026-real-p real-type zero)
     (ht026-real-p real-type one)
     (not (equal zero one))
     (ht026-field-laws-p real-type)
     (ht026-order-laws-p real-type)
     (ht026-less real-type zero one)
     (ht026-completeness-p real-type))))

;; The arctangent power series is used only to identify the geometric
;; constant pi independently. Machin's identity is
;; pi = 16*arctan(1/5) - 4*arctan(1/239).

(defun ht026-arctan-prefix (real-type z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht026-zero real-type)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned
            (ht026-div
             real-type
             (ht026-power real-type z exponent)
             (ht026-nat real-type exponent)))
           (term
            (if (equal (mod index 2) 0)
                unsigned
              (ht026-neg real-type unsigned))))
      (ht026-add
       real-type
       (ht026-arctan-prefix real-type z index)
       term))))

(defun ht026-machin-pi-prefix (real-type terms)
  (let* ((one (ht026-one real-type))
         (five (ht026-nat real-type 5))
         (two-thirty-nine (ht026-nat real-type 239))
         (sixteen (ht026-nat real-type 16))
         (four (ht026-nat real-type 4)))
    (ht026-sub
     real-type
     (ht026-mul
      real-type
      sixteen
      (ht026-arctan-prefix
       real-type (ht026-div real-type one five) terms))
     (ht026-mul
      real-type
      four
      (ht026-arctan-prefix
       real-type
       (ht026-div real-type one two-thirty-nine)
       terms)))))

(defun-sk ht026-machin-pi-tail-p
    (real-type epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (natp cutoff)
          (<= cutoff terms))
     (ht026-less
      real-type
      (ht026-abs
       real-type
       (ht026-sub
        real-type
        (ht026-machin-pi-prefix real-type terms)
        (ht026-pi real-type)))
      epsilon))))

(defun-sk ht026-machin-pi-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht026-machin-pi-tail-p
      real-type epsilon cutoff))))

(defun-sk ht026-exact-pi-p (real-type)
  (forall (epsilon)
    (implies
     (ht026-positive-p real-type epsilon)
     (ht026-machin-pi-cutoff-exists-p
      real-type epsilon))))

;; These are exactly the partial sums
;; sum_{i < terms} (-1)^i / (2*i+1) in the represented real field.

(defun ht026-leibniz-prefix (real-type terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (ht026-zero real-type)
    (let* ((index (1- terms))
           (denominator (+ (* 2 index) 1))
           (unsigned
            (ht026-inv
             real-type
             (ht026-nat real-type denominator)))
           (term
            (if (equal (mod index 2) 0)
                unsigned
              (ht026-neg real-type unsigned))))
      (ht026-add
       real-type
       (ht026-leibniz-prefix real-type index)
       term))))

(defun ht026-pi-over-four (real-type)
  (ht026-div
   real-type
   (ht026-pi real-type)
   (ht026-nat real-type 4)))

(defun-sk ht026-leibniz-tail-p
    (real-type epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (natp cutoff)
          (<= cutoff terms))
     (ht026-less
      real-type
      (ht026-abs
       real-type
       (ht026-sub
        real-type
        (ht026-leibniz-prefix real-type terms)
        (ht026-pi-over-four real-type)))
      epsilon))))

(defun-sk ht026-leibniz-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht026-leibniz-tail-p
      real-type epsilon cutoff))))

(defun-sk ht026-leibniz-limit-p (real-type)
  (forall (epsilon)
    (implies
     (ht026-positive-p real-type epsilon)
     (ht026-leibniz-cutoff-exists-p
      real-type epsilon))))

(defun hundred-theorems-026-leibniz-series-for-pi-statement
    (real-type)
  (implies
   (and
    (ht026-real-field-p real-type)
    (ht026-real-p real-type (ht026-pi real-type))
    (ht026-exact-pi-p real-type))
   (ht026-leibniz-limit-p real-type)))

(value-triple :itpeval-statement-checked)
:q
