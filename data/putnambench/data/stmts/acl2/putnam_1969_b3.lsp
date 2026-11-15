;; Statement-only formalization of PutnamBench corpus artifact putnam_1969_b3:
;; a real sequence recurrence and successive-term ratio limit imply
;; pi times the square of the first term is 2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative interfaces represent an arbitrary Archimedean ordered
;; subfield of the reals, its pi element, and an arbitrary natural-indexed
;; sequence. Every particular real sequence, together with pi, is contained
;; in such a subfield. All field, order, constant, and sequence properties are
;; explicit hypotheses below; DEFSTUB supplies none of them.

(defstub p69b3-real-p (real-type value) t)
(defstub p69b3-zero (real-type) t)
(defstub p69b3-one (real-type) t)
(defstub p69b3-add (real-type left right) t)
(defstub p69b3-multiply (real-type left right) t)
(defstub p69b3-negate (real-type value) t)
(defstub p69b3-inverse (real-type value) t)
(defstub p69b3-less (real-type left right) t)
(defstub p69b3-pi (real-type) t)
(defstub p69b3-t (real-type index) t)

(defun p69b3-subtract (real-type left right)
  (p69b3-add
   real-type left (p69b3-negate real-type right)))

(defun p69b3-divide (real-type numerator denominator)
  (p69b3-multiply
   real-type numerator (p69b3-inverse real-type denominator)))

(defun p69b3-absolute-value (real-type value)
  (if (p69b3-less real-type value (p69b3-zero real-type))
      (p69b3-negate real-type value)
    value))

(defun p69b3-natural-value (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p69b3-zero real-type)
    (p69b3-add
     real-type
     (p69b3-one real-type)
     (p69b3-natural-value real-type (1- n)))))

(defun-sk p69b3-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p69b3-real-p real-type x)
      (p69b3-real-p real-type y)
      (p69b3-real-p real-type z))
     (let* ((zero (p69b3-zero real-type))
            (one (p69b3-one real-type))
            (x-plus-y (p69b3-add real-type x y))
            (y-plus-z (p69b3-add real-type y z))
            (x-times-y (p69b3-multiply real-type x y))
            (y-times-z (p69b3-multiply real-type y z))
            (minus-x (p69b3-negate real-type x))
            (inverse-x (p69b3-inverse real-type x)))
       (and
        (p69b3-real-p real-type x-plus-y)
        (p69b3-real-p real-type x-times-y)
        (p69b3-real-p real-type minus-x)
        (p69b3-real-p real-type inverse-x)
        (equal
         (p69b3-add real-type x-plus-y z)
         (p69b3-add real-type x y-plus-z))
        (equal x-plus-y (p69b3-add real-type y x))
        (equal (p69b3-add real-type x zero) x)
        (equal (p69b3-add real-type x minus-x) zero)
        (equal
         (p69b3-multiply real-type x-times-y z)
         (p69b3-multiply real-type x y-times-z))
        (equal x-times-y (p69b3-multiply real-type y x))
        (equal (p69b3-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p69b3-multiply real-type x inverse-x)
          one))
        (equal
         (p69b3-multiply real-type x y-plus-z)
         (p69b3-add
          real-type
          (p69b3-multiply real-type x y)
          (p69b3-multiply real-type x z))))))))

(defun-sk p69b3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p69b3-real-p real-type x)
      (p69b3-real-p real-type y)
      (p69b3-real-p real-type z))
     (let ((zero (p69b3-zero real-type)))
       (and
        (not (p69b3-less real-type x x))
        (or
         (p69b3-less real-type x y)
         (equal x y)
         (p69b3-less real-type y x))
        (implies
         (and
          (p69b3-less real-type x y)
          (p69b3-less real-type y z))
         (p69b3-less real-type x z))
        (implies
         (p69b3-less real-type x y)
         (p69b3-less
          real-type
          (p69b3-add real-type x z)
          (p69b3-add real-type y z)))
        (implies
         (and
          (p69b3-less real-type zero x)
          (p69b3-less real-type zero y))
         (p69b3-less
          real-type
          zero
          (p69b3-multiply real-type x y))))))))

(defun-sk p69b3-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (p69b3-less
      real-type value (p69b3-natural-value real-type n)))))

(defun-sk p69b3-archimedean-p (real-type)
  (forall (value)
    (implies
     (p69b3-real-p real-type value)
     (p69b3-archimedean-bound-exists-p
      real-type value))))

(defun p69b3-real-structure-p (real-type)
  (let ((zero (p69b3-zero real-type))
        (one (p69b3-one real-type)))
    (and
     (p69b3-real-p real-type zero)
     (p69b3-real-p real-type one)
     (not (equal zero one))
     (p69b3-field-laws-p real-type)
     (p69b3-order-laws-p real-type)
     (p69b3-less real-type zero one)
     (p69b3-archimedean-p real-type))))

;; Machin's identity fixes pi exactly:
;; pi = 16*arctan(1/5) - 4*arctan(1/239).

(defun p69b3-power (real-type base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (p69b3-one real-type)
    (p69b3-multiply
     real-type
     base
     (p69b3-power real-type base (1- exponent)))))

(defun p69b3-arctan-prefix (real-type z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p69b3-zero real-type)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (unsigned-term
            (p69b3-divide
             real-type
             (p69b3-power real-type z exponent)
             (p69b3-natural-value real-type exponent)))
           (term
            (if (equal (mod index 2) 0)
                unsigned-term
              (p69b3-negate real-type unsigned-term))))
      (p69b3-add
       real-type
       (p69b3-arctan-prefix real-type z index)
       term))))

(defun p69b3-pi-prefix (real-type terms)
  (let* ((one (p69b3-one real-type))
         (five (p69b3-natural-value real-type 5))
         (two-hundred-thirty-nine
          (p69b3-natural-value real-type 239))
         (sixteen (p69b3-natural-value real-type 16))
         (four (p69b3-natural-value real-type 4))
         (atan-one-fifth
          (p69b3-arctan-prefix
           real-type
           (p69b3-divide real-type one five)
           terms))
         (atan-one-over-two-hundred-thirty-nine
          (p69b3-arctan-prefix
           real-type
           (p69b3-divide
            real-type one two-hundred-thirty-nine)
           terms)))
    (p69b3-subtract
     real-type
     (p69b3-multiply real-type sixteen atan-one-fifth)
     (p69b3-multiply
      real-type four atan-one-over-two-hundred-thirty-nine))))

(defun-sk p69b3-pi-tail-p
    (real-type epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (p69b3-less
      real-type
      (p69b3-absolute-value
       real-type
       (p69b3-subtract
        real-type
        (p69b3-pi-prefix real-type terms)
        (p69b3-pi real-type)))
      epsilon))))

(defun-sk p69b3-pi-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p69b3-pi-tail-p real-type epsilon cutoff))))

(defun-sk p69b3-pi-converges-p (real-type)
  (forall (epsilon)
    (implies
     (and
      (p69b3-real-p real-type epsilon)
      (p69b3-less
       real-type (p69b3-zero real-type) epsilon))
     (p69b3-pi-cutoff-exists-p
      real-type epsilon))))

(defun p69b3-pi-value-p (real-type)
  (and
   (p69b3-real-p real-type (p69b3-pi real-type))
   (p69b3-pi-converges-p real-type)))

(defun-sk p69b3-sequence-real-valued-p (real-type)
  (forall (n)
    (implies
     (natp n)
     (p69b3-real-p real-type (p69b3-t real-type n)))))

(defun-sk p69b3-recurrence-p (real-type)
  (forall (n)
    (implies
     (and (natp n)
          (<= 1 n))
     (equal
      (p69b3-multiply
       real-type
       (p69b3-t real-type n)
       (p69b3-t real-type (+ n 1)))
      (p69b3-natural-value real-type n)))))

(defun p69b3-ratio (real-type n)
  (p69b3-divide
   real-type
   (p69b3-t real-type n)
   (p69b3-t real-type (+ n 1))))

(defun-sk p69b3-ratio-limit-tail-p
    (real-type epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (p69b3-less
      real-type
      (p69b3-absolute-value
       real-type
       (p69b3-subtract
        real-type
        (p69b3-ratio real-type n)
        (p69b3-one real-type)))
      epsilon))))

(defun-sk p69b3-ratio-limit-cutoff-exists-p
    (real-type epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p69b3-ratio-limit-tail-p
      real-type epsilon cutoff))))

(defun-sk p69b3-ratio-converges-to-one-p (real-type)
  (forall (epsilon)
    (implies
     (and
      (p69b3-real-p real-type epsilon)
      (p69b3-less
       real-type (p69b3-zero real-type) epsilon))
     (p69b3-ratio-limit-cutoff-exists-p
      real-type epsilon))))

(defun putnambench-putnam-1969-b3-statement
    (real-type)
  (implies
   (and
    (p69b3-real-structure-p real-type)
    (p69b3-pi-value-p real-type)
    (p69b3-sequence-real-valued-p real-type)
    (p69b3-recurrence-p real-type)
    (p69b3-ratio-converges-to-one-p real-type))
   (equal
    (p69b3-multiply
     real-type
     (p69b3-pi real-type)
     (p69b3-multiply
      real-type
      (p69b3-t real-type 1)
      (p69b3-t real-type 1)))
    (p69b3-natural-value real-type 2))))

(value-triple :itpeval-statement-checked)
:q
