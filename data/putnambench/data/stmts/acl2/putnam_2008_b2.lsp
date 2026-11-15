;; Statement-only formalization of PutnamBench corpus artifact putnam_2008_b2:
;; an arbitrary real-valued family obtained by repeated integration from the
;; real logarithm has factorial-normalized values at 1 whose quotient by
;; log(n) tends to -1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Real values, real-valued families, gauges, and sets are arbitrary ACL2
;; objects interpreted through conservative fixed-arity interfaces.
;; Formula-specific DEFUN-SK binders retain the source's unbounded
;; quantifiers; no finite carrier or function table is used.

(defstub pb08b2-real-p (real-type value) t)
(defstub pb08b2-zero (real-type) t)
(defstub pb08b2-one (real-type) t)
(defstub pb08b2-add (real-type left right) t)
(defstub pb08b2-multiply (real-type left right) t)
(defstub pb08b2-negate (real-type value) t)
(defstub pb08b2-inverse (real-type value) t)
(defstub pb08b2-less (real-type left right) t)
(defstub pb08b2-set-member-p (real-type set value) t)

(defstub pb08b2-logarithm (real-type value) t)
(defstub pb08b2-family-value
  (real-type family natural-index argument) t)
(defstub pb08b2-gauge-value (real-type gauge argument) t)

(defun pb08b2-subtract (real-type left right)
  (pb08b2-add
   real-type left (pb08b2-negate real-type right)))

(defun pb08b2-divide (real-type numerator denominator)
  (pb08b2-multiply
   real-type numerator (pb08b2-inverse real-type denominator)))

(defun pb08b2-leq (real-type left right)
  (not (pb08b2-less real-type right left)))

(defun pb08b2-absolute-value (real-type value)
  (if (pb08b2-less
       real-type value (pb08b2-zero real-type))
      (pb08b2-negate real-type value)
    value))

(defun pb08b2-positive-real-p (real-type value)
  (and
   (pb08b2-real-p real-type value)
   (pb08b2-less
    real-type (pb08b2-zero real-type) value)))

;; A complete Archimedean ordered-field presentation of the real carrier.

(defun-sk pb08b2-operation-closure-p (real-type)
  (forall (x y)
    (and
     (pb08b2-real-p real-type (pb08b2-zero real-type))
     (pb08b2-real-p real-type (pb08b2-one real-type))
     (implies
      (pb08b2-real-p real-type x)
      (and
       (pb08b2-real-p
        real-type (pb08b2-negate real-type x))
       (pb08b2-real-p
        real-type (pb08b2-inverse real-type x))))
     (implies
      (and
       (pb08b2-real-p real-type x)
       (pb08b2-real-p real-type y))
      (and
       (pb08b2-real-p
        real-type (pb08b2-add real-type x y))
       (pb08b2-real-p
        real-type (pb08b2-multiply real-type x y)))))))

(defun-sk pb08b2-unary-field-laws-p (real-type)
  (forall (x)
    (implies
     (pb08b2-real-p real-type x)
     (let ((zero (pb08b2-zero real-type))
           (one (pb08b2-one real-type)))
       (and
        (equal (pb08b2-add real-type zero x) x)
        (equal (pb08b2-add real-type x zero) x)
        (equal
         (pb08b2-add
          real-type x (pb08b2-negate real-type x))
         zero)
        (equal (pb08b2-multiply real-type one x) x)
        (equal (pb08b2-multiply real-type x one) x)
        (implies
         (equal x zero)
         (equal (pb08b2-inverse real-type x) zero))
        (implies
         (not (equal x zero))
         (equal
          (pb08b2-multiply
           real-type x (pb08b2-inverse real-type x))
          one)))))))

(defun-sk pb08b2-binary-field-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (pb08b2-real-p real-type x)
      (pb08b2-real-p real-type y))
     (and
      (equal
       (pb08b2-add real-type x y)
       (pb08b2-add real-type y x))
      (equal
       (pb08b2-multiply real-type x y)
       (pb08b2-multiply real-type y x))))))

(defun-sk pb08b2-ternary-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (pb08b2-real-p real-type x)
      (pb08b2-real-p real-type y)
      (pb08b2-real-p real-type z))
     (and
      (equal
       (pb08b2-add
        real-type (pb08b2-add real-type x y) z)
       (pb08b2-add
        real-type x (pb08b2-add real-type y z)))
      (equal
       (pb08b2-multiply
        real-type (pb08b2-multiply real-type x y) z)
       (pb08b2-multiply
        real-type x (pb08b2-multiply real-type y z)))
      (equal
       (pb08b2-multiply
        real-type x (pb08b2-add real-type y z))
       (pb08b2-add
        real-type
        (pb08b2-multiply real-type x y)
        (pb08b2-multiply real-type x z)))))))

(defun-sk pb08b2-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (pb08b2-real-p real-type x)
      (pb08b2-real-p real-type y)
      (pb08b2-real-p real-type z))
     (and
      (not (pb08b2-less real-type x x))
      (or
       (pb08b2-less real-type x y)
       (equal x y)
       (pb08b2-less real-type y x))
      (implies
       (and
        (pb08b2-less real-type x y)
        (pb08b2-less real-type y z))
       (pb08b2-less real-type x z))
      (implies
       (pb08b2-less real-type x y)
       (pb08b2-less
        real-type
        (pb08b2-add real-type x z)
        (pb08b2-add real-type y z)))
      (implies
       (and
        (pb08b2-less
         real-type (pb08b2-zero real-type) x)
        (pb08b2-less
         real-type (pb08b2-zero real-type) y))
       (pb08b2-less
        real-type
        (pb08b2-zero real-type)
        (pb08b2-multiply real-type x y)))))))

(defun-sk pb08b2-valid-real-set-p (real-type set)
  (forall (x)
    (implies
     (pb08b2-set-member-p real-type set x)
     (pb08b2-real-p real-type x))))

(defun-sk pb08b2-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (pb08b2-real-p real-type x)
     (pb08b2-set-member-p real-type set x))))

(defun-sk pb08b2-upper-bound-p (real-type set bound)
  (forall (x)
    (implies
     (pb08b2-set-member-p real-type set x)
     (pb08b2-leq real-type x bound))))

(defun-sk pb08b2-set-bounded-above-p (real-type set)
  (exists (bound)
    (and
     (pb08b2-real-p real-type bound)
     (pb08b2-upper-bound-p real-type set bound))))

(defun-sk pb08b2-least-upper-bound-p
    (real-type set supremum)
  (forall (bound)
    (and
     (pb08b2-real-p real-type supremum)
     (pb08b2-upper-bound-p real-type set supremum)
     (implies
      (and
       (pb08b2-real-p real-type bound)
       (pb08b2-upper-bound-p real-type set bound))
      (pb08b2-leq real-type supremum bound)))))

(defun-sk pb08b2-supremum-exists-p (real-type set)
  (exists (supremum)
    (and
     (pb08b2-real-p real-type supremum)
     (pb08b2-least-upper-bound-p
      real-type set supremum))))

(defun-sk pb08b2-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (pb08b2-valid-real-set-p real-type set)
      (pb08b2-set-nonempty-p real-type set)
      (pb08b2-set-bounded-above-p real-type set))
     (pb08b2-supremum-exists-p real-type set))))

(defun pb08b2-real-natural (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (pb08b2-zero real-type)
    (pb08b2-add
     real-type
     (pb08b2-one real-type)
     (pb08b2-real-natural real-type (1- n)))))

(defun-sk pb08b2-archimedean-bound-exists-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (pb08b2-less
      real-type value
      (pb08b2-real-natural real-type n)))))

(defun-sk pb08b2-archimedean-p (real-type)
  (forall (value)
    (implies
     (pb08b2-real-p real-type value)
     (pb08b2-archimedean-bound-exists-p
      real-type value))))

(defun pb08b2-real-structure-p (real-type)
  (and
   (pb08b2-operation-closure-p real-type)
   (pb08b2-unary-field-laws-p real-type)
   (pb08b2-binary-field-laws-p real-type)
   (pb08b2-ternary-field-laws-p real-type)
   (pb08b2-order-laws-p real-type)
   (not
    (equal
     (pb08b2-zero real-type)
     (pb08b2-one real-type)))
   (pb08b2-less
    real-type
    (pb08b2-zero real-type)
    (pb08b2-one real-type))
   (pb08b2-dedekind-complete-p real-type)
   (pb08b2-archimedean-p real-type)))

;; Tagged divisions and gauge integrals provide an exact definition of every
;; integral occurring in the logarithm and repeated-integration assumptions.

(defun pb08b2-in-closed-interval-p
    (real-type left right value)
  (and
   (pb08b2-real-p real-type value)
   (pb08b2-leq real-type left value)
   (pb08b2-leq real-type value right)))

(defun pb08b2-tagged-piece-p (real-type piece)
  (and
   (true-listp piece)
   (equal (len piece) 3)
   (pb08b2-real-p real-type (nth 0 piece))
   (pb08b2-real-p real-type (nth 1 piece))
   (pb08b2-real-p real-type (nth 2 piece))
   (pb08b2-less
    real-type (nth 1 piece) (nth 2 piece))
   (pb08b2-leq
    real-type (nth 1 piece) (nth 0 piece))
   (pb08b2-leq
    real-type (nth 0 piece) (nth 2 piece))))

(defun pb08b2-tagged-division-tail-p
    (real-type division next-left right)
  (if (endp division)
      (equal next-left right)
    (let ((piece (car division)))
      (and
       (pb08b2-tagged-piece-p real-type piece)
       (equal (nth 1 piece) next-left)
       (pb08b2-tagged-division-tail-p
        real-type
        (cdr division)
        (nth 2 piece)
        right)))))

(defun pb08b2-tagged-division-p
    (real-type left right division)
  (and
   (true-listp division)
   (pb08b2-real-p real-type left)
   (pb08b2-real-p real-type right)
   (pb08b2-leq real-type left right)
   (pb08b2-tagged-division-tail-p
    real-type division left right)))

(defun-sk pb08b2-positive-gauge-p
    (real-type gauge left right)
  (forall (x)
    (implies
     (pb08b2-in-closed-interval-p
      real-type left right x)
     (and
      (pb08b2-real-p
       real-type
       (pb08b2-gauge-value real-type gauge x))
      (pb08b2-less
       real-type
       (pb08b2-zero real-type)
       (pb08b2-gauge-value real-type gauge x))))))

(defun pb08b2-fine-tagged-division-p
    (real-type gauge division)
  (if (endp division)
      t
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece))
           (radius
            (pb08b2-gauge-value real-type gauge tag)))
      (and
       (pb08b2-less
        real-type
        (pb08b2-subtract real-type tag left)
        radius)
       (pb08b2-less
        real-type
        (pb08b2-subtract real-type right tag)
        radius)
       (pb08b2-fine-tagged-division-p
        real-type gauge (cdr division))))))

(defun-sk pb08b2-fine-division-exists-p
    (real-type gauge left right)
  (exists (division)
    (and
     (pb08b2-tagged-division-p
      real-type left right division)
     (pb08b2-fine-tagged-division-p
      real-type gauge division))))

(defun pb08b2-family-riemann-sum
    (real-type family n division)
  (if (endp division)
      (pb08b2-zero real-type)
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece)))
      (pb08b2-add
       real-type
       (pb08b2-multiply
        real-type
        (pb08b2-family-value
         real-type family n tag)
        (pb08b2-subtract real-type right left))
       (pb08b2-family-riemann-sum
        real-type family n (cdr division))))))

(defun-sk pb08b2-all-family-sums-close-p
    (real-type family n integral gauge left right epsilon)
  (forall (division)
    (implies
     (and
      (pb08b2-tagged-division-p
       real-type left right division)
      (pb08b2-fine-tagged-division-p
       real-type gauge division))
     (pb08b2-less
      real-type
      (pb08b2-absolute-value
       real-type
       (pb08b2-subtract
        real-type
        (pb08b2-family-riemann-sum
         real-type family n division)
        integral))
      epsilon))))

(defun-sk pb08b2-family-integral-gauge-exists-p
    (real-type family n integral left right epsilon)
  (exists (gauge)
    (and
     (pb08b2-positive-gauge-p
      real-type gauge left right)
     (pb08b2-fine-division-exists-p
      real-type gauge left right)
     (pb08b2-all-family-sums-close-p
      real-type family n integral gauge
      left right epsilon))))

(defun-sk pb08b2-family-has-integral-p
    (real-type family n integral left right)
  (forall (epsilon)
    (implies
     (pb08b2-positive-real-p real-type epsilon)
     (pb08b2-family-integral-gauge-exists-p
      real-type family n integral
      left right epsilon))))

;; On every positive interval, the logarithm is characterized by the gauge
;; integral of the reciprocal function. The reversed case gives the usual
;; signed integral from 1 to x when 0 < x < 1.

(defun pb08b2-reciprocal-riemann-sum
    (real-type division)
  (if (endp division)
      (pb08b2-zero real-type)
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece)))
      (pb08b2-add
       real-type
       (pb08b2-multiply
        real-type
        (pb08b2-inverse real-type tag)
        (pb08b2-subtract real-type right left))
       (pb08b2-reciprocal-riemann-sum
        real-type (cdr division))))))

(defun-sk pb08b2-all-reciprocal-sums-close-p
    (real-type integral gauge left right epsilon)
  (forall (division)
    (implies
     (and
      (pb08b2-tagged-division-p
       real-type left right division)
      (pb08b2-fine-tagged-division-p
       real-type gauge division))
     (pb08b2-less
      real-type
      (pb08b2-absolute-value
       real-type
       (pb08b2-subtract
        real-type
        (pb08b2-reciprocal-riemann-sum
         real-type division)
        integral))
      epsilon))))

(defun-sk pb08b2-reciprocal-integral-gauge-exists-p
    (real-type integral left right epsilon)
  (exists (gauge)
    (and
     (pb08b2-positive-gauge-p
      real-type gauge left right)
     (pb08b2-fine-division-exists-p
      real-type gauge left right)
     (pb08b2-all-reciprocal-sums-close-p
      real-type integral gauge left right epsilon))))

(defun-sk pb08b2-reciprocal-has-integral-p
    (real-type integral left right)
  (forall (epsilon)
    (implies
     (pb08b2-positive-real-p real-type epsilon)
     (pb08b2-reciprocal-integral-gauge-exists-p
      real-type integral left right epsilon))))

(defun-sk pb08b2-logarithm-real-valued-p (real-type)
  (forall (x)
    (implies
     (pb08b2-real-p real-type x)
     (pb08b2-real-p
      real-type (pb08b2-logarithm real-type x)))))

(defun-sk pb08b2-logarithm-positive-definition-p
    (real-type)
  (forall (x)
    (implies
     (pb08b2-positive-real-p real-type x)
     (if (pb08b2-leq
          real-type (pb08b2-one real-type) x)
         (pb08b2-reciprocal-has-integral-p
          real-type
          (pb08b2-logarithm real-type x)
          (pb08b2-one real-type)
          x)
       (pb08b2-reciprocal-has-integral-p
        real-type
        (pb08b2-negate
         real-type (pb08b2-logarithm real-type x))
        x
        (pb08b2-one real-type))))))

(defun pb08b2-logarithm-laws-p (real-type)
  (and
   (pb08b2-logarithm-real-valued-p real-type)
   (pb08b2-logarithm-positive-definition-p real-type)))

;; The family remains arbitrary. These predicates state exactly the source
;; base equation and the integral recurrence, rather than defining F_n(1)
;; through a closed form derived from them.

(defun-sk pb08b2-real-family-p (real-type family)
  (forall (n x)
    (implies
     (and
      (natp n)
      (pb08b2-real-p real-type x))
     (pb08b2-real-p
      real-type
      (pb08b2-family-value
       real-type family n x)))))

(defun-sk pb08b2-family-base-p (real-type family)
  (forall (x)
    (implies
     (pb08b2-real-p real-type x)
     (equal
      (pb08b2-family-value real-type family 0 x)
      (pb08b2-logarithm real-type x)))))

(defun-sk pb08b2-family-recurrence-p
    (real-type family)
  (forall (n x)
    (implies
     (and
      (natp n)
      (pb08b2-positive-real-p real-type x))
     (pb08b2-family-has-integral-p
      real-type
      family
      n
      (pb08b2-family-value
       real-type family (+ n 1) x)
      (pb08b2-zero real-type)
      x))))

(defun pb08b2-real-factorial (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (pb08b2-one real-type)
    (pb08b2-multiply
     real-type
     (pb08b2-real-natural real-type n)
     (pb08b2-real-factorial real-type (1- n)))))

(defun pb08b2-normalized-value
    (real-type family n)
  (pb08b2-divide
   real-type
   (pb08b2-multiply
    real-type
    (pb08b2-real-factorial real-type n)
    (pb08b2-family-value
     real-type family n (pb08b2-one real-type)))
   (pb08b2-logarithm
    real-type (pb08b2-real-natural real-type n))))

;; The source limit is kept in its original existential epsilon-tail form.

(defun-sk pb08b2-limit-tail-p
    (real-type family epsilon start)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp start)
      (<= start n))
     (pb08b2-less
      real-type
      (pb08b2-absolute-value
       real-type
       (pb08b2-subtract
        real-type
        (pb08b2-normalized-value
         real-type family n)
        (pb08b2-negate
         real-type (pb08b2-one real-type))))
      epsilon))))

(defun-sk pb08b2-limit-start-exists-p
    (real-type family epsilon)
  (exists (start)
    (and
     (natp start)
     (pb08b2-limit-tail-p
      real-type family epsilon start))))

(defun-sk pb08b2-converges-to-minus-one-p
    (real-type family)
  (forall (epsilon)
    (implies
     (pb08b2-positive-real-p real-type epsilon)
     (pb08b2-limit-start-exists-p
      real-type family epsilon))))

(defun-sk putnambench-putnam-2008-b2-statement ()
  (forall (real-type family)
    (implies
     (and
      (pb08b2-real-structure-p real-type)
      (pb08b2-logarithm-laws-p real-type)
      (pb08b2-real-family-p real-type family)
      (pb08b2-family-base-p real-type family)
      (pb08b2-family-recurrence-p real-type family))
     (pb08b2-converges-to-minus-one-p
      real-type family))))

(value-triple :itpeval-statement-checked)
:q
