;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_a6:
;; 1/e is the greatest lower bound of the integral of |f'(x)-f(x)| over all
;; continuously differentiable real functions on [0,1] with f(0)=0 and
;; f(1)=1. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive real-number or real-function sort. Following
;; the corpus convention, conservative interfaces present an arbitrary complete
;; ordered field, its arbitrary real-valued functions, and its arbitrary sets.
;; Every field, order, completeness, function-typing, differentiability, and
;; integration condition used by the statement is explicit below.

(defstub p80a6-real-p (r-type value) t)
(defstub p80a6-zero (r-type) t)
(defstub p80a6-one (r-type) t)
(defstub p80a6-add (r-type left right) t)
(defstub p80a6-mul (r-type left right) t)
(defstub p80a6-neg (r-type value) t)
(defstub p80a6-inv (r-type value) t)
(defstub p80a6-lt (r-type left right) t)
(defstub p80a6-function-value (r-type function argument) t)
(defstub p80a6-set-member-p (r-type set value) t)

(defun p80a6-sub (r-type x y)
  (p80a6-add r-type x (p80a6-neg r-type y)))

(defun p80a6-le (r-type x y)
  (not (p80a6-lt r-type y x)))

(defun p80a6-abs (r-type x)
  (if (p80a6-lt r-type x (p80a6-zero r-type))
      (p80a6-neg r-type x)
    x))

(defun p80a6-in-closed-unit-interval-p (r-type x)
  (and
   (p80a6-real-p r-type x)
   (p80a6-le r-type (p80a6-zero r-type) x)
   (p80a6-le r-type x (p80a6-one r-type))))

;; Complete ordered-field presentation of the real carrier.

(defun-sk p80a6-operation-closure-p (r-type)
  (forall (x y)
    (and
     (p80a6-real-p r-type (p80a6-zero r-type))
     (p80a6-real-p r-type (p80a6-one r-type))
     (implies
      (p80a6-real-p r-type x)
      (and
       (p80a6-real-p r-type (p80a6-neg r-type x))
       (p80a6-real-p r-type (p80a6-inv r-type x))))
     (implies
      (and
       (p80a6-real-p r-type x)
       (p80a6-real-p r-type y))
      (and
       (p80a6-real-p r-type (p80a6-add r-type x y))
       (p80a6-real-p r-type (p80a6-mul r-type x y)))))))

(defun-sk p80a6-unary-field-laws-p (r-type)
  (forall (x)
    (implies
     (p80a6-real-p r-type x)
     (let ((zero (p80a6-zero r-type))
           (one (p80a6-one r-type)))
       (and
        (equal (p80a6-add r-type zero x) x)
        (equal (p80a6-add r-type x zero) x)
        (equal (p80a6-add r-type x (p80a6-neg r-type x)) zero)
        (equal (p80a6-add r-type (p80a6-neg r-type x) x) zero)
        (equal (p80a6-mul r-type one x) x)
        (equal (p80a6-mul r-type x one) x)
        (implies
         (not (equal x zero))
         (and
          (equal (p80a6-mul r-type x (p80a6-inv r-type x)) one)
          (equal (p80a6-mul r-type (p80a6-inv r-type x) x) one))))))))

(defun-sk p80a6-binary-field-laws-p (r-type)
  (forall (x y)
    (implies
     (and
      (p80a6-real-p r-type x)
      (p80a6-real-p r-type y))
     (and
      (equal
       (p80a6-add r-type x y)
       (p80a6-add r-type y x))
      (equal
       (p80a6-mul r-type x y)
       (p80a6-mul r-type y x))))))

(defun-sk p80a6-ternary-field-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (p80a6-real-p r-type x)
      (p80a6-real-p r-type y)
      (p80a6-real-p r-type z))
     (and
      (equal
       (p80a6-add r-type (p80a6-add r-type x y) z)
       (p80a6-add r-type x (p80a6-add r-type y z)))
      (equal
       (p80a6-mul r-type (p80a6-mul r-type x y) z)
       (p80a6-mul r-type x (p80a6-mul r-type y z)))
      (equal
       (p80a6-mul r-type x (p80a6-add r-type y z))
       (p80a6-add
        r-type
        (p80a6-mul r-type x y)
        (p80a6-mul r-type x z)))))))

(defun-sk p80a6-order-laws-p (r-type)
  (forall (x y z)
    (implies
     (and
      (p80a6-real-p r-type x)
      (p80a6-real-p r-type y)
      (p80a6-real-p r-type z))
     (and
      (not (p80a6-lt r-type x x))
      (implies
       (and
        (p80a6-lt r-type x y)
        (p80a6-lt r-type y z))
       (p80a6-lt r-type x z))
      (or
       (p80a6-lt r-type x y)
       (equal x y)
       (p80a6-lt r-type y x))
      (implies
       (p80a6-lt r-type x y)
       (p80a6-lt
        r-type
        (p80a6-add r-type x z)
        (p80a6-add r-type y z)))
      (implies
       (and
        (p80a6-lt r-type (p80a6-zero r-type) x)
        (p80a6-lt r-type (p80a6-zero r-type) y))
       (p80a6-lt
        r-type
        (p80a6-zero r-type)
        (p80a6-mul r-type x y)))))))

(defun-sk p80a6-valid-real-set-p (r-type set)
  (forall (x)
    (implies
     (p80a6-set-member-p r-type set x)
     (p80a6-real-p r-type x))))

(defun-sk p80a6-set-nonempty-p (r-type set)
  (exists (x)
    (and
     (p80a6-real-p r-type x)
     (p80a6-set-member-p r-type set x))))

(defun-sk p80a6-upper-bound-p (r-type set bound)
  (forall (x)
    (implies
     (p80a6-set-member-p r-type set x)
     (p80a6-le r-type x bound))))

(defun-sk p80a6-set-bounded-above-p (r-type set)
  (exists (bound)
    (and
     (p80a6-real-p r-type bound)
     (p80a6-upper-bound-p r-type set bound))))

(defun-sk p80a6-least-upper-bound-p
    (r-type set supremum)
  (forall (bound)
    (and
     (p80a6-real-p r-type supremum)
     (p80a6-upper-bound-p r-type set supremum)
     (implies
      (and
       (p80a6-real-p r-type bound)
       (p80a6-upper-bound-p r-type set bound))
      (p80a6-le r-type supremum bound)))))

(defun-sk p80a6-supremum-exists-p (r-type set)
  (exists (supremum)
    (and
     (p80a6-real-p r-type supremum)
     (p80a6-least-upper-bound-p
      r-type set supremum))))

(defun-sk p80a6-dedekind-complete-p (r-type)
  (forall (set)
    (implies
     (and
      (p80a6-valid-real-set-p r-type set)
      (p80a6-set-nonempty-p r-type set)
      (p80a6-set-bounded-above-p r-type set))
     (p80a6-supremum-exists-p r-type set))))

(defun p80a6-real-structure-p (r-type)
  (and
   (p80a6-operation-closure-p r-type)
   (p80a6-unary-field-laws-p r-type)
   (p80a6-binary-field-laws-p r-type)
   (p80a6-ternary-field-laws-p r-type)
   (p80a6-order-laws-p r-type)
   (not (equal (p80a6-zero r-type)
               (p80a6-one r-type)))
   (p80a6-lt
    r-type
    (p80a6-zero r-type)
    (p80a6-one r-type))
   (p80a6-dedekind-complete-p r-type)))

;; Exact characterization of e as the limit of sum_{k=0}^{n-1} 1/k!.

(defun p80a6-real-natural (r-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p80a6-zero r-type)
    (p80a6-add
     r-type
     (p80a6-one r-type)
     (p80a6-real-natural r-type (1- n)))))

(defun p80a6-real-factorial (r-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p80a6-one r-type)
    (p80a6-mul
     r-type
     (p80a6-real-natural r-type n)
     (p80a6-real-factorial r-type (1- n)))))

(defun p80a6-exp-partial-sum (r-type terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p80a6-zero r-type)
    (let ((index (1- terms)))
      (p80a6-add
       r-type
       (p80a6-exp-partial-sum r-type index)
       (p80a6-inv
        r-type
        (p80a6-real-factorial r-type index))))))

(defun-sk p80a6-exp-eventually-close-p
    (r-type e-value epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p80a6-lt
      r-type
      (p80a6-abs
       r-type
       (p80a6-sub
        r-type
        (p80a6-exp-partial-sum r-type terms)
        e-value))
      epsilon))))

(defun-sk p80a6-exp-cutoff-exists-p
    (r-type e-value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p80a6-exp-eventually-close-p
      r-type e-value epsilon cutoff))))

(defun-sk p80a6-exp-one-value-p (r-type e-value)
  (forall (epsilon)
    (implies
     (and
      (p80a6-real-p r-type epsilon)
      (p80a6-lt
       r-type
       (p80a6-zero r-type)
       epsilon))
     (p80a6-exp-cutoff-exists-p
      r-type e-value epsilon))))

;; Real-valued functions, continuity, and an interval-relative derivative.

(defun-sk p80a6-real-function-p (r-type function)
  (forall (x)
    (implies
     (p80a6-real-p r-type x)
     (p80a6-real-p
      r-type
      (p80a6-function-value r-type function x)))))

(defun-sk p80a6-continuity-neighborhood-p
    (r-type function x epsilon delta)
  (forall (y)
    (implies
     (and
      (p80a6-in-closed-unit-interval-p r-type y)
      (p80a6-lt
       r-type
       (p80a6-abs
        r-type
        (p80a6-sub r-type y x))
       delta))
     (p80a6-lt
      r-type
      (p80a6-abs
       r-type
       (p80a6-sub
        r-type
        (p80a6-function-value r-type function y)
        (p80a6-function-value r-type function x)))
      epsilon))))

(defun-sk p80a6-continuity-delta-exists-p
    (r-type function x epsilon)
  (exists (delta)
    (and
     (p80a6-real-p r-type delta)
     (p80a6-lt
      r-type
      (p80a6-zero r-type)
      delta)
     (p80a6-continuity-neighborhood-p
      r-type function x epsilon delta))))

(defun-sk p80a6-continuous-on-unit-interval-p
    (r-type function)
  (forall (x epsilon)
    (implies
     (and
      (p80a6-in-closed-unit-interval-p r-type x)
      (p80a6-real-p r-type epsilon)
      (p80a6-lt
       r-type
       (p80a6-zero r-type)
       epsilon))
     (p80a6-continuity-delta-exists-p
      r-type function x epsilon))))

(defun-sk p80a6-derivative-neighborhood-p
    (r-type function derivative x epsilon radius)
  (forall (y)
    (implies
     (and
      (p80a6-in-closed-unit-interval-p r-type y)
      (p80a6-lt
       r-type
       (p80a6-abs
        r-type
        (p80a6-sub r-type y x))
       radius))
     (p80a6-le
      r-type
      (p80a6-abs
       r-type
       (p80a6-sub
        r-type
        (p80a6-sub
         r-type
         (p80a6-function-value r-type function y)
         (p80a6-function-value r-type function x))
        (p80a6-mul
         r-type
         derivative
         (p80a6-sub r-type y x))))
      (p80a6-mul
       r-type
       epsilon
       (p80a6-abs
        r-type
        (p80a6-sub r-type y x)))))))

(defun-sk p80a6-derivative-radius-exists-p
    (r-type function derivative x epsilon)
  (exists (radius)
    (and
     (p80a6-real-p r-type radius)
     (p80a6-lt
      r-type
      (p80a6-zero r-type)
      radius)
     (p80a6-derivative-neighborhood-p
      r-type function derivative x epsilon radius))))

(defun-sk p80a6-has-derivative-within-p
    (r-type function derivative x)
  (forall (epsilon)
    (implies
     (and
      (p80a6-real-p r-type epsilon)
      (p80a6-lt
       r-type
       (p80a6-zero r-type)
       epsilon))
     (p80a6-derivative-radius-exists-p
      r-type function derivative x epsilon))))

(defun-sk p80a6-derivative-on-unit-interval-p
    (r-type function derivative-function)
  (forall (x)
    (implies
     (p80a6-in-closed-unit-interval-p r-type x)
     (p80a6-has-derivative-within-p
      r-type
      function
      (p80a6-function-value
       r-type derivative-function x)
      x))))

(defun p80a6-admissible-representation-p
    (r-type function derivative-function)
  (and
   (p80a6-real-function-p r-type function)
   (p80a6-real-function-p r-type derivative-function)
   (p80a6-derivative-on-unit-interval-p
    r-type function derivative-function)
   (p80a6-continuous-on-unit-interval-p
    r-type function)
   (p80a6-continuous-on-unit-interval-p
    r-type derivative-function)
   (equal
    (p80a6-function-value
     r-type function (p80a6-zero r-type))
    (p80a6-zero r-type))
   (equal
    (p80a6-function-value
     r-type function (p80a6-one r-type))
    (p80a6-one r-type))))

;; Gauge-integral definition for the continuous residual |f'-f|. On a compact
;; interval this equals the source interval Lebesgue integral.

(defun p80a6-residual-value
    (r-type function derivative-function x)
  (p80a6-abs
   r-type
   (p80a6-sub
    r-type
    (p80a6-function-value
     r-type derivative-function x)
    (p80a6-function-value r-type function x))))

(defun p80a6-tagged-piece-p (r-type piece)
  (and
   (true-listp piece)
   (equal (len piece) 3)
   (p80a6-real-p r-type (nth 0 piece))
   (p80a6-real-p r-type (nth 1 piece))
   (p80a6-real-p r-type (nth 2 piece))
   (p80a6-lt r-type (nth 1 piece) (nth 2 piece))
   (p80a6-le r-type (nth 1 piece) (nth 0 piece))
   (p80a6-le r-type (nth 0 piece) (nth 2 piece))))

(defun p80a6-tagged-division-tail-p
    (r-type division next-left)
  (if (endp division)
      (equal next-left (p80a6-one r-type))
    (let ((piece (car division)))
      (and
       (p80a6-tagged-piece-p r-type piece)
       (equal (nth 1 piece) next-left)
       (p80a6-tagged-division-tail-p
        r-type
        (cdr division)
        (nth 2 piece))))))

(defun p80a6-tagged-division-p (r-type division)
  (and
   (true-listp division)
   (p80a6-tagged-division-tail-p
    r-type division (p80a6-zero r-type))))

(defun p80a6-residual-riemann-sum
    (r-type function derivative-function division)
  (if (endp division)
      (p80a6-zero r-type)
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece)))
      (p80a6-add
       r-type
       (p80a6-mul
        r-type
        (p80a6-residual-value
         r-type function derivative-function tag)
        (p80a6-sub r-type right left))
       (p80a6-residual-riemann-sum
        r-type
        function
        derivative-function
        (cdr division))))))

(defun-sk p80a6-positive-gauge-p (r-type gauge)
  (forall (x)
    (implies
     (p80a6-in-closed-unit-interval-p r-type x)
     (p80a6-lt
      r-type
      (p80a6-zero r-type)
      (p80a6-function-value r-type gauge x)))))

(defun p80a6-fine-tagged-division-p
    (r-type gauge division)
  (if (endp division)
      t
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece))
           (gauge-at-tag
            (p80a6-function-value r-type gauge tag)))
      (and
       (p80a6-lt
        r-type
        (p80a6-sub r-type tag left)
        gauge-at-tag)
       (p80a6-lt
        r-type
        (p80a6-sub r-type right tag)
        gauge-at-tag)
       (p80a6-fine-tagged-division-p
        r-type gauge (cdr division))))))

(defun-sk p80a6-fine-division-exists-p
    (r-type gauge)
  (exists (division)
    (and
     (p80a6-tagged-division-p r-type division)
     (p80a6-fine-tagged-division-p
      r-type gauge division))))

(defun-sk p80a6-all-fine-sums-close-p
    (r-type function derivative-function
            integral gauge epsilon)
  (forall (division)
    (implies
     (and
      (p80a6-tagged-division-p r-type division)
      (p80a6-fine-tagged-division-p
       r-type gauge division))
     (p80a6-lt
      r-type
      (p80a6-abs
       r-type
       (p80a6-sub
        r-type
        (p80a6-residual-riemann-sum
         r-type function derivative-function division)
        integral))
      epsilon))))

(defun-sk p80a6-integral-gauge-exists-p
    (r-type function derivative-function
            integral epsilon)
  (exists (gauge)
    (and
     (p80a6-real-function-p r-type gauge)
     (p80a6-positive-gauge-p r-type gauge)
     (p80a6-fine-division-exists-p r-type gauge)
     (p80a6-all-fine-sums-close-p
      r-type
      function
      derivative-function
      integral
      gauge
      epsilon))))

(defun-sk p80a6-has-residual-integral-p
    (r-type function derivative-function integral)
  (forall (epsilon)
    (implies
     (and
      (p80a6-real-p r-type epsilon)
      (p80a6-lt
       r-type
       (p80a6-zero r-type)
       epsilon))
     (p80a6-integral-gauge-exists-p
      r-type
      function
      derivative-function
      integral
      epsilon))))

;; Direct characteristic predicate for the source set of real lower bounds,
;; followed by its greatest-element condition.

(defun-sk p80a6-lower-bound-p (r-type lower-bound)
  (forall (function derivative-function integral)
    (implies
     (and
      (p80a6-real-p r-type lower-bound)
      (p80a6-admissible-representation-p
       r-type function derivative-function)
      (p80a6-real-p r-type integral)
      (p80a6-has-residual-integral-p
       r-type function derivative-function integral))
     (p80a6-le r-type lower-bound integral))))

(defun-sk p80a6-dominates-all-lower-bounds-p
    (r-type greatest)
  (forall (lower-bound)
    (implies
     (and
      (p80a6-real-p r-type lower-bound)
      (p80a6-lower-bound-p r-type lower-bound))
     (p80a6-le r-type lower-bound greatest))))

(defun p80a6-greatest-lower-bound-p
    (r-type greatest)
  (and
   (p80a6-real-p r-type greatest)
   (p80a6-lower-bound-p r-type greatest)
   (p80a6-dominates-all-lower-bounds-p
    r-type greatest)))

(defun-sk putnambench-putnam-1980-a6-statement ()
  (forall (r-type e-value)
    (implies
     (and
      (p80a6-real-structure-p r-type)
      (p80a6-real-p r-type e-value)
      (p80a6-exp-one-value-p r-type e-value))
     (p80a6-greatest-lower-bound-p
      r-type
      (p80a6-inv r-type e-value)))))

(value-triple :itpeval-statement-checked)
:q
