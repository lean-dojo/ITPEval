;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_a3:
;; nonexistence of a finite real limit for an exponential times an iterated
;; real integral. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The interfaces below present the real numbers as an arbitrary complete
;; ordered field.  Formula-specific DEFUN-SK binders supply the mathematical
;; quantifiers; no finite carrier, table of values, or sampled approximation
;; is used.

(defstub p81a3-real-p (r-type value) t)
(defstub p81a3-zero (r-type) t)
(defstub p81a3-one (r-type) t)
(defstub p81a3-add (r-type left right) t)
(defstub p81a3-mul (r-type left right) t)
(defstub p81a3-neg (r-type value) t)
(defstub p81a3-inv (r-type value) t)
(defstub p81a3-lt (r-type left right) t)
(defstub p81a3-set-member-p (r-type set value) t)

;; These three operations are constrained below by exact definitions:
;; the exponential by its real power series and the two integral operations
;; by convergence of uniform midpoint Riemann sums.

(defstub p81a3-exp (r-type value) t)
(defstub p81a3-inner-integral (r-type time y) t)
(defstub p81a3-outer-integral (r-type time) t)

(defun p81a3-sub (r-type x y)
  (p81a3-add r-type x (p81a3-neg r-type y)))

(defun p81a3-div (r-type x y)
  (p81a3-mul r-type x (p81a3-inv r-type y)))

(defun p81a3-le (r-type x y)
  (not (p81a3-lt r-type y x)))

(defun p81a3-abs (r-type x)
  (if (p81a3-lt r-type x (p81a3-zero r-type))
      (p81a3-neg r-type x)
    x))

(defun p81a3-in-closed-interval-p (r-type a b x)
  (and (p81a3-real-p r-type x)
       (p81a3-le r-type a x)
       (p81a3-le r-type x b)))

;; Complete ordered-field laws for the real carrier.

(defun-sk p81a3-operation-closure-p (r-type)
  (forall (x y)
    (and
     (p81a3-real-p r-type (p81a3-zero r-type))
     (p81a3-real-p r-type (p81a3-one r-type))
     (implies
      (p81a3-real-p r-type x)
      (and
       (p81a3-real-p r-type (p81a3-neg r-type x))
       (p81a3-real-p r-type (p81a3-inv r-type x))))
     (implies
      (and (p81a3-real-p r-type x)
           (p81a3-real-p r-type y))
      (and
       (p81a3-real-p r-type (p81a3-add r-type x y))
       (p81a3-real-p r-type (p81a3-mul r-type x y)))))))

(defun-sk p81a3-unary-field-laws-p (r-type)
  (forall (x)
    (implies
     (p81a3-real-p r-type x)
     (let ((zero (p81a3-zero r-type))
           (one (p81a3-one r-type)))
       (and
        (equal (p81a3-add r-type zero x) x)
        (equal (p81a3-add r-type x zero) x)
        (equal (p81a3-add r-type x (p81a3-neg r-type x)) zero)
        (equal (p81a3-add r-type (p81a3-neg r-type x) x) zero)
        (equal (p81a3-mul r-type one x) x)
        (equal (p81a3-mul r-type x one) x)
        (implies
         (not (equal x zero))
         (and
          (equal (p81a3-mul r-type x (p81a3-inv r-type x)) one)
          (equal (p81a3-mul r-type (p81a3-inv r-type x) x) one))))))))

(defun-sk p81a3-binary-field-laws-p (r-type)
  (forall (x y)
    (implies
     (and (p81a3-real-p r-type x)
          (p81a3-real-p r-type y))
     (and
      (equal (p81a3-add r-type x y)
             (p81a3-add r-type y x))
      (equal (p81a3-mul r-type x y)
             (p81a3-mul r-type y x))))))

(defun-sk p81a3-ternary-field-laws-p (r-type)
  (forall (x y z)
    (implies
     (and (p81a3-real-p r-type x)
          (p81a3-real-p r-type y)
          (p81a3-real-p r-type z))
     (and
      (equal
       (p81a3-add r-type (p81a3-add r-type x y) z)
       (p81a3-add r-type x (p81a3-add r-type y z)))
      (equal
       (p81a3-mul r-type (p81a3-mul r-type x y) z)
       (p81a3-mul r-type x (p81a3-mul r-type y z)))
      (equal
       (p81a3-mul r-type x (p81a3-add r-type y z))
       (p81a3-add
        r-type
        (p81a3-mul r-type x y)
        (p81a3-mul r-type x z)))))))

(defun-sk p81a3-order-laws-p (r-type)
  (forall (x y z)
    (implies
     (and (p81a3-real-p r-type x)
          (p81a3-real-p r-type y)
          (p81a3-real-p r-type z))
     (and
      (not (p81a3-lt r-type x x))
      (implies
       (and (p81a3-lt r-type x y)
            (p81a3-lt r-type y z))
       (p81a3-lt r-type x z))
      (or (p81a3-lt r-type x y)
          (equal x y)
          (p81a3-lt r-type y x))
      (implies
       (p81a3-lt r-type x y)
       (p81a3-lt
        r-type
        (p81a3-add r-type x z)
        (p81a3-add r-type y z)))
      (implies
       (and (p81a3-lt r-type (p81a3-zero r-type) x)
            (p81a3-lt r-type (p81a3-zero r-type) y))
       (p81a3-lt
        r-type
        (p81a3-zero r-type)
        (p81a3-mul r-type x y)))))))

(defun-sk p81a3-valid-real-set-p (r-type set)
  (forall (x)
    (implies
     (p81a3-set-member-p r-type set x)
     (p81a3-real-p r-type x))))

(defun-sk p81a3-set-nonempty-p (r-type set)
  (exists (x)
    (and (p81a3-real-p r-type x)
         (p81a3-set-member-p r-type set x))))

(defun-sk p81a3-upper-bound-p (r-type set bound)
  (forall (x)
    (implies
     (p81a3-set-member-p r-type set x)
     (p81a3-le r-type x bound))))

(defun-sk p81a3-set-bounded-above-p (r-type set)
  (exists (bound)
    (and (p81a3-real-p r-type bound)
         (p81a3-upper-bound-p r-type set bound))))

(defun-sk p81a3-least-upper-bound-p (r-type set supremum)
  (forall (bound)
    (and
     (p81a3-real-p r-type supremum)
     (p81a3-upper-bound-p r-type set supremum)
     (implies
      (and (p81a3-real-p r-type bound)
           (p81a3-upper-bound-p r-type set bound))
      (p81a3-le r-type supremum bound)))))

(defun-sk p81a3-supremum-exists-p (r-type set)
  (exists (supremum)
    (and (p81a3-real-p r-type supremum)
         (p81a3-least-upper-bound-p r-type set supremum))))

(defun-sk p81a3-dedekind-complete-p (r-type)
  (forall (set)
    (implies
     (and (p81a3-valid-real-set-p r-type set)
          (p81a3-set-nonempty-p r-type set)
          (p81a3-set-bounded-above-p r-type set))
     (p81a3-supremum-exists-p r-type set))))

(defun p81a3-real-structure-p (r-type)
  (and
   (p81a3-operation-closure-p r-type)
   (p81a3-unary-field-laws-p r-type)
   (p81a3-binary-field-laws-p r-type)
   (p81a3-ternary-field-laws-p r-type)
   (p81a3-order-laws-p r-type)
   (not (equal (p81a3-zero r-type) (p81a3-one r-type)))
   (p81a3-lt r-type (p81a3-zero r-type) (p81a3-one r-type))
   (p81a3-dedekind-complete-p r-type)))

;; Natural numerals, powers, factorials, and partial sums are interpreted
;; inside the presented real field.  The exponential interface is exactly
;; the limit of sum_{k < n} x^k/k!, not an uninterpreted token.

(defun p81a3-real-nat (r-type n)
  (if (zp n)
      (p81a3-zero r-type)
    (p81a3-add r-type
               (p81a3-one r-type)
               (p81a3-real-nat r-type (1- n)))))

(defun-sk p81a3-archimedean-witness-p (r-type x)
  (exists (n)
    (and
     (natp n)
     (p81a3-lt
      r-type x (p81a3-real-nat r-type n)))))

(defun-sk p81a3-archimedean-p (r-type)
  (forall (x)
    (implies
     (p81a3-real-p r-type x)
     (p81a3-archimedean-witness-p r-type x))))

(defun p81a3-power (r-type x n)
  (if (zp n)
      (p81a3-one r-type)
    (p81a3-mul r-type x (p81a3-power r-type x (1- n)))))

(defun p81a3-factorial (r-type n)
  (if (zp n)
      (p81a3-one r-type)
    (p81a3-mul
     r-type
     (p81a3-real-nat r-type n)
     (p81a3-factorial r-type (1- n)))))

(defun p81a3-exp-prefix (r-type x n)
  (if (zp n)
      (p81a3-zero r-type)
    (let ((k (1- n)))
      (p81a3-add
       r-type
       (p81a3-exp-prefix r-type x k)
       (p81a3-div
        r-type
        (p81a3-power r-type x k)
        (p81a3-factorial r-type k))))))

(defun-sk p81a3-exp-tail-p (r-type x epsilon cutoff)
  (forall (n)
    (implies
     (and (natp n)
          (<= cutoff n))
     (p81a3-lt
      r-type
      (p81a3-abs
       r-type
       (p81a3-sub
        r-type
        (p81a3-exp-prefix r-type x n)
        (p81a3-exp r-type x)))
      epsilon))))

(defun-sk p81a3-exp-cutoff-exists-p (r-type x epsilon)
  (exists (cutoff)
    (and (natp cutoff)
         (p81a3-exp-tail-p r-type x epsilon cutoff))))

(defun-sk p81a3-exp-operation-p (r-type)
  (forall (x epsilon)
    (and
     (implies
      (p81a3-real-p r-type x)
      (p81a3-real-p r-type (p81a3-exp r-type x)))
     (implies
      (and (p81a3-real-p r-type x)
           (p81a3-real-p r-type epsilon)
           (p81a3-lt r-type (p81a3-zero r-type) epsilon))
      (p81a3-exp-cutoff-exists-p r-type x epsilon)))))

;; Lean's totalized real division makes the displayed quotient zero on the
;; diagonal.  This definition records that value explicitly.

(defun p81a3-divided-difference (r-type x y)
  (if (equal x y)
      (p81a3-zero r-type)
    (p81a3-div
     r-type
     (p81a3-sub r-type
                (p81a3-exp r-type x)
                (p81a3-exp r-type y))
     (p81a3-sub r-type x y))))

;; Uniform midpoint sums give a concrete, nonvacuous Cauchy name for each
;; compact-interval integral. The isolated diagonal value changes no limit.

(defun p81a3-midpoint
    (r-type a b index subdivisions)
  (p81a3-add
   r-type
   a
   (p81a3-mul
    r-type
    (p81a3-sub r-type b a)
    (p81a3-div
     r-type
     (p81a3-real-nat r-type (+ (* 2 index) 1))
     (p81a3-real-nat r-type (* 2 subdivisions))))))

(defun p81a3-inner-midpoint-sum-aux
    (r-type time y remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p81a3-zero r-type)
    (let* ((index (- remaining 1))
           (x (p81a3-midpoint
               r-type
               (p81a3-zero r-type)
               time
               index
               subdivisions))
           (width
            (p81a3-div
             r-type
             time
             (p81a3-real-nat r-type subdivisions))))
      (p81a3-add
       r-type
       (p81a3-mul
        r-type
        (p81a3-divided-difference r-type x y)
        width)
       (p81a3-inner-midpoint-sum-aux
        r-type time y index subdivisions)))))

(defun p81a3-inner-riemann-sum
    (r-type time y subdivisions)
  (if (posp subdivisions)
      (p81a3-inner-midpoint-sum-aux
       r-type time y subdivisions subdivisions)
    (p81a3-zero r-type)))

(defun-sk p81a3-inner-sums-tail-p
    (r-type time y integral epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (p81a3-lt
      r-type
      (p81a3-abs
       r-type
       (p81a3-sub
        r-type
        (p81a3-inner-riemann-sum
         r-type time y subdivisions)
        integral))
      epsilon))))

(defun-sk p81a3-inner-cutoff-exists-p
    (r-type time y integral epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p81a3-inner-sums-tail-p
      r-type time y integral epsilon cutoff))))

(defun-sk p81a3-inner-sums-converge-p
    (r-type time y integral)
  (forall (epsilon)
    (implies
     (and
      (p81a3-real-p r-type epsilon)
      (p81a3-lt r-type (p81a3-zero r-type) epsilon))
     (p81a3-inner-cutoff-exists-p
      r-type time y integral epsilon))))

(defun p81a3-has-inner-integral-p
    (r-type time y integral)
  (and
   (p81a3-real-p r-type integral)
   (p81a3-inner-sums-converge-p
    r-type time y integral)))

(defun-sk p81a3-inner-integral-operation-p (r-type)
  (forall (time y)
    (implies
     (and
      (p81a3-in-closed-interval-p
       r-type (p81a3-zero r-type) time y))
     (and
      (p81a3-real-p r-type (p81a3-inner-integral r-type time y))
      (p81a3-has-inner-integral-p
       r-type time y (p81a3-inner-integral r-type time y))))))

(defun p81a3-outer-midpoint-sum-aux
    (r-type time remaining subdivisions)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p81a3-zero r-type)
    (let* ((index (- remaining 1))
           (y (p81a3-midpoint
               r-type
               (p81a3-zero r-type)
               time
               index
               subdivisions))
           (width
            (p81a3-div
             r-type
             time
             (p81a3-real-nat r-type subdivisions))))
      (p81a3-add
       r-type
       (p81a3-mul
        r-type
        (p81a3-inner-integral r-type time y)
        width)
       (p81a3-outer-midpoint-sum-aux
        r-type time index subdivisions)))))

(defun p81a3-outer-riemann-sum
    (r-type time subdivisions)
  (if (posp subdivisions)
      (p81a3-outer-midpoint-sum-aux
       r-type time subdivisions subdivisions)
    (p81a3-zero r-type)))

(defun-sk p81a3-outer-sums-tail-p
    (r-type time integral epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (natp subdivisions)
      (<= cutoff subdivisions))
     (p81a3-lt
      r-type
      (p81a3-abs
       r-type
       (p81a3-sub
        r-type
        (p81a3-outer-riemann-sum
         r-type time subdivisions)
        integral))
      epsilon))))

(defun-sk p81a3-outer-cutoff-exists-p
    (r-type time integral epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p81a3-outer-sums-tail-p
      r-type time integral epsilon cutoff))))

(defun-sk p81a3-outer-sums-converge-p
    (r-type time integral)
  (forall (epsilon)
    (implies
     (and
      (p81a3-real-p r-type epsilon)
      (p81a3-lt r-type (p81a3-zero r-type) epsilon))
     (p81a3-outer-cutoff-exists-p
      r-type time integral epsilon))))

(defun p81a3-has-outer-integral-p
    (r-type time integral)
  (and
   (p81a3-real-p r-type integral)
   (p81a3-outer-sums-converge-p
    r-type time integral)))

(defun-sk p81a3-outer-integral-operation-p (r-type)
  (forall (time)
    (implies
     (and
      (p81a3-real-p r-type time)
      (p81a3-le r-type (p81a3-zero r-type) time))
     (and
      (p81a3-real-p r-type (p81a3-outer-integral r-type time))
      (p81a3-has-outer-integral-p
       r-type time (p81a3-outer-integral r-type time))))))

;; On each compact interval these midpoint limits agree with the source
;; interval integrals for the displayed bounded integrands. The isolated
;; diagonal value is immaterial. For negative t the Lean half-open intervals
;; are empty; this branch therefore has value zero.

(defun p81a3-function-value (r-type time)
  (if (and
       (p81a3-real-p r-type time)
       (p81a3-le r-type (p81a3-zero r-type) time))
      (p81a3-mul
       r-type
       (p81a3-exp r-type (p81a3-neg r-type time))
       (p81a3-outer-integral r-type time))
    (p81a3-zero r-type)))

;; This is the ordinary epsilon definition of convergence to a finite real
;; limit as t tends to +infinity.  Both the candidate limit and the tail
;; threshold remain internally existential, as in the source proposition.

(defun-sk p81a3-limit-tail-p (r-type limit epsilon threshold)
  (forall (time)
    (implies
     (and
      (p81a3-real-p r-type time)
      (p81a3-le r-type threshold time))
     (p81a3-lt
      r-type
      (p81a3-abs
       r-type
       (p81a3-sub
        r-type
        (p81a3-function-value r-type time)
        limit))
      epsilon))))

(defun-sk p81a3-limit-threshold-exists-p
    (r-type limit epsilon)
  (exists (threshold)
    (and
     (p81a3-real-p r-type threshold)
     (p81a3-limit-tail-p
      r-type limit epsilon threshold))))

(defun-sk p81a3-tends-to-at-top-p (r-type limit)
  (forall (epsilon)
    (implies
     (and
      (p81a3-real-p r-type epsilon)
      (p81a3-lt r-type (p81a3-zero r-type) epsilon))
     (p81a3-limit-threshold-exists-p
      r-type limit epsilon))))

(defun-sk p81a3-finite-limit-exists-p (r-type)
  (exists (limit)
    (and
     (p81a3-real-p r-type limit)
     (p81a3-tends-to-at-top-p r-type limit))))

(defun p81a3-analysis-context-p (r-type)
  (and
   (p81a3-real-structure-p r-type)
   (p81a3-archimedean-p r-type)
   (p81a3-exp-operation-p r-type)
   (p81a3-inner-integral-operation-p r-type)
   (p81a3-outer-integral-operation-p r-type)))

;; The cataloged solution proposition is False.  Keeping the biconditional
;; explicit preserves the source statement rather than replacing it by a
;; preselected numerical witness or an asymptotic estimate.

(defun-sk putnambench-acl2-putnam-1981-a3-statement ()
  (forall (r-type)
    (implies
     (p81a3-analysis-context-p r-type)
     (iff (p81a3-finite-limit-exists-p r-type)
          nil))))

(value-triple :itpeval-statement-checked)

:q
