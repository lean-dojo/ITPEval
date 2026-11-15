;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_a6:
;; the normalized real exponential integral over the triangle with vertices
;; (0,0), (a,0), and (0,a) tends to 2/9 as a tends to infinity.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Ordinary ACL2 has no native real-analysis type. These conservative
;; function symbols present one arbitrary real field and its exponential.
;; Every algebraic, order, completeness, and exponential law used to identify
;; that presentation with the real numbers is explicit in the statement.

(defstub p83a6-real-p (x) t)
(defstub p83a6-add (x y) t)
(defstub p83a6-mul (x y) t)
(defstub p83a6-neg (x) t)
(defstub p83a6-inv (x) t)
(defstub p83a6-lt (x y) t)
(defstub p83a6-exp (x) t)

(defun p83a6-zero () 0)
(defun p83a6-one () 1)

(defun p83a6-sub (x y)
  (p83a6-add x (p83a6-neg y)))

(defun p83a6-div (x y)
  (p83a6-mul x (p83a6-inv y)))

(defun p83a6-le (x y)
  (not (p83a6-lt y x)))

(defun p83a6-abs (x)
  (if (p83a6-lt x (p83a6-zero))
      (p83a6-neg x)
    x))

(defun p83a6-positive-real-p (x)
  (and
   (p83a6-real-p x)
   (p83a6-lt (p83a6-zero) x)))

(defun-sk p83a6-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p83a6-real-p x)
      (p83a6-real-p y)
      (p83a6-real-p z))
     (and
      (p83a6-real-p (p83a6-add x y))
      (p83a6-real-p (p83a6-mul x y))
      (p83a6-real-p (p83a6-neg x))
      (p83a6-real-p (p83a6-inv x))
      (equal
       (p83a6-add (p83a6-add x y) z)
       (p83a6-add x (p83a6-add y z)))
      (equal (p83a6-add x y)
             (p83a6-add y x))
      (equal (p83a6-add x (p83a6-zero)) x)
      (equal (p83a6-add x (p83a6-neg x))
             (p83a6-zero))
      (equal
       (p83a6-mul (p83a6-mul x y) z)
       (p83a6-mul x (p83a6-mul y z)))
      (equal (p83a6-mul x y)
             (p83a6-mul y x))
      (equal (p83a6-mul x (p83a6-one)) x)
      (implies
       (equal x (p83a6-zero))
       (equal (p83a6-inv x) (p83a6-zero)))
      (implies
       (not (equal x (p83a6-zero)))
       (equal
        (p83a6-mul x (p83a6-inv x))
        (p83a6-one)))
      (equal
       (p83a6-mul x (p83a6-add y z))
       (p83a6-add
        (p83a6-mul x y)
        (p83a6-mul x z)))))))

(defun-sk p83a6-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p83a6-real-p x)
      (p83a6-real-p y)
      (p83a6-real-p z))
     (and
      (not (p83a6-lt x x))
      (or
       (equal x y)
       (p83a6-lt x y)
       (p83a6-lt y x))
      (implies
       (and (p83a6-lt x y)
            (p83a6-lt y z))
       (p83a6-lt x z))
      (implies
       (p83a6-lt x y)
       (p83a6-lt
        (p83a6-add x z)
        (p83a6-add y z)))
      (implies
       (and
        (p83a6-lt (p83a6-zero) x)
        (p83a6-lt (p83a6-zero) y))
       (p83a6-lt
        (p83a6-zero)
        (p83a6-mul x y)))))))

;; Dedekind completeness ranges over ACL2 APPLY$ function objects representing
;; subsets of the carrier.

(defun-sk p83a6-valid-set-p (set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p83a6-real-p x))))

(defun-sk p83a6-set-nonempty-p (set)
  (exists (x)
    (and
     (p83a6-real-p x)
     (apply$ set (list x)))))

(defun-sk p83a6-upper-bound-p (set bound)
  (forall (x)
    (implies
     (and
      (p83a6-real-p x)
      (apply$ set (list x)))
     (p83a6-le x bound))))

(defun-sk p83a6-bounded-above-p (set)
  (exists (bound)
    (and
     (p83a6-real-p bound)
     (p83a6-upper-bound-p set bound))))

(defun-sk p83a6-least-upper-bound-p (set supremum)
  (forall (bound)
    (implies
     (and
      (p83a6-real-p bound)
      (p83a6-upper-bound-p set bound))
     (p83a6-le supremum bound))))

(defun p83a6-supremum-p (set supremum)
  (and
   (p83a6-real-p supremum)
   (p83a6-upper-bound-p set supremum)
   (p83a6-least-upper-bound-p set supremum)))

(defun-sk p83a6-has-supremum-p (set)
  (exists (supremum)
    (p83a6-supremum-p set supremum)))

(defun-sk p83a6-dedekind-complete-p ()
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p83a6-valid-set-p set)
      (p83a6-set-nonempty-p set)
      (p83a6-bounded-above-p set))
     (p83a6-has-supremum-p set))))

;; Requiring exp(0)=1 and exp'=exp under the epsilon-delta derivative below
;; characterizes the real exponential without a finite Taylor approximation.

(defun-sk p83a6-exp-derivative-neighborhood-p
    (x epsilon radius)
  (forall (z)
    (implies
     (and
      (p83a6-real-p z)
      (p83a6-lt
       (p83a6-abs (p83a6-sub z x))
       radius))
     (p83a6-le
      (p83a6-abs
       (p83a6-sub
        (p83a6-sub
         (p83a6-exp z)
         (p83a6-exp x))
        (p83a6-mul
         (p83a6-exp x)
         (p83a6-sub z x))))
      (p83a6-mul
       epsilon
       (p83a6-abs (p83a6-sub z x)))))))

(defun-sk p83a6-exp-derivative-radius-exists-p
    (x epsilon)
  (exists (radius)
    (and
     (p83a6-positive-real-p radius)
     (p83a6-exp-derivative-neighborhood-p
      x epsilon radius))))

(defun-sk p83a6-exp-has-derivative-p (x)
  (forall (epsilon)
    (implies
     (p83a6-positive-real-p epsilon)
     (p83a6-exp-derivative-radius-exists-p
      x epsilon))))

(defun-sk p83a6-exponential-derivative-values-p ()
  (forall (x)
    (implies
     (p83a6-real-p x)
     (p83a6-exp-has-derivative-p x))))

(defun-sk p83a6-exponential-typed-p ()
  (forall (x)
    (implies
     (p83a6-real-p x)
     (p83a6-real-p (p83a6-exp x)))))

(defun p83a6-real-context-p ()
  (and
   (p83a6-real-p (p83a6-zero))
   (p83a6-real-p (p83a6-one))
   (not (equal (p83a6-zero) (p83a6-one)))
   (p83a6-field-laws-p)
   (p83a6-order-laws-p)
   (p83a6-lt (p83a6-zero) (p83a6-one))
   (p83a6-dedekind-complete-p)
   (p83a6-exponential-typed-p)
   (equal (p83a6-exp (p83a6-zero))
          (p83a6-one))
   (p83a6-exponential-derivative-values-p)))

(defun p83a6-nat-cast (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p83a6-zero)
    (p83a6-add
     (p83a6-one)
     (p83a6-nat-cast (- n 1)))))

(defun p83a6-pow (x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p83a6-one)
    (p83a6-mul
     x
     (p83a6-pow x (- n 1)))))

(defun p83a6-grid-fraction (index subdivisions)
  (p83a6-div
   (p83a6-nat-cast index)
   (p83a6-nat-cast subdivisions)))

(defun p83a6-inner-grid-point
    (a x index subdivisions)
  (p83a6-mul
   (p83a6-sub a x)
   (p83a6-grid-fraction index subdivisions)))

(defun p83a6-integrand (x y)
  (p83a6-exp
   (p83a6-add
    (p83a6-pow x 3)
    (p83a6-pow y 3))))

(defun p83a6-inner-sum
    (a x subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p83a6-zero)
    (let ((y
           (p83a6-inner-grid-point
            a x remaining subdivisions)))
      (p83a6-add
       (p83a6-integrand x y)
       (p83a6-inner-sum
        a x subdivisions (- remaining 1))))))

(defun p83a6-inner-integral-approx
    (a x subdivisions)
  (p83a6-mul
   (p83a6-div
    (p83a6-sub a x)
    (p83a6-nat-cast subdivisions))
   (p83a6-inner-sum
    a x subdivisions subdivisions)))

(defun p83a6-outer-grid-point
    (a index subdivisions)
  (p83a6-mul
   a
   (p83a6-grid-fraction index subdivisions)))

(defun p83a6-outer-sum
    (a subdivisions remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p83a6-zero)
    (let ((x
           (p83a6-outer-grid-point
            a remaining subdivisions)))
      (p83a6-add
       (p83a6-inner-integral-approx
        a x subdivisions)
       (p83a6-outer-sum
        a subdivisions (- remaining 1))))))

;; For positive a this is the nested uniform right-endpoint Riemann sum for
;; integral_0^a integral_0^(a-x) exp(x^3+y^3) dy dx. The predicate below is
;; its unbounded limit, not a finite quadrature or an asserted error bound.

(defun p83a6-double-integral-approx
    (a subdivisions)
  (if (posp subdivisions)
      (p83a6-mul
       (p83a6-div
        a
        (p83a6-nat-cast subdivisions))
       (p83a6-outer-sum
        a subdivisions subdivisions))
    (p83a6-zero)))

(defun-sk p83a6-integral-tail-p
    (a integral epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p83a6-lt
      (p83a6-abs
       (p83a6-sub
        (p83a6-double-integral-approx
         a subdivisions)
        integral))
      epsilon))))

(defun-sk p83a6-integral-cutoff-exists-p
    (a integral epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p83a6-integral-tail-p
      a integral epsilon cutoff))))

(defun-sk p83a6-integral-converges-to-p
    (a integral)
  (forall (epsilon)
    (implies
     (p83a6-positive-real-p epsilon)
     (p83a6-integral-cutoff-exists-p
      a integral epsilon))))

(defun p83a6-integral-value-p (a integral)
  (and
   (p83a6-real-p integral)
   (p83a6-integral-converges-to-p
    a integral)))

(defun p83a6-normalized-value (a integral)
  (p83a6-mul
   (p83a6-div
    (p83a6-pow a 4)
    (p83a6-exp (p83a6-pow a 3)))
   integral))

(defun p83a6-solution ()
  (p83a6-div
   (p83a6-nat-cast 2)
   (p83a6-nat-cast 9)))

(defun-sk p83a6-value-close-at-p
    (a epsilon)
  (exists (integral)
    (and
     (p83a6-integral-value-p a integral)
     (p83a6-lt
      (p83a6-abs
       (p83a6-sub
        (p83a6-normalized-value a integral)
        (p83a6-solution)))
      epsilon))))

(defun-sk p83a6-limit-tail-p
    (epsilon threshold)
  (forall (a)
    (implies
     (and
      (p83a6-real-p a)
      (p83a6-le threshold a))
     (p83a6-value-close-at-p
      a epsilon))))

(defun-sk p83a6-limit-threshold-exists-p
    (epsilon)
  (exists (threshold)
    (and
     (p83a6-positive-real-p threshold)
     (p83a6-limit-tail-p
      epsilon threshold))))

(defun-sk p83a6-normalized-integral-tends-to-solution-p ()
  (forall (epsilon)
    (implies
     (p83a6-positive-real-p epsilon)
     (p83a6-limit-threshold-exists-p
      epsilon))))

(defun putnambench-putnam-1983-a6-statement ()
  (implies
   (p83a6-real-context-p)
   (p83a6-normalized-integral-tends-to-solution-p)))

(value-triple :itpeval-statement-checked)
:q
