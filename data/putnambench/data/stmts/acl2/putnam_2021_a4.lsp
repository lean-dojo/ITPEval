;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_a4:
;; the limit of a rational-function integral over expanding disks in the real
;; plane is (sqrt(2)/2) * pi * ln(2). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A tame APPLY$ presentation of a Dedekind-complete ordered field represents
;; the reals.  The named constants are fixed by the principal-square-root
;; condition and convergent series for pi and ln(2).  Uniform square-grid
;; Riemann sums with the disk indicator define the displayed two-dimensional
;; integral; for this continuous rational integrand they equal its disk
;; Lebesgue integral, and open versus closed disks have the same value.

(defun p21a4-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p21a4-unary-value (function x)
  (apply$ function (list x)))

(defun p21a4-binary-value (function x y)
  (apply$ function (list x y)))

(defun-sk p21a4-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p21a4-member-p carrier x))))

(defun-sk p21a4-real-function-p (carrier function)
  (forall (x)
    (implies
     (p21a4-member-p carrier x)
     (p21a4-member-p
      carrier
      (p21a4-unary-value function x)))))

(defun-sk p21a4-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p21a4-member-p carrier x)
      (p21a4-member-p carrier y)
      (p21a4-member-p carrier z))
     (and
      (p21a4-member-p carrier
                      (p21a4-binary-value add x y))
      (p21a4-member-p carrier
                      (p21a4-binary-value multiply x y))
      (p21a4-member-p carrier
                      (p21a4-unary-value negate x))
      (p21a4-member-p carrier
                      (p21a4-unary-value inverse x))
      (equal
       (p21a4-binary-value
        add (p21a4-binary-value add x y) z)
       (p21a4-binary-value
        add x (p21a4-binary-value add y z)))
      (equal
       (p21a4-binary-value add x y)
       (p21a4-binary-value add y x))
      (equal (p21a4-binary-value add x zero) x)
      (equal
       (p21a4-binary-value
        add x (p21a4-unary-value negate x))
       zero)
      (equal
       (p21a4-binary-value
        multiply (p21a4-binary-value multiply x y) z)
       (p21a4-binary-value
        multiply x (p21a4-binary-value multiply y z)))
      (equal
       (p21a4-binary-value multiply x y)
       (p21a4-binary-value multiply y x))
      (equal (p21a4-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p21a4-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p21a4-binary-value
         multiply x (p21a4-unary-value inverse x))
        one))
      (equal
       (p21a4-binary-value
        multiply x (p21a4-binary-value add y z))
       (p21a4-binary-value
        add
        (p21a4-binary-value multiply x y)
        (p21a4-binary-value multiply x z)))))))

(defun-sk p21a4-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p21a4-member-p carrier x)
      (p21a4-member-p carrier y)
      (p21a4-member-p carrier z))
     (and
      (not (p21a4-binary-value less x x))
      (or
       (equal x y)
       (p21a4-binary-value less x y)
       (p21a4-binary-value less y x))
      (implies
       (and
        (p21a4-binary-value less x y)
        (p21a4-binary-value less y z))
       (p21a4-binary-value less x z))
      (implies
       (p21a4-binary-value less x y)
       (p21a4-binary-value
        less
        (p21a4-binary-value add x z)
        (p21a4-binary-value add y z)))
      (implies
       (and
        (p21a4-binary-value less zero x)
        (p21a4-binary-value less zero y))
       (p21a4-binary-value
        less zero (p21a4-binary-value multiply x y)))))))

(defun-sk p21a4-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p21a4-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p21a4-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p21a4-member-p carrier x)
      (apply$ set (list x)))
     (not (p21a4-binary-value less bound x)))))

(defun-sk p21a4-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p21a4-member-p carrier bound)
     (p21a4-upper-bound-p carrier less set bound))))

(defun-sk p21a4-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (p21a4-member-p carrier bound)
      (p21a4-upper-bound-p carrier less set bound))
     (not (p21a4-binary-value less bound supremum)))))

(defun p21a4-supremum-p (carrier less set supremum)
  (and
   (p21a4-member-p carrier supremum)
   (p21a4-upper-bound-p carrier less set supremum)
   (p21a4-least-upper-bound-p
    carrier less set supremum)))

(defun-sk p21a4-has-supremum-p (carrier less set)
  (exists (supremum)
    (p21a4-supremum-p carrier less set supremum)))

(defun-sk p21a4-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p21a4-valid-set-p carrier set)
      (p21a4-set-nonempty-p carrier set)
      (p21a4-bounded-above-p carrier less set))
     (p21a4-has-supremum-p carrier less set))))

(defun p21a4-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p21a4-member-p carrier zero)
   (p21a4-member-p carrier one)
   (not (equal zero one))
   (p21a4-field-laws-p
    carrier add multiply negate inverse zero one)
   (p21a4-order-laws-p
    carrier add multiply zero less)
   (p21a4-binary-value less zero one)
   (p21a4-dedekind-complete-p carrier less)))

;; CTX is (carrier zero one add multiply negate inverse less
;;         sqrt-two pi-value ln-two).

(defun p21a4-carrier (ctx) (nth 0 ctx))
(defun p21a4-zero (ctx) (nth 1 ctx))
(defun p21a4-one (ctx) (nth 2 ctx))
(defun p21a4-add (ctx) (nth 3 ctx))
(defun p21a4-multiply (ctx) (nth 4 ctx))
(defun p21a4-negate (ctx) (nth 5 ctx))
(defun p21a4-inverse (ctx) (nth 6 ctx))
(defun p21a4-less (ctx) (nth 7 ctx))
(defun p21a4-sqrt-two (ctx) (nth 8 ctx))
(defun p21a4-pi-value (ctx) (nth 9 ctx))
(defun p21a4-ln-two (ctx) (nth 10 ctx))

(defun p21a4-r-add (ctx x y)
  (p21a4-binary-value (p21a4-add ctx) x y))

(defun p21a4-r-neg (ctx x)
  (p21a4-unary-value (p21a4-negate ctx) x))

(defun p21a4-r-sub (ctx x y)
  (p21a4-r-add ctx x (p21a4-r-neg ctx y)))

(defun p21a4-r-mul (ctx x y)
  (p21a4-binary-value (p21a4-multiply ctx) x y))

(defun p21a4-r-inv (ctx x)
  (p21a4-unary-value (p21a4-inverse ctx) x))

(defun p21a4-r-div (ctx x y)
  (p21a4-r-mul ctx x (p21a4-r-inv ctx y)))

(defun p21a4-r-lt-p (ctx x y)
  (if (p21a4-binary-value (p21a4-less ctx) x y) t nil))

(defun p21a4-r-le-p (ctx x y)
  (not (p21a4-r-lt-p ctx y x)))

(defun p21a4-r-abs (ctx x)
  (if (p21a4-r-lt-p ctx x (p21a4-zero ctx))
      (p21a4-r-neg ctx x)
    x))

(defun p21a4-positive-p (ctx x)
  (and
   (p21a4-member-p (p21a4-carrier ctx) x)
   (p21a4-r-lt-p ctx (p21a4-zero ctx) x)))

(defun p21a4-r-nat (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p21a4-zero ctx)
    (p21a4-r-add
     ctx
     (p21a4-one ctx)
     (p21a4-r-nat ctx (1- n)))))

(defun p21a4-r-pow (ctx x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p21a4-one ctx)
    (p21a4-r-mul
     ctx x (p21a4-r-pow ctx x (1- n)))))

;; Exact series names for pi (Machin's formula) and ln(2).

(defun p21a4-arctan-prefix (ctx z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p21a4-zero ctx)
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (term
            (p21a4-r-div
             ctx
             (p21a4-r-pow ctx z exponent)
             (p21a4-r-nat ctx exponent))))
      (p21a4-r-add
       ctx
       (p21a4-arctan-prefix ctx z index)
       (if (evenp index) term (p21a4-r-neg ctx term))))))

(defun p21a4-pi-prefix (ctx terms)
  (let* ((one-fifth
          (p21a4-r-inv ctx (p21a4-r-nat ctx 5)))
         (one-over-239
          (p21a4-r-inv ctx (p21a4-r-nat ctx 239))))
    (p21a4-r-sub
     ctx
     (p21a4-r-mul
      ctx
      (p21a4-r-nat ctx 16)
      (p21a4-arctan-prefix ctx one-fifth terms))
     (p21a4-r-mul
      ctx
      (p21a4-r-nat ctx 4)
      (p21a4-arctan-prefix ctx one-over-239 terms)))))

(defun p21a4-ln-two-prefix (ctx terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (p21a4-zero ctx)
    (let* ((index (1- terms))
           (denominator (p21a4-r-nat ctx (1+ index)))
           (term (p21a4-r-inv ctx denominator)))
      (p21a4-r-add
       ctx
       (p21a4-ln-two-prefix ctx index)
       (if (evenp index) term (p21a4-r-neg ctx term))))))

(defun p21a4-named-prefix (ctx name terms)
  (if (eq name 'pi)
      (p21a4-pi-prefix ctx terms)
    (p21a4-ln-two-prefix ctx terms)))

(defun-sk p21a4-named-series-tail-p
    (ctx name value epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (<= cutoff terms))
     (p21a4-r-lt-p
      ctx
      (p21a4-r-abs
       ctx
       (p21a4-r-sub
        ctx (p21a4-named-prefix ctx name terms) value))
      epsilon))))

(defun-sk p21a4-named-series-cutoff-exists-p
    (ctx name value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p21a4-named-series-tail-p
      ctx name value epsilon cutoff))))

(defun-sk p21a4-named-series-value-p (ctx name value)
  (forall (epsilon)
    (implies
     (p21a4-positive-p ctx epsilon)
     (p21a4-named-series-cutoff-exists-p
      ctx name value epsilon))))

(defun p21a4-sqrt-two-p (ctx)
  (and
   (p21a4-member-p
    (p21a4-carrier ctx) (p21a4-sqrt-two ctx))
   (p21a4-r-le-p
    ctx (p21a4-zero ctx) (p21a4-sqrt-two ctx))
   (equal
    (p21a4-r-mul
     ctx (p21a4-sqrt-two ctx) (p21a4-sqrt-two ctx))
    (p21a4-r-nat ctx 2))))

(defun p21a4-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 11)
   (p21a4-real-field-p
    (p21a4-carrier ctx)
    (p21a4-zero ctx)
    (p21a4-one ctx)
    (p21a4-add ctx)
    (p21a4-multiply ctx)
    (p21a4-negate ctx)
    (p21a4-inverse ctx)
    (p21a4-less ctx))
   (p21a4-sqrt-two-p ctx)
   (p21a4-member-p
    (p21a4-carrier ctx) (p21a4-pi-value ctx))
   (p21a4-positive-p ctx (p21a4-pi-value ctx))
   (p21a4-named-series-value-p
    ctx 'pi (p21a4-pi-value ctx))
   (p21a4-member-p
    (p21a4-carrier ctx) (p21a4-ln-two ctx))
   (p21a4-positive-p ctx (p21a4-ln-two ctx))
   (p21a4-named-series-value-p
    ctx 'ln-two (p21a4-ln-two ctx))))

;; The displayed integrand and its disk Riemann sums.

(defun p21a4-integrand (ctx x y)
  (let* ((one (p21a4-one ctx))
         (two (p21a4-r-nat ctx 2))
         (six (p21a4-r-nat ctx 6))
         (x2 (p21a4-r-pow ctx x 2))
         (y2 (p21a4-r-pow ctx y 2))
         (x4 (p21a4-r-pow ctx x 4))
         (y4 (p21a4-r-pow ctx y 4))
         (first-numerator
          (p21a4-r-add
           ctx one (p21a4-r-mul ctx two x2)))
         (first-denominator
          (p21a4-r-add
           ctx
           (p21a4-r-add ctx one x4)
           (p21a4-r-add
            ctx
            (p21a4-r-mul
             ctx six (p21a4-r-mul ctx x2 y2))
            y4)))
         (second-numerator
          (p21a4-r-add ctx one y2))
         (second-denominator
          (p21a4-r-add
           ctx (p21a4-r-add ctx two x4) y4)))
    (p21a4-r-sub
     ctx
     (p21a4-r-div ctx first-numerator first-denominator)
     (p21a4-r-div ctx second-numerator second-denominator))))

(defun p21a4-grid-coordinate (ctx bound width index)
  (p21a4-r-add
   ctx
   (p21a4-r-neg ctx bound)
   (p21a4-r-mul ctx (p21a4-r-nat ctx index) width)))

(defun p21a4-grid-cell
    (ctx radius-square bound width row column)
  (let* ((x (p21a4-grid-coordinate ctx bound width row))
         (y (p21a4-grid-coordinate ctx bound width column))
         (distance-square
          (p21a4-r-add
           ctx
           (p21a4-r-pow ctx x 2)
           (p21a4-r-pow ctx y 2))))
    (if (p21a4-r-le-p ctx distance-square radius-square)
        (p21a4-r-mul
         ctx
         (p21a4-r-mul ctx width width)
         (p21a4-integrand ctx x y))
      (p21a4-zero ctx))))

(defun p21a4-grid-row-sum
    (ctx radius-square bound width row columns)
  (declare (xargs :measure (nfix columns)))
  (if (zp columns)
      (p21a4-zero ctx)
    (let ((column (1- columns)))
      (p21a4-r-add
       ctx
       (p21a4-grid-row-sum
        ctx radius-square bound width row column)
       (p21a4-grid-cell
        ctx radius-square bound width row column)))))

(defun p21a4-grid-sum-rows
    (ctx radius-square bound width subdivisions rows)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      (p21a4-zero ctx)
    (let ((row (1- rows)))
      (p21a4-r-add
       ctx
       (p21a4-grid-sum-rows
        ctx radius-square bound width subdivisions row)
       (p21a4-grid-row-sum
        ctx radius-square bound width row subdivisions)))))

(defun p21a4-grid-sum (ctx radius subdivisions)
  (if (posp subdivisions)
      (let* ((bound (p21a4-r-abs ctx radius))
             (diameter
              (p21a4-r-mul ctx (p21a4-r-nat ctx 2) bound))
             (width
              (p21a4-r-div
               ctx diameter (p21a4-r-nat ctx subdivisions)))
             (radius-square (p21a4-r-pow ctx radius 2)))
        (p21a4-grid-sum-rows
         ctx radius-square bound width subdivisions subdivisions))
    (p21a4-zero ctx)))

(defun-sk p21a4-integral-tail-p
    (ctx radius value epsilon cutoff)
  (forall (subdivisions)
    (implies
     (and
      (posp subdivisions)
      (<= cutoff subdivisions))
     (p21a4-r-lt-p
      ctx
      (p21a4-r-abs
       ctx
       (p21a4-r-sub
        ctx
        (p21a4-grid-sum ctx radius subdivisions)
        value))
      epsilon))))

(defun-sk p21a4-integral-cutoff-exists-p
    (ctx radius value epsilon)
  (exists (cutoff)
    (and
     (posp cutoff)
     (p21a4-integral-tail-p
      ctx radius value epsilon cutoff))))

(defun-sk p21a4-disk-integral-p (ctx radius value)
  (forall (epsilon)
    (implies
     (p21a4-positive-p ctx epsilon)
     (p21a4-integral-cutoff-exists-p
      ctx radius value epsilon))))

(defun-sk p21a4-integral-definition-p (ctx integral-function)
  (forall (radius)
    (implies
     (p21a4-member-p (p21a4-carrier ctx) radius)
     (and
      (p21a4-member-p
       (p21a4-carrier ctx)
       (p21a4-unary-value integral-function radius))
      (p21a4-disk-integral-p
       ctx radius
       (p21a4-unary-value integral-function radius))))))

;; Epsilon definition of the real-parameter limit as radius tends to +infinity.

(defun p21a4-solution-value (ctx)
  (p21a4-r-mul
   ctx
   (p21a4-r-div
    ctx (p21a4-sqrt-two ctx) (p21a4-r-nat ctx 2))
   (p21a4-r-mul
    ctx (p21a4-pi-value ctx) (p21a4-ln-two ctx))))

(defun-sk p21a4-limit-tail-p
    (ctx integral-function limit epsilon cutoff)
  (forall (radius)
    (implies
     (and
      (p21a4-member-p (p21a4-carrier ctx) radius)
      (p21a4-r-le-p ctx cutoff radius))
     (p21a4-r-lt-p
      ctx
      (p21a4-r-abs
       ctx
       (p21a4-r-sub
        ctx
        (p21a4-unary-value integral-function radius)
        limit))
      epsilon))))

(defun-sk p21a4-limit-cutoff-exists-p
    (ctx integral-function limit epsilon)
  (exists (cutoff)
    (and
     (p21a4-member-p (p21a4-carrier ctx) cutoff)
     (p21a4-limit-tail-p
      ctx integral-function limit epsilon cutoff))))

(defun-sk p21a4-tends-at-top-p
    (ctx integral-function limit)
  (forall (epsilon)
    (implies
     (p21a4-positive-p ctx epsilon)
     (p21a4-limit-cutoff-exists-p
      ctx integral-function limit epsilon))))

(defun putnambench-putnam-2021-a4-statement
    (ctx integral-function)
  (implies
   (and
    (p21a4-context-p ctx)
    (tamep-functionp integral-function)
    (p21a4-real-function-p
     (p21a4-carrier ctx) integral-function)
    (p21a4-integral-definition-p
     ctx integral-function))
   (p21a4-tends-at-top-p
    ctx integral-function (p21a4-solution-value ctx))))

(value-triple :itpeval-statement-checked)
:q
