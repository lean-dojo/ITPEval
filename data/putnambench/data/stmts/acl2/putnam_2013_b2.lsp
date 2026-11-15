;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_b2:
;; the greatest attained value at zero of nonnegative real cosine polynomials
;; whose coefficients at multiples of three vanish is 3. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; CTX presents an arbitrary real-closed ordered field.  Real-closed fields
;; are elementarily equivalent, so the finite-coefficient statement below is
;; bidirectionally equivalent to the same statement over the real numbers;
;; no coefficient domain is narrowed to ACL2's rationals.
;;
;; For theta = 2*pi*x,
;;
;;   cos(n*theta) = T_n(cos(theta)),
;;
;; where T_n is the Chebyshev polynomial defined below.  As x ranges over the
;; reals, cos(2*pi*x) ranges over the entire interval [-1,1].  Consequently,
;; universal nonnegativity of the source cosine polynomial is exactly
;; universal nonnegativity of its Chebyshev form on [-1,1].  The final
;; predicate states IsGreatest at 3 as an internal attainment existential
;; together with the universal upper-bound condition.

(defun p13b2-apply1 (function argument)
  (apply$ function (list argument)))

(defun p13b2-apply2 (function left right)
  (apply$ function (list left right)))

(defun p13b2-carrier-p (ctx value)
  (if (p13b2-apply1 (nth 0 ctx) value) t nil))

(defun p13b2-zero (ctx)
  (nth 1 ctx))

(defun p13b2-one (ctx)
  (nth 2 ctx))

(defun p13b2-add-operation (ctx)
  (nth 3 ctx))

(defun p13b2-multiply-operation (ctx)
  (nth 4 ctx))

(defun p13b2-negate-operation (ctx)
  (nth 5 ctx))

(defun p13b2-inverse-operation (ctx)
  (nth 6 ctx))

(defun p13b2-less-operation (ctx)
  (nth 7 ctx))

(defun p13b2-add (ctx left right)
  (p13b2-apply2
   (p13b2-add-operation ctx) left right))

(defun p13b2-multiply (ctx left right)
  (p13b2-apply2
   (p13b2-multiply-operation ctx) left right))

(defun p13b2-negate (ctx value)
  (p13b2-apply1
   (p13b2-negate-operation ctx) value))

(defun p13b2-inverse (ctx value)
  (p13b2-apply1
   (p13b2-inverse-operation ctx) value))

(defun p13b2-less-p (ctx left right)
  (if (p13b2-apply2
       (p13b2-less-operation ctx) left right)
      t
    nil))

(defun p13b2-less-equal-p (ctx left right)
  (not (p13b2-less-p ctx right left)))

(defun-sk p13b2-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p13b2-carrier-p ctx x)
      (p13b2-carrier-p ctx y)
      (p13b2-carrier-p ctx z))
     (let* ((zero (p13b2-zero ctx))
            (one (p13b2-one ctx))
            (x-plus-y (p13b2-add ctx x y))
            (y-plus-z (p13b2-add ctx y z))
            (x-times-y (p13b2-multiply ctx x y))
            (y-times-z (p13b2-multiply ctx y z))
            (minus-x (p13b2-negate ctx x))
            (inverse-x (p13b2-inverse ctx x)))
       (and
        (p13b2-carrier-p ctx x-plus-y)
        (p13b2-carrier-p ctx x-times-y)
        (p13b2-carrier-p ctx minus-x)
        (p13b2-carrier-p ctx inverse-x)
        (equal
         (p13b2-add ctx x-plus-y z)
         (p13b2-add ctx x y-plus-z))
        (equal x-plus-y (p13b2-add ctx y x))
        (equal (p13b2-add ctx x zero) x)
        (equal (p13b2-add ctx x minus-x) zero)
        (equal
         (p13b2-multiply ctx x-times-y z)
         (p13b2-multiply ctx x y-times-z))
        (equal x-times-y (p13b2-multiply ctx y x))
        (equal (p13b2-multiply ctx x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p13b2-multiply ctx x inverse-x)
          one))
        (equal
         (p13b2-multiply ctx x y-plus-z)
         (p13b2-add
          ctx
          (p13b2-multiply ctx x y)
          (p13b2-multiply ctx x z))))))))

(defun-sk p13b2-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p13b2-carrier-p ctx x)
      (p13b2-carrier-p ctx y)
      (p13b2-carrier-p ctx z))
     (let ((zero (p13b2-zero ctx)))
       (and
        (not (p13b2-less-p ctx x x))
        (or
         (p13b2-less-p ctx x y)
         (equal x y)
         (p13b2-less-p ctx y x))
        (implies
         (and
          (p13b2-less-p ctx x y)
          (p13b2-less-p ctx y z))
         (p13b2-less-p ctx x z))
        (implies
         (p13b2-less-p ctx x y)
         (p13b2-less-p
          ctx
          (p13b2-add ctx x z)
          (p13b2-add ctx y z)))
        (implies
         (and
          (p13b2-less-p ctx zero x)
          (p13b2-less-p ctx zero y))
         (p13b2-less-p
          ctx
          zero
          (p13b2-multiply ctx x y))))))))

(defun p13b2-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (p13b2-carrier-p ctx (car coefficients))
       (p13b2-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun p13b2-polynomial-p (ctx coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p13b2-coefficient-list-p ctx coefficients)
   (not
    (equal
     (car (last coefficients))
     (p13b2-zero ctx)))))

(defun p13b2-polynomial-evaluate (ctx coefficients x)
  (if (consp coefficients)
      (p13b2-add
       ctx
       (car coefficients)
       (p13b2-multiply
        ctx
        x
        (p13b2-polynomial-evaluate
         ctx (cdr coefficients) x)))
    (p13b2-zero ctx)))

(defun-sk p13b2-positive-square-root-exists-p
    (ctx value)
  (exists (root)
    (and
     (p13b2-carrier-p ctx root)
     (equal
      (p13b2-multiply ctx root root)
      value))))

(defun-sk p13b2-positive-square-root-law-p (ctx)
  (forall (value)
    (implies
     (and
      (p13b2-carrier-p ctx value)
      (p13b2-less-p
       ctx (p13b2-zero ctx) value))
     (p13b2-positive-square-root-exists-p
      ctx value))))

(defun-sk p13b2-odd-polynomial-root-exists-p
    (ctx coefficients)
  (exists (root)
    (and
     (p13b2-carrier-p ctx root)
     (equal
      (p13b2-polynomial-evaluate
       ctx coefficients root)
      (p13b2-zero ctx)))))

(defun-sk p13b2-odd-polynomial-root-law-p (ctx)
  (forall (coefficients)
    (implies
     (and
      (p13b2-polynomial-p ctx coefficients)
      (evenp (len coefficients)))
     (p13b2-odd-polynomial-root-exists-p
      ctx coefficients))))

(defun p13b2-real-closed-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (nth 0 ctx))
   (tamep-functionp (nth 3 ctx))
   (tamep-functionp (nth 4 ctx))
   (tamep-functionp (nth 5 ctx))
   (tamep-functionp (nth 6 ctx))
   (tamep-functionp (nth 7 ctx))
   (p13b2-carrier-p ctx (p13b2-zero ctx))
   (p13b2-carrier-p ctx (p13b2-one ctx))
   (not (equal (p13b2-zero ctx) (p13b2-one ctx)))
   (p13b2-field-laws-p ctx)
   (p13b2-order-laws-p ctx)
   (p13b2-less-p
    ctx (p13b2-zero ctx) (p13b2-one ctx))
   (p13b2-positive-square-root-law-p ctx)
   (p13b2-odd-polynomial-root-law-p ctx)))

(defun p13b2-two (ctx)
  (p13b2-add ctx (p13b2-one ctx) (p13b2-one ctx)))

(defun p13b2-three (ctx)
  (p13b2-add ctx (p13b2-one ctx) (p13b2-two ctx)))

(defun p13b2-chebyshev (ctx degree x)
  (declare (xargs :measure (nfix degree)))
  (cond
   ((zp degree)
    (p13b2-one ctx))
   ((equal degree 1)
    x)
   (t
    (p13b2-add
     ctx
     (p13b2-multiply
      ctx
      (p13b2-multiply ctx (p13b2-two ctx) x)
      (p13b2-chebyshev ctx (- degree 1) x))
     (p13b2-negate
      ctx
      (p13b2-chebyshev ctx (- degree 2) x))))))

(defun p13b2-forbidden-zeroes-p
    (ctx coefficients index)
  (if (consp coefficients)
      (and
       (implies
        (equal (mod index 3) 0)
        (equal (car coefficients) (p13b2-zero ctx)))
       (p13b2-forbidden-zeroes-p
        ctx (cdr coefficients) (+ index 1)))
    (equal coefficients nil)))

(defun p13b2-eligible-coefficients-p
    (ctx degree coefficients)
  (and
   (posp degree)
   (true-listp coefficients)
   (equal (len coefficients) (+ degree 1))
   (p13b2-coefficient-list-p ctx coefficients)
   (p13b2-forbidden-zeroes-p ctx coefficients 0)))

(defun p13b2-cosine-polynomial-value
    (ctx coefficients degree cosine-value)
  (declare (xargs :measure (nfix degree)))
  (if (zp degree)
      (p13b2-one ctx)
    (p13b2-add
     ctx
     (p13b2-multiply
      ctx
      (nth degree coefficients)
      (p13b2-chebyshev ctx degree cosine-value))
     (p13b2-cosine-polynomial-value
      ctx coefficients (- degree 1) cosine-value))))

(defun-sk p13b2-nonnegative-p
    (ctx degree coefficients)
  (forall (cosine-value)
    (implies
     (and
      (p13b2-carrier-p ctx cosine-value)
      (p13b2-less-equal-p
       ctx
       (p13b2-negate ctx (p13b2-one ctx))
       cosine-value)
      (p13b2-less-equal-p
       ctx cosine-value (p13b2-one ctx)))
     (p13b2-less-equal-p
      ctx
      (p13b2-zero ctx)
      (p13b2-cosine-polynomial-value
       ctx coefficients degree cosine-value)))))

(defun-sk p13b2-three-is-attained-p (ctx)
  (exists (degree coefficients)
    (and
     (p13b2-eligible-coefficients-p
      ctx degree coefficients)
     (p13b2-nonnegative-p
      ctx degree coefficients)
     (equal
      (p13b2-cosine-polynomial-value
       ctx coefficients degree (p13b2-one ctx))
      (p13b2-three ctx)))))

(defun-sk p13b2-three-is-upper-bound-p (ctx)
  (forall (degree coefficients)
    (implies
     (and
      (p13b2-eligible-coefficients-p
       ctx degree coefficients)
      (p13b2-nonnegative-p
       ctx degree coefficients))
     (p13b2-less-equal-p
      ctx
      (p13b2-cosine-polynomial-value
       ctx coefficients degree (p13b2-one ctx))
      (p13b2-three ctx)))))

(defun putnambench-putnam-2013-b2-statement (ctx)
  (implies
   (p13b2-real-closed-field-p ctx)
   (and
    (p13b2-three-is-attained-p ctx)
    (p13b2-three-is-upper-bound-p ctx))))

(value-triple :itpeval-statement-checked)
:q
