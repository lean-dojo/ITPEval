;; Statement-only formalization of PutnamBench corpus artifact putnam_2006_b1:
;; the cubic curve x^3 + 3xy + y^3 = 1 has a unique three-point equilateral
;; subset, and its convex-hull area is 3*sqrt(3)/2. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The conservative operations below present an arbitrary real closed ordered
;; field. Real closed fields have the same first-order theory as the reals.
;; The named square-root operation is fixed by its nonnegative-root law, so the
;; displayed answer denotes exactly 3*sqrt(3)/2.
;;
;; A three-element set is represented extensionally by three pairwise distinct
;; points. Equality of such sets is membership in both directions, so coordinate
;; order is irrelevant. Equal squared side lengths are equivalent to the source
;; distance definition of equilateral. For three distinct equilateral points,
;; the Lebesgue measure of their convex hull is the standard triangle area
;; |det(B-A,C-A)|/2, used explicitly below.
;;
;; The final existential packages the source conjunction equivalently: it gives
;; an area-qualified triangle and says that every other equilateral triple on
;; the curve enumerates the same set. All point and competitor quantifiers remain
;; internal to DEFUN-SK.

(defstub p06b1-real-p (ctx value) t)
(defstub p06b1-zero (ctx) t)
(defstub p06b1-one (ctx) t)
(defstub p06b1-add-op (ctx left right) t)
(defstub p06b1-mul-op (ctx left right) t)
(defstub p06b1-neg-op (ctx value) t)
(defstub p06b1-inv-op (ctx value) t)
(defstub p06b1-less-op (ctx left right) t)
(defstub p06b1-sqrt-op (ctx value) t)

(defun p06b1-add (ctx left right)
  (p06b1-add-op ctx left right))

(defun p06b1-mul (ctx left right)
  (p06b1-mul-op ctx left right))

(defun p06b1-neg (ctx value)
  (p06b1-neg-op ctx value))

(defun p06b1-inv (ctx value)
  (p06b1-inv-op ctx value))

(defun p06b1-less-p (ctx left right)
  (if (p06b1-less-op ctx left right) t nil))

(defun p06b1-sqrt (ctx value)
  (p06b1-sqrt-op ctx value))

(defun p06b1-sub (ctx left right)
  (p06b1-add ctx left (p06b1-neg ctx right)))

(defun p06b1-div (ctx numerator denominator)
  (p06b1-mul ctx numerator (p06b1-inv ctx denominator)))

(defun p06b1-square (ctx value)
  (p06b1-mul ctx value value))

(defun p06b1-cube (ctx value)
  (p06b1-mul ctx (p06b1-square ctx value) value))

(defun p06b1-two (ctx)
  (p06b1-add ctx (p06b1-one ctx) (p06b1-one ctx)))

(defun p06b1-three (ctx)
  (p06b1-add ctx (p06b1-two ctx) (p06b1-one ctx)))

(defun p06b1-abs (ctx value)
  (if (p06b1-less-p ctx value (p06b1-zero ctx))
      (p06b1-neg ctx value)
    value))

(defun-sk p06b1-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p06b1-real-p ctx x)
      (p06b1-real-p ctx y)
      (p06b1-real-p ctx z))
     (and
      (p06b1-real-p ctx (p06b1-add ctx x y))
      (p06b1-real-p ctx (p06b1-mul ctx x y))
      (p06b1-real-p ctx (p06b1-neg ctx x))
      (p06b1-real-p ctx (p06b1-inv ctx x))
      (equal
       (p06b1-add ctx (p06b1-add ctx x y) z)
       (p06b1-add ctx x (p06b1-add ctx y z)))
      (equal
       (p06b1-add ctx x y)
       (p06b1-add ctx y x))
      (equal
       (p06b1-add ctx x (p06b1-zero ctx))
       x)
      (equal
       (p06b1-add ctx x (p06b1-neg ctx x))
       (p06b1-zero ctx))
      (equal
       (p06b1-mul ctx (p06b1-mul ctx x y) z)
       (p06b1-mul ctx x (p06b1-mul ctx y z)))
      (equal
       (p06b1-mul ctx x y)
       (p06b1-mul ctx y x))
      (equal
       (p06b1-mul ctx x (p06b1-one ctx))
       x)
      (implies
       (equal x (p06b1-zero ctx))
       (equal
        (p06b1-inv ctx x)
        (p06b1-zero ctx)))
      (implies
       (not (equal x (p06b1-zero ctx)))
       (equal
        (p06b1-mul ctx x (p06b1-inv ctx x))
        (p06b1-one ctx)))
      (equal
       (p06b1-mul ctx x (p06b1-add ctx y z))
       (p06b1-add
        ctx
        (p06b1-mul ctx x y)
        (p06b1-mul ctx x z)))))))

(defun-sk p06b1-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p06b1-real-p ctx x)
      (p06b1-real-p ctx y)
      (p06b1-real-p ctx z))
     (and
      (not (p06b1-less-p ctx x x))
      (or
       (equal x y)
       (p06b1-less-p ctx x y)
       (p06b1-less-p ctx y x))
      (implies
       (and
        (p06b1-less-p ctx x y)
        (p06b1-less-p ctx y z))
       (p06b1-less-p ctx x z))
      (implies
       (p06b1-less-p ctx x y)
       (p06b1-less-p
        ctx
        (p06b1-add ctx x z)
        (p06b1-add ctx y z)))
      (implies
       (and
        (p06b1-less-p ctx (p06b1-zero ctx) x)
        (p06b1-less-p ctx (p06b1-zero ctx) y))
       (p06b1-less-p
        ctx
        (p06b1-zero ctx)
        (p06b1-mul ctx x y)))))))

(defun p06b1-real-list-p (values ctx)
  (if (endp values)
      (equal values nil)
    (and
     (p06b1-real-p ctx (car values))
     (p06b1-real-list-p (cdr values) ctx))))

(defun p06b1-polynomial-p (coefficients ctx)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p06b1-real-list-p coefficients ctx)
   (or
    (equal (len coefficients) 1)
    (not
     (equal
      (car (last coefficients))
      (p06b1-zero ctx))))))

(defun p06b1-polynomial-eval (ctx coefficients value)
  (if (endp coefficients)
      (p06b1-zero ctx)
    (p06b1-add
     ctx
     (car coefficients)
     (p06b1-mul
      ctx
      value
      (p06b1-polynomial-eval
       ctx (cdr coefficients) value)))))

(defun-sk p06b1-odd-polynomial-root-exists-p
    (ctx coefficients)
  (exists (root)
    (and
     (p06b1-real-p ctx root)
     (equal
      (p06b1-polynomial-eval ctx coefficients root)
      (p06b1-zero ctx)))))

(defun-sk p06b1-square-root-laws-p (ctx)
  (forall (value)
    (implies
     (and
      (p06b1-real-p ctx value)
      (not
       (p06b1-less-p ctx value (p06b1-zero ctx))))
     (let ((root (p06b1-sqrt ctx value)))
       (and
        (p06b1-real-p ctx root)
        (not
         (p06b1-less-p ctx root (p06b1-zero ctx)))
        (equal
         (p06b1-square ctx root)
         value))))))

(defun-sk p06b1-odd-root-laws-p (ctx)
  (forall (coefficients)
    (implies
     (and
      (p06b1-polynomial-p coefficients ctx)
      (evenp (len coefficients)))
     (p06b1-odd-polynomial-root-exists-p
      ctx coefficients))))

(defun p06b1-real-closed-field-p (ctx)
  (and
   (p06b1-real-p ctx (p06b1-zero ctx))
   (p06b1-real-p ctx (p06b1-one ctx))
   (not
    (equal
     (p06b1-zero ctx)
     (p06b1-one ctx)))
   (p06b1-field-laws-p ctx)
   (p06b1-order-laws-p ctx)
   (p06b1-less-p
    ctx (p06b1-zero ctx) (p06b1-one ctx))
   (p06b1-square-root-laws-p ctx)
   (p06b1-odd-root-laws-p ctx)))

(defun p06b1-point-p (ctx x y)
  (and
   (p06b1-real-p ctx x)
   (p06b1-real-p ctx y)))

(defun p06b1-curve-point-p (ctx x y)
  (and
   (p06b1-point-p ctx x y)
   (equal
    (p06b1-add
     ctx
     (p06b1-cube ctx x)
     (p06b1-add
      ctx
      (p06b1-mul
       ctx
       (p06b1-three ctx)
       (p06b1-mul ctx x y))
      (p06b1-cube ctx y)))
    (p06b1-one ctx))))

(defun p06b1-same-point-p (ax ay bx by)
  (and
   (equal ax bx)
   (equal ay by)))

(defun p06b1-distinct-points-p (ax ay bx by)
  (not (p06b1-same-point-p ax ay bx by)))

(defun p06b1-squared-distance
    (ctx ax ay bx by)
  (p06b1-add
   ctx
   (p06b1-square ctx (p06b1-sub ctx ax bx))
   (p06b1-square ctx (p06b1-sub ctx ay by))))

(defun p06b1-equilateral-triple-p
    (ctx ax ay bx by cx cy)
  (let ((ab
         (p06b1-squared-distance
          ctx ax ay bx by))
        (ac
         (p06b1-squared-distance
          ctx ax ay cx cy))
        (bc
         (p06b1-squared-distance
          ctx bx by cx cy)))
    (and
     (p06b1-distinct-points-p ax ay bx by)
     (p06b1-distinct-points-p ax ay cx cy)
     (p06b1-distinct-points-p bx by cx cy)
     (equal ab ac)
     (equal ac bc))))

(defun p06b1-triangle-on-curve-p
    (ctx ax ay bx by cx cy)
  (and
   (p06b1-curve-point-p ctx ax ay)
   (p06b1-curve-point-p ctx bx by)
   (p06b1-curve-point-p ctx cx cy)
   (p06b1-equilateral-triple-p
    ctx ax ay bx by cx cy)))

(defun p06b1-point-in-triple-p
    (px py ax ay bx by cx cy)
  (or
   (p06b1-same-point-p px py ax ay)
   (p06b1-same-point-p px py bx by)
   (p06b1-same-point-p px py cx cy)))

(defun p06b1-same-triangle-set-p
    (ax ay bx by cx cy dx dy ex ey fx fy)
  (and
   (p06b1-point-in-triple-p
    ax ay dx dy ex ey fx fy)
   (p06b1-point-in-triple-p
    bx by dx dy ex ey fx fy)
   (p06b1-point-in-triple-p
    cx cy dx dy ex ey fx fy)
   (p06b1-point-in-triple-p
    dx dy ax ay bx by cx cy)
   (p06b1-point-in-triple-p
    ex ey ax ay bx by cx cy)
   (p06b1-point-in-triple-p
    fx fy ax ay bx by cx cy)))

(defun p06b1-determinant
    (ctx ax ay bx by cx cy)
  (p06b1-sub
   ctx
   (p06b1-mul
    ctx
    (p06b1-sub ctx bx ax)
    (p06b1-sub ctx cy ay))
   (p06b1-mul
    ctx
    (p06b1-sub ctx by ay)
    (p06b1-sub ctx cx ax))))

(defun p06b1-triangle-area
    (ctx ax ay bx by cx cy)
  (p06b1-div
   ctx
   (p06b1-abs
    ctx
    (p06b1-determinant
     ctx ax ay bx by cx cy))
   (p06b1-two ctx)))

(defun p06b1-answer (ctx)
  (p06b1-div
   ctx
   (p06b1-mul
    ctx
    (p06b1-three ctx)
    (p06b1-sqrt ctx (p06b1-three ctx)))
   (p06b1-two ctx)))

(defun p06b1-area-is-answer-p
    (ctx ax ay bx by cx cy)
  (equal
   (p06b1-triangle-area
    ctx ax ay bx by cx cy)
   (p06b1-answer ctx)))

(defun-sk p06b1-all-triangles-are-this-set-p
    (ctx ax ay bx by cx cy)
  (forall (dx dy ex ey fx fy)
    (implies
     (p06b1-triangle-on-curve-p
      ctx dx dy ex ey fx fy)
     (p06b1-same-triangle-set-p
      ax ay bx by cx cy
      dx dy ex ey fx fy))))

(defun-sk p06b1-unique-area-triangle-exists-p (ctx)
  (exists (ax ay bx by cx cy)
    (and
     (p06b1-triangle-on-curve-p
      ctx ax ay bx by cx cy)
     (p06b1-area-is-answer-p
      ctx ax ay bx by cx cy)
     (p06b1-all-triangles-are-this-set-p
      ctx ax ay bx by cx cy))))

(defun putnambench-putnam-2006-b1-statement (ctx)
  (implies
   (p06b1-real-closed-field-p ctx)
   (p06b1-unique-area-triangle-exists-p ctx)))

(value-triple :itpeval-statement-checked)
:q
