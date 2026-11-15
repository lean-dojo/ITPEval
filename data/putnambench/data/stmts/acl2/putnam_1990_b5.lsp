;; Statement-only formalization of PutnamBench corpus artifact putnam_1990_b5:
;; existence of an infinite sequence of nonzero real coefficients whose
;; degree-n partial polynomial has exactly n distinct real roots for every
;; positive n. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real scalar domain is presented as a real-closed ordered field. This
;; suffices because the statement concerns polynomial arithmetic, order, and
;; roots. APPLY$ objects represent the field operations and sequence, while
;; DEFUN-SK keeps the sequence and all root-list witnesses existentially
;; quantified inside the statement.

(defun p90b5-apply1 (function argument)
  (apply$ function (list argument)))

(defun p90b5-apply2 (function left right)
  (apply$ function (list left right)))

(defun p90b5-carrier-p (ctx value)
  (if (p90b5-apply1 (nth 0 ctx) value) t nil))

(defun p90b5-zero (ctx) (nth 1 ctx))
(defun p90b5-one (ctx) (nth 2 ctx))
(defun p90b5-add-operation (ctx) (nth 3 ctx))
(defun p90b5-multiply-operation (ctx) (nth 4 ctx))
(defun p90b5-negate-operation (ctx) (nth 5 ctx))
(defun p90b5-inverse-operation (ctx) (nth 6 ctx))
(defun p90b5-less-operation (ctx) (nth 7 ctx))

(defun p90b5-add (ctx left right)
  (p90b5-apply2
   (p90b5-add-operation ctx) left right))

(defun p90b5-multiply (ctx left right)
  (p90b5-apply2
   (p90b5-multiply-operation ctx) left right))

(defun p90b5-negate (ctx value)
  (p90b5-apply1
   (p90b5-negate-operation ctx) value))

(defun p90b5-inverse (ctx value)
  (p90b5-apply1
   (p90b5-inverse-operation ctx) value))

(defun p90b5-less-p (ctx left right)
  (if (p90b5-apply2
       (p90b5-less-operation ctx) left right)
      t nil))

(defun-sk p90b5-field-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p90b5-carrier-p ctx x)
      (p90b5-carrier-p ctx y)
      (p90b5-carrier-p ctx z))
     (let* ((zero (p90b5-zero ctx))
            (one (p90b5-one ctx))
            (x-plus-y (p90b5-add ctx x y))
            (y-plus-z (p90b5-add ctx y z))
            (x-times-y (p90b5-multiply ctx x y))
            (y-times-z (p90b5-multiply ctx y z))
            (minus-x (p90b5-negate ctx x))
            (inverse-x (p90b5-inverse ctx x)))
       (and
        (p90b5-carrier-p ctx x-plus-y)
        (p90b5-carrier-p ctx x-times-y)
        (p90b5-carrier-p ctx minus-x)
        (p90b5-carrier-p ctx inverse-x)
        (equal
         (p90b5-add ctx x-plus-y z)
         (p90b5-add ctx x y-plus-z))
        (equal x-plus-y (p90b5-add ctx y x))
        (equal (p90b5-add ctx x zero) x)
        (equal (p90b5-add ctx x minus-x) zero)
        (equal
         (p90b5-multiply ctx x-times-y z)
         (p90b5-multiply ctx x y-times-z))
        (equal x-times-y (p90b5-multiply ctx y x))
        (equal (p90b5-multiply ctx x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (p90b5-multiply ctx x inverse-x)
          one))
        (equal
         (p90b5-multiply ctx x y-plus-z)
         (p90b5-add
          ctx
          (p90b5-multiply ctx x y)
          (p90b5-multiply ctx x z))))))))

(defun-sk p90b5-order-laws-p (ctx)
  (forall (x y z)
    (implies
     (and
      (p90b5-carrier-p ctx x)
      (p90b5-carrier-p ctx y)
      (p90b5-carrier-p ctx z))
     (let ((zero (p90b5-zero ctx)))
       (and
        (not (p90b5-less-p ctx x x))
        (or
         (p90b5-less-p ctx x y)
         (equal x y)
         (p90b5-less-p ctx y x))
        (implies
         (and
          (p90b5-less-p ctx x y)
          (p90b5-less-p ctx y z))
         (p90b5-less-p ctx x z))
        (implies
         (p90b5-less-p ctx x y)
         (p90b5-less-p
          ctx
          (p90b5-add ctx x z)
          (p90b5-add ctx y z)))
        (implies
         (and
          (p90b5-less-p ctx zero x)
          (p90b5-less-p ctx zero y))
         (p90b5-less-p
          ctx
          zero
          (p90b5-multiply ctx x y))))))))

(defun p90b5-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (p90b5-carrier-p ctx (car coefficients))
       (p90b5-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun p90b5-polynomial-p (ctx coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (p90b5-coefficient-list-p ctx coefficients)
   (not
    (equal
     (car (last coefficients))
     (p90b5-zero ctx)))))

(defun p90b5-polynomial-evaluate (ctx coefficients x)
  (if (consp coefficients)
      (p90b5-add
       ctx
       (car coefficients)
       (p90b5-multiply
        ctx
        x
        (p90b5-polynomial-evaluate
         ctx (cdr coefficients) x)))
    (p90b5-zero ctx)))

(defun-sk p90b5-positive-square-root-exists-p
    (ctx value)
  (exists (root)
    (and
     (p90b5-carrier-p ctx root)
     (equal
      (p90b5-multiply ctx root root)
      value))))

(defun-sk p90b5-positive-square-root-law-p (ctx)
  (forall (value)
    (implies
     (and
      (p90b5-carrier-p ctx value)
      (p90b5-less-p
       ctx (p90b5-zero ctx) value))
     (p90b5-positive-square-root-exists-p
      ctx value))))

(defun-sk p90b5-odd-polynomial-root-exists-p
    (ctx coefficients)
  (exists (root)
    (and
     (p90b5-carrier-p ctx root)
     (equal
      (p90b5-polynomial-evaluate
       ctx coefficients root)
      (p90b5-zero ctx)))))

(defun-sk p90b5-odd-polynomial-root-law-p (ctx)
  (forall (coefficients)
    (implies
     (and
      (p90b5-polynomial-p ctx coefficients)
      (evenp (len coefficients)))
     (p90b5-odd-polynomial-root-exists-p
      ctx coefficients))))

(defun p90b5-real-closed-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (nth 0 ctx))
   (tamep-functionp (nth 3 ctx))
   (tamep-functionp (nth 4 ctx))
   (tamep-functionp (nth 5 ctx))
   (tamep-functionp (nth 6 ctx))
   (tamep-functionp (nth 7 ctx))
   (p90b5-carrier-p ctx (p90b5-zero ctx))
   (p90b5-carrier-p ctx (p90b5-one ctx))
   (not (equal (p90b5-zero ctx) (p90b5-one ctx)))
   (p90b5-field-laws-p ctx)
   (p90b5-order-laws-p ctx)
   (p90b5-less-p
    ctx (p90b5-zero ctx) (p90b5-one ctx))
   (p90b5-positive-square-root-law-p ctx)
   (p90b5-odd-polynomial-root-law-p ctx)))

(defun p90b5-sequence-value (sequence index)
  (p90b5-apply1 sequence index))

(defun-sk p90b5-sequence-values-p (ctx sequence)
  (forall (index)
    (implies
     (natp index)
     (and
      (p90b5-carrier-p
       ctx
       (p90b5-sequence-value sequence index))
      (not
       (equal
        (p90b5-sequence-value sequence index)
        (p90b5-zero ctx)))))))

;; Horner evaluation of
;; a_index + a_(index+1)x + ... + a_(index+count-1)x^(count-1).

(defun p90b5-partial-polynomial-evaluate
    (ctx sequence index count x)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p90b5-zero ctx)
    (p90b5-add
     ctx
     (p90b5-sequence-value sequence index)
     (p90b5-multiply
      ctx
      x
      (p90b5-partial-polynomial-evaluate
       ctx sequence (+ index 1) (- count 1) x)))))

(defun p90b5-root-p (ctx sequence degree value)
  (and
   (p90b5-carrier-p ctx value)
   (equal
    (p90b5-partial-polynomial-evaluate
     ctx sequence 0 (+ degree 1) value)
    (p90b5-zero ctx))))

(defun p90b5-listed-roots-p
    (ctx sequence degree roots)
  (if (consp roots)
      (and
       (p90b5-root-p
        ctx sequence degree (car roots))
       (p90b5-listed-roots-p
        ctx sequence degree (cdr roots)))
    (equal roots nil)))

(defun-sk p90b5-all-roots-listed-p
    (ctx sequence degree roots)
  (forall (value)
    (implies
     (p90b5-root-p ctx sequence degree value)
     (member-equal value roots))))

(defun p90b5-exact-root-list-p
    (ctx sequence degree roots)
  (and
   (true-listp roots)
   (equal (len roots) degree)
   (no-duplicatesp-equal roots)
   (p90b5-listed-roots-p
    ctx sequence degree roots)
   (p90b5-all-roots-listed-p
    ctx sequence degree roots)))

(defun-sk p90b5-exact-root-list-exists-p
    (ctx sequence degree)
  (exists (roots)
    (p90b5-exact-root-list-p
     ctx sequence degree roots)))

(defun-sk p90b5-all-partial-polynomials-p
    (ctx sequence)
  (forall (degree)
    (implies
     (posp degree)
     (p90b5-exact-root-list-exists-p
      ctx sequence degree))))

(defun p90b5-sequence-witness-p (ctx sequence)
  (and
   (tamep-functionp sequence)
   (p90b5-sequence-values-p ctx sequence)
   (p90b5-all-partial-polynomials-p
    ctx sequence)))

(defun-sk p90b5-sequence-exists-p (ctx)
  (exists (sequence)
    (p90b5-sequence-witness-p ctx sequence)))

(defun p90b5-solution ()
  t)

(defun putnambench-putnam-1990-b5-statement (ctx)
  (implies
   (p90b5-real-closed-field-p ctx)
   (iff
    (p90b5-sequence-exists-p ctx)
    (p90b5-solution))))

(value-triple :itpeval-statement-checked)
:q
