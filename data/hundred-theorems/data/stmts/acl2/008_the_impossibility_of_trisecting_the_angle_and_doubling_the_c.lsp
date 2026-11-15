;; Statement-only formalization of Hundred Theorems artifact 008,
;; "The Impossibility of Trisecting the Angle and Doubling the Cube."
;; Constructible points are exactly those admitting a finite derivation from
;; rational points by the three straightedge-and-compass intersection rules.
;; No cube root of two, nor a point whose first coordinate is cos(pi/9), has
;; such a derivation. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar operations describe an arbitrary real-closed ordered field.
;; This gives the full algebraic real geometry needed by the source without
;; restricting coordinates to ACL2's built-in rationals.

(defstub ht008-carrier (x) t)
(defstub ht008-add-op (x y) t)
(defstub ht008-multiply-op (x y) t)
(defstub ht008-negate-op (x) t)
(defstub ht008-inverse-op (x) t)
(defstub ht008-less-op (x y) t)

(defun ht008-member-p (x)
  (if (ht008-carrier x) t nil))

(defun ht008-add (x y)
  (ht008-add-op x y))

(defun ht008-multiply (x y)
  (ht008-multiply-op x y))

(defun ht008-negate (x)
  (ht008-negate-op x))

(defun ht008-inverse (x)
  (ht008-inverse-op x))

(defun ht008-subtract (x y)
  (ht008-add x (ht008-negate y)))

(defun ht008-less (x y)
  (if (ht008-less-op x y) t nil))

(defun ht008-square (x)
  (ht008-multiply x x))

(defun ht008-cube (x)
  (ht008-multiply x (ht008-square x)))

(defun-sk ht008-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (ht008-member-p x)
      (ht008-member-p y)
      (ht008-member-p z))
     (and
      (ht008-member-p (ht008-add x y))
      (ht008-member-p (ht008-multiply x y))
      (ht008-member-p (ht008-negate x))
      (ht008-member-p (ht008-inverse x))
      (equal (ht008-add (ht008-add x y) z)
             (ht008-add x (ht008-add y z)))
      (equal (ht008-add x y)
             (ht008-add y x))
      (equal (ht008-add x zero) x)
      (equal (ht008-add x (ht008-negate x)) zero)
      (equal (ht008-multiply (ht008-multiply x y) z)
             (ht008-multiply x (ht008-multiply y z)))
      (equal (ht008-multiply x y)
             (ht008-multiply y x))
      (equal (ht008-multiply x one) x)
      (equal
       (ht008-multiply x (ht008-add y z))
       (ht008-add
        (ht008-multiply x y)
        (ht008-multiply x z)))
      (implies
       (not (equal x zero))
       (equal
        (ht008-multiply x (ht008-inverse x))
        one))))))

(defun-sk ht008-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (ht008-member-p x)
      (ht008-member-p y)
      (ht008-member-p z))
     (and
      (not (ht008-less x x))
      (or
       (equal x y)
       (ht008-less x y)
       (ht008-less y x))
      (implies
       (and
        (ht008-less x y)
        (ht008-less y z))
       (ht008-less x z))
      (implies
       (ht008-less x y)
       (ht008-less
        (ht008-add x z)
        (ht008-add y z)))
      (implies
       (and
        (ht008-less zero x)
        (ht008-less zero y))
       (ht008-less zero (ht008-multiply x y)))))))

(defun ht008-carrier-list-p (values)
  (if (consp values)
      (and
       (ht008-member-p (car values))
       (ht008-carrier-list-p (cdr values)))
    (equal values nil)))

(defun ht008-polynomial-value (coefficients x zero)
  (if (consp coefficients)
      (ht008-add
       (car coefficients)
       (ht008-multiply
        x
        (ht008-polynomial-value
         (cdr coefficients) x zero)))
    zero))

(defun ht008-odd-degree-polynomial-p
    (coefficients zero)
  (and
   (consp coefficients)
   (true-listp coefficients)
   (ht008-carrier-list-p coefficients)
   (evenp (len coefficients))
   (not (equal (car (last coefficients)) zero))))

(defun-sk ht008-has-square-root-p (x)
  (exists (root)
    (and
     (ht008-member-p root)
     (equal (ht008-square root) x))))

(defun-sk ht008-polynomial-has-root-p
    (coefficients zero)
  (exists (root)
    (and
     (ht008-member-p root)
     (equal
      (ht008-polynomial-value coefficients root zero)
      zero))))

(defun-sk ht008-real-closure-laws-p (zero)
  (forall (x coefficients)
    (and
     (implies
      (and
       (ht008-member-p x)
       (not (ht008-less x zero)))
      (ht008-has-square-root-p x))
     (implies
      (ht008-odd-degree-polynomial-p coefficients zero)
      (ht008-polynomial-has-root-p coefficients zero)))))

(defun ht008-real-scalar-context-p (zero one)
  (and
   (ht008-member-p zero)
   (ht008-member-p one)
   (not (equal zero one))
   (ht008-less zero one)
   (ht008-field-laws-p zero one)
   (ht008-order-laws-p zero)
   (ht008-real-closure-laws-p zero)))

(defun ht008-natural-value (n zero one)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ht008-add
     one
     (ht008-natural-value (- n 1) zero one))))

(defun ht008-integer-value (integer zero one)
  (if (< integer 0)
      (ht008-negate
       (ht008-natural-value (- integer) zero one))
    (ht008-natural-value integer zero one)))

(defun-sk ht008-rational-element-p (x zero one)
  (exists (numerator denominator)
    (and
     (integerp numerator)
     (posp denominator)
     (equal
      (ht008-multiply
       x
       (ht008-integer-value denominator zero one))
      (ht008-integer-value numerator zero one)))))

;; Planar points and the exact incidence/radius relations from the sources.

(defun ht008-point-p (point)
  (and
   (consp point)
   (ht008-member-p (car point))
   (ht008-member-p (cdr point))))

(defun ht008-rational-point-p (point zero one)
  (and
   (ht008-point-p point)
   (ht008-rational-element-p (car point) zero one)
   (ht008-rational-element-p (cdr point) zero one)))

(defun ht008-point-equal-p (left right)
  (and
   (equal (car left) (car right))
   (equal (cdr left) (cdr right))))

(defun ht008-parallel-p (point-a point-b point-c point-d)
  (equal
   (ht008-multiply
    (ht008-subtract (car point-a) (car point-b))
    (ht008-subtract (cdr point-c) (cdr point-d)))
   (ht008-multiply
    (ht008-subtract (cdr point-a) (cdr point-b))
    (ht008-subtract (car point-c) (car point-d)))))

(defun ht008-collinear-p (point-a point-m point-b)
  (ht008-parallel-p point-a point-m point-a point-b))

(defun ht008-squared-distance (left right)
  (let ((dx (ht008-subtract (car left) (car right)))
        (dy (ht008-subtract (cdr left) (cdr right))))
    (ht008-add
     (ht008-square dx)
     (ht008-square dy))))

(defun ht008-same-distance-p
    (point-a point-b point-c point-d)
  (equal
   (ht008-squared-distance point-a point-b)
   (ht008-squared-distance point-c point-d)))

;; A construction is a finite sequence of steps. References in a step must
;; be equal to earlier complete steps, so cycles and forward references are
;; impossible. The second field of every step is its output point.

(defun ht008-step-output (step)
  (cadr step))

(defun ht008-prior-step-p (step prior-steps)
  (if (member-equal step prior-steps) t nil))

(defun ht008-valid-rational-step-p
    (step zero one)
  (and
   (true-listp step)
   (equal (len step) 2)
   (eq (car step) :rational-point)
   (ht008-rational-point-p
    (ht008-step-output step) zero one)))

(defun ht008-valid-line-line-step-p
    (step prior-steps)
  (let* ((point-m (nth 1 step))
         (step-a (nth 2 step))
         (step-b (nth 3 step))
         (step-c (nth 4 step))
         (step-d (nth 5 step))
         (point-a (ht008-step-output step-a))
         (point-b (ht008-step-output step-b))
         (point-c (ht008-step-output step-c))
         (point-d (ht008-step-output step-d)))
    (and
     (true-listp step)
     (equal (len step) 6)
     (eq (car step) :line-line)
     (ht008-point-p point-m)
     (ht008-prior-step-p step-a prior-steps)
     (ht008-prior-step-p step-b prior-steps)
     (ht008-prior-step-p step-c prior-steps)
     (ht008-prior-step-p step-d prior-steps)
     (not (ht008-parallel-p
           point-a point-b point-c point-d))
     (ht008-collinear-p point-a point-m point-b)
     (ht008-collinear-p point-c point-m point-d))))

(defun ht008-valid-line-circle-step-p
    (step prior-steps)
  (let* ((point-m (nth 1 step))
         (step-a (nth 2 step))
         (step-b (nth 3 step))
         (step-c (nth 4 step))
         (step-d (nth 5 step))
         (step-e (nth 6 step))
         (point-a (ht008-step-output step-a))
         (point-b (ht008-step-output step-b))
         (point-c (ht008-step-output step-c))
         (point-d (ht008-step-output step-d))
         (point-e (ht008-step-output step-e)))
    (and
     (true-listp step)
     (equal (len step) 7)
     (eq (car step) :line-circle)
     (ht008-point-p point-m)
     (ht008-prior-step-p step-a prior-steps)
     (ht008-prior-step-p step-b prior-steps)
     (ht008-prior-step-p step-c prior-steps)
     (ht008-prior-step-p step-d prior-steps)
     (ht008-prior-step-p step-e prior-steps)
     (not (ht008-point-equal-p point-a point-b))
     (ht008-collinear-p point-a point-m point-b)
     (ht008-same-distance-p
      point-c point-m point-d point-e))))

(defun ht008-valid-circle-circle-step-p
    (step prior-steps)
  (let* ((point-m (nth 1 step))
         (step-a (nth 2 step))
         (step-b (nth 3 step))
         (step-c (nth 4 step))
         (step-d (nth 5 step))
         (step-e (nth 6 step))
         (step-f (nth 7 step))
         (point-a (ht008-step-output step-a))
         (point-b (ht008-step-output step-b))
         (point-c (ht008-step-output step-c))
         (point-d (ht008-step-output step-d))
         (point-e (ht008-step-output step-e))
         (point-f (ht008-step-output step-f)))
    (and
     (true-listp step)
     (equal (len step) 8)
     (eq (car step) :circle-circle)
     (ht008-point-p point-m)
     (ht008-prior-step-p step-a prior-steps)
     (ht008-prior-step-p step-b prior-steps)
     (ht008-prior-step-p step-c prior-steps)
     (ht008-prior-step-p step-d prior-steps)
     (ht008-prior-step-p step-e prior-steps)
     (ht008-prior-step-p step-f prior-steps)
     (not
      (and
       (ht008-point-equal-p point-a point-d)
       (ht008-same-distance-p
        point-b point-c point-e point-f)))
     (ht008-same-distance-p
      point-a point-m point-b point-c)
     (ht008-same-distance-p
      point-d point-m point-e point-f))))

(defun ht008-valid-step-p
    (step prior-steps zero one)
  (cond
   ((and (consp step)
         (eq (car step) :rational-point))
    (ht008-valid-rational-step-p step zero one))
   ((and (consp step)
         (eq (car step) :line-line))
    (ht008-valid-line-line-step-p step prior-steps))
   ((and (consp step)
         (eq (car step) :line-circle))
    (ht008-valid-line-circle-step-p step prior-steps))
   ((and (consp step)
         (eq (car step) :circle-circle))
    (ht008-valid-circle-circle-step-p step prior-steps))
   (t nil)))

(defun ht008-valid-construction-sequence-p
    (steps prior-steps zero one)
  (if (consp steps)
      (and
       (ht008-valid-step-p
        (car steps) prior-steps zero one)
       (ht008-valid-construction-sequence-p
        (cdr steps)
        (cons (car steps) prior-steps)
        zero one))
    (equal steps nil)))

(defun-sk ht008-constructible-point-p
    (point zero one)
  (exists (steps)
    (and
     (consp steps)
     (true-listp steps)
     (ht008-valid-construction-sequence-p
      steps nil zero one)
     (ht008-point-equal-p
      point
      (ht008-step-output (car (last steps)))))))

(defun ht008-cos-pi-over-nine-p
    (value zero one)
  (let* ((six (ht008-natural-value 6 zero one))
         (eight (ht008-natural-value 8 zero one))
         (polynomial-value
          (ht008-subtract
           (ht008-subtract
            (ht008-multiply eight (ht008-cube value))
            (ht008-multiply six value))
           one)))
    (and
     (ht008-member-p value)
     (ht008-less zero value)
     (equal polynomial-value zero))))

(defun-sk ht008-doubling-the-cube-impossible-p
    (zero one)
  (forall (x)
    (implies
     (and
      (ht008-member-p x)
      (equal
       (ht008-cube x)
       (ht008-natural-value 2 zero one)))
     (not
      (ht008-constructible-point-p
       (cons x zero) zero one)))))

(defun-sk ht008-trisecting-sixty-degrees-impossible-p
    (zero one)
  (forall (cosine-value ordinate)
    (implies
     (and
      (ht008-cos-pi-over-nine-p
       cosine-value zero one)
      (ht008-member-p ordinate))
     (not
      (ht008-constructible-point-p
       (cons cosine-value ordinate) zero one)))))

(defun hundred-theorems-008-impossibility-statement
    (zero one)
  (implies
   (ht008-real-scalar-context-p zero one)
   (and
    (ht008-doubling-the-cube-impossible-p zero one)
    (ht008-trisecting-sixty-degrees-impossible-p
     zero one))))

(value-triple :itpeval-statement-checked)
:q
