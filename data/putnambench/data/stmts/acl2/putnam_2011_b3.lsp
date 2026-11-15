;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_b3:
;; nonvanishing and continuity of g at zero, together with differentiability
;; there of f*g and f/g, imply differentiability of f. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative generic symbols present arbitrary scalar-valued
;; functions f and g over an ordered field. The theorem is local and its proof
;; uses only field algebra and epsilon-delta definitions, so no completeness
;; assumption or APPLY$ function-object universe is needed.

(defstub putnam-2011-b3-carrier (x) t)
(defstub putnam-2011-b3-add (x y) t)
(defstub putnam-2011-b3-multiply (x y) t)
(defstub putnam-2011-b3-negate (x) t)
(defstub putnam-2011-b3-inverse (x) t)
(defstub putnam-2011-b3-less (x y) t)
(defstub putnam-2011-b3-f (x) t)
(defstub putnam-2011-b3-g (x) t)

(defun putnam-2011-b3-member-p (x)
  (if (putnam-2011-b3-carrier x) t nil))

(defun putnam-2011-b3-subtract (x y)
  (putnam-2011-b3-add
   x
   (putnam-2011-b3-negate y)))

(defun putnam-2011-b3-divide (x y)
  (putnam-2011-b3-multiply
   x
   (putnam-2011-b3-inverse y)))

(defun putnam-2011-b3-less-p (x y)
  (if (putnam-2011-b3-less x y) t nil))

(defun putnam-2011-b3-less-equal-p (x y)
  (not (putnam-2011-b3-less-p y x)))

(defun putnam-2011-b3-absolute-value (zero x)
  (if (putnam-2011-b3-less-p x zero)
      (putnam-2011-b3-negate x)
    x))

(defun putnam-2011-b3-positive-p (zero x)
  (and
   (putnam-2011-b3-member-p x)
   (putnam-2011-b3-less-p zero x)))

(defun-sk putnam-2011-b3-field-laws-p (zero one)
  (forall (x y z)
    (implies
     (and
      (putnam-2011-b3-member-p x)
      (putnam-2011-b3-member-p y)
      (putnam-2011-b3-member-p z))
     (and
      (putnam-2011-b3-member-p
       (putnam-2011-b3-add x y))
      (putnam-2011-b3-member-p
       (putnam-2011-b3-multiply x y))
      (putnam-2011-b3-member-p
       (putnam-2011-b3-negate x))
      (putnam-2011-b3-member-p
       (putnam-2011-b3-inverse x))
      (equal
       (putnam-2011-b3-add
        (putnam-2011-b3-add x y)
        z)
       (putnam-2011-b3-add
        x
        (putnam-2011-b3-add y z)))
      (equal
       (putnam-2011-b3-add x y)
       (putnam-2011-b3-add y x))
      (equal
       (putnam-2011-b3-add x zero)
       x)
      (equal
       (putnam-2011-b3-add
        x
        (putnam-2011-b3-negate x))
       zero)
      (equal
       (putnam-2011-b3-multiply
        (putnam-2011-b3-multiply x y)
        z)
       (putnam-2011-b3-multiply
        x
        (putnam-2011-b3-multiply y z)))
      (equal
       (putnam-2011-b3-multiply x y)
       (putnam-2011-b3-multiply y x))
      (equal
       (putnam-2011-b3-multiply x one)
       x)
      (implies
       (equal x zero)
       (equal
        (putnam-2011-b3-inverse x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (putnam-2011-b3-multiply
         x
         (putnam-2011-b3-inverse x))
        one))
      (equal
       (putnam-2011-b3-multiply
        x
        (putnam-2011-b3-add y z))
       (putnam-2011-b3-add
        (putnam-2011-b3-multiply x y)
        (putnam-2011-b3-multiply x z)))))))

(defun-sk putnam-2011-b3-order-laws-p (zero)
  (forall (x y z)
    (implies
     (and
      (putnam-2011-b3-member-p x)
      (putnam-2011-b3-member-p y)
      (putnam-2011-b3-member-p z))
     (and
      (not (putnam-2011-b3-less-p x x))
      (or
       (equal x y)
       (putnam-2011-b3-less-p x y)
       (putnam-2011-b3-less-p y x))
      (implies
       (and
        (putnam-2011-b3-less-p x y)
        (putnam-2011-b3-less-p y z))
       (putnam-2011-b3-less-p x z))
      (implies
       (putnam-2011-b3-less-p x y)
       (putnam-2011-b3-less-p
        (putnam-2011-b3-add x z)
        (putnam-2011-b3-add y z)))
      (implies
       (and
        (putnam-2011-b3-less-p zero x)
        (putnam-2011-b3-less-p zero y))
       (putnam-2011-b3-less-p
        zero
        (putnam-2011-b3-multiply x y)))))))

(defun putnam-2011-b3-ordered-field-p (zero one)
  (and
   (putnam-2011-b3-member-p zero)
   (putnam-2011-b3-member-p one)
   (not (equal zero one))
   (putnam-2011-b3-field-laws-p zero one)
   (putnam-2011-b3-order-laws-p zero)
   (putnam-2011-b3-less-p zero one)))

(defun-sk putnam-2011-b3-functions-real-valued-p ()
  (forall (x)
    (implies
     (putnam-2011-b3-member-p x)
     (and
      (putnam-2011-b3-member-p
       (putnam-2011-b3-f x))
      (putnam-2011-b3-member-p
       (putnam-2011-b3-g x))))))

;; The three tags below select only the source function f and its two
;; definitionally specified combinations with g; they do not encode f or g.

(defun putnam-2011-b3-function-value (kind x)
  (cond
   ((equal kind :f)
    (putnam-2011-b3-f x))
   ((equal kind :product)
    (putnam-2011-b3-multiply
     (putnam-2011-b3-f x)
     (putnam-2011-b3-g x)))
   ((equal kind :quotient)
    (putnam-2011-b3-divide
     (putnam-2011-b3-f x)
     (putnam-2011-b3-g x)))
   (t x)))

;; Ordinary epsilon-delta continuity of g at the field zero.

(defun-sk putnam-2011-b3-continuity-neighborhood-p
    (zero epsilon delta)
  (forall (x)
    (implies
     (and
      (putnam-2011-b3-member-p x)
      (putnam-2011-b3-less-p
       (putnam-2011-b3-absolute-value
        zero
        (putnam-2011-b3-subtract x zero))
       delta))
     (putnam-2011-b3-less-p
      (putnam-2011-b3-absolute-value
       zero
       (putnam-2011-b3-subtract
        (putnam-2011-b3-g x)
        (putnam-2011-b3-g zero)))
      epsilon))))

(defun-sk putnam-2011-b3-continuity-radius-exists-p
    (zero epsilon)
  (exists (delta)
    (and
     (putnam-2011-b3-positive-p zero delta)
     (putnam-2011-b3-continuity-neighborhood-p
      zero epsilon delta))))

(defun-sk putnam-2011-b3-g-continuous-at-zero-p (zero)
  (forall (epsilon)
    (implies
     (putnam-2011-b3-positive-p zero epsilon)
     (putnam-2011-b3-continuity-radius-exists-p
      zero epsilon))))

;; Differentiability uses the equivalent first-order remainder formulation
;; |h(y)-h(0)-d(y-0)| <= epsilon*|y-0| in a neighborhood of zero.

(defun-sk putnam-2011-b3-derivative-neighborhood-p
    (kind zero derivative epsilon radius)
  (forall (y)
    (implies
     (and
      (putnam-2011-b3-member-p y)
      (putnam-2011-b3-less-p
       (putnam-2011-b3-absolute-value
        zero
        (putnam-2011-b3-subtract y zero))
       radius))
     (putnam-2011-b3-less-equal-p
      (putnam-2011-b3-absolute-value
       zero
       (putnam-2011-b3-subtract
        (putnam-2011-b3-subtract
         (putnam-2011-b3-function-value kind y)
         (putnam-2011-b3-function-value kind zero))
        (putnam-2011-b3-multiply
         derivative
         (putnam-2011-b3-subtract y zero))))
      (putnam-2011-b3-multiply
       epsilon
       (putnam-2011-b3-absolute-value
        zero
        (putnam-2011-b3-subtract y zero)))))))

(defun-sk putnam-2011-b3-derivative-radius-exists-p
    (kind zero derivative epsilon)
  (exists (radius)
    (and
     (putnam-2011-b3-positive-p zero radius)
     (putnam-2011-b3-derivative-neighborhood-p
      kind zero derivative epsilon radius))))

(defun-sk putnam-2011-b3-derivative-epsilon-p
    (kind zero derivative)
  (forall (epsilon)
    (implies
     (putnam-2011-b3-positive-p zero epsilon)
     (putnam-2011-b3-derivative-radius-exists-p
      kind zero derivative epsilon))))

(defun putnam-2011-b3-has-derivative-at-zero-p
    (kind zero derivative)
  (and
   (putnam-2011-b3-member-p derivative)
   (putnam-2011-b3-derivative-epsilon-p
    kind zero derivative)))

(defun-sk putnam-2011-b3-differentiable-at-zero-p
    (kind zero)
  (exists (derivative)
    (putnam-2011-b3-has-derivative-at-zero-p
     kind zero derivative)))

(defun-sk putnambench-putnam-2011-b3-statement ()
  (forall (zero one)
    (implies
     (and
      (putnam-2011-b3-ordered-field-p zero one)
      (putnam-2011-b3-functions-real-valued-p)
      (not
       (equal
        (putnam-2011-b3-g zero)
        zero))
      (putnam-2011-b3-g-continuous-at-zero-p
       zero)
      (putnam-2011-b3-differentiable-at-zero-p
       :product zero)
      (putnam-2011-b3-differentiable-at-zero-p
       :quotient zero))
     (putnam-2011-b3-differentiable-at-zero-p
      :f zero))))

(value-triple :itpeval-statement-checked)
:q
