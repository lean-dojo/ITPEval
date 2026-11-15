;; Statement-only formalization of PutnamBench corpus artifact putnam_1988_a5:
;; existence and uniqueness of a positive-real function satisfying
;; f(f(x)) = 6*x - f(x) on the positive reals. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar symbols conservatively present an arbitrary Archimedean ordered
;; field with its rational embedding, the exact real-algebraic structure used
;; by this statement. The competitor is an arbitrary unary function symbol,
;; so the final implication is generic over every competing real function and
;; does not replace that quantifier by a recurrence or a finite function code.

(defstub putnam-1988-a5-scalar-p (x) t)
(defstub putnam-1988-a5-add-op (x y) t)
(defstub putnam-1988-a5-multiply-op (x y) t)
(defstub putnam-1988-a5-negate-op (x) t)
(defstub putnam-1988-a5-inverse-op (x) t)
(defstub putnam-1988-a5-less-op (x y) t)
(defstub putnam-1988-a5-rational-embed (q) t)
(defstub putnam-1988-a5-arch-bound (x) t)
(defstub putnam-1988-a5-zero () t)
(defstub putnam-1988-a5-one () t)

(defun putnam-1988-a5-add (x y)
  (putnam-1988-a5-add-op x y))

(defun putnam-1988-a5-multiply (x y)
  (putnam-1988-a5-multiply-op x y))

(defun putnam-1988-a5-negate (x)
  (putnam-1988-a5-negate-op x))

(defun putnam-1988-a5-inverse (x)
  (putnam-1988-a5-inverse-op x))

(defun putnam-1988-a5-subtract (x y)
  (putnam-1988-a5-add
   x
   (putnam-1988-a5-negate y)))

(defun putnam-1988-a5-less (x y)
  (if (putnam-1988-a5-less-op x y) t nil))

(defun putnam-1988-a5-positive-p (x)
  (and
   (putnam-1988-a5-scalar-p x)
   (putnam-1988-a5-less
    (putnam-1988-a5-zero)
    x)))

(defun-sk putnam-1988-a5-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1988-a5-scalar-p x)
      (putnam-1988-a5-scalar-p y)
      (putnam-1988-a5-scalar-p z))
     (and
      (putnam-1988-a5-scalar-p
       (putnam-1988-a5-add x y))
      (putnam-1988-a5-scalar-p
       (putnam-1988-a5-multiply x y))
      (putnam-1988-a5-scalar-p
       (putnam-1988-a5-negate x))
      (putnam-1988-a5-scalar-p
       (putnam-1988-a5-inverse x))
      (equal
       (putnam-1988-a5-add
        (putnam-1988-a5-add x y)
        z)
       (putnam-1988-a5-add
        x
        (putnam-1988-a5-add y z)))
      (equal
       (putnam-1988-a5-add x y)
       (putnam-1988-a5-add y x))
      (equal
       (putnam-1988-a5-add
        x
        (putnam-1988-a5-zero))
       x)
      (equal
       (putnam-1988-a5-add
        x
        (putnam-1988-a5-negate x))
       (putnam-1988-a5-zero))
      (equal
       (putnam-1988-a5-multiply
        (putnam-1988-a5-multiply x y)
        z)
       (putnam-1988-a5-multiply
        x
        (putnam-1988-a5-multiply y z)))
      (equal
       (putnam-1988-a5-multiply x y)
       (putnam-1988-a5-multiply y x))
      (equal
       (putnam-1988-a5-multiply
        x
        (putnam-1988-a5-one))
       x)
      (implies
       (equal x (putnam-1988-a5-zero))
       (equal
        (putnam-1988-a5-inverse x)
        (putnam-1988-a5-zero)))
      (implies
       (not (equal x (putnam-1988-a5-zero)))
       (equal
        (putnam-1988-a5-multiply
         x
         (putnam-1988-a5-inverse x))
        (putnam-1988-a5-one)))
      (equal
       (putnam-1988-a5-multiply
        x
        (putnam-1988-a5-add y z))
       (putnam-1988-a5-add
        (putnam-1988-a5-multiply x y)
        (putnam-1988-a5-multiply x z)))))))

(defun-sk putnam-1988-a5-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (putnam-1988-a5-scalar-p x)
      (putnam-1988-a5-scalar-p y)
      (putnam-1988-a5-scalar-p z))
     (and
      (not (putnam-1988-a5-less x x))
      (or
       (equal x y)
       (putnam-1988-a5-less x y)
       (putnam-1988-a5-less y x))
      (implies
       (and
        (putnam-1988-a5-less x y)
        (putnam-1988-a5-less y z))
       (putnam-1988-a5-less x z))
      (implies
       (putnam-1988-a5-less x y)
       (putnam-1988-a5-less
        (putnam-1988-a5-add x z)
        (putnam-1988-a5-add y z)))
      (implies
       (and
        (putnam-1988-a5-less
         (putnam-1988-a5-zero)
         x)
        (putnam-1988-a5-less
         (putnam-1988-a5-zero)
         y))
       (putnam-1988-a5-less
        (putnam-1988-a5-zero)
        (putnam-1988-a5-multiply x y)))))))

(defun-sk putnam-1988-a5-rational-embedding-laws-p ()
  (forall (q r)
    (implies
     (and
      (rationalp q)
      (rationalp r))
     (and
      (putnam-1988-a5-scalar-p
       (putnam-1988-a5-rational-embed q))
      (equal
       (putnam-1988-a5-rational-embed (+ q r))
       (putnam-1988-a5-add
        (putnam-1988-a5-rational-embed q)
        (putnam-1988-a5-rational-embed r)))
      (equal
       (putnam-1988-a5-rational-embed (* q r))
       (putnam-1988-a5-multiply
        (putnam-1988-a5-rational-embed q)
        (putnam-1988-a5-rational-embed r)))
      (iff
       (< q r)
       (putnam-1988-a5-less
        (putnam-1988-a5-rational-embed q)
        (putnam-1988-a5-rational-embed r)))))))

(defun-sk putnam-1988-a5-archimedean-p ()
  (forall (x)
    (implies
     (putnam-1988-a5-scalar-p x)
     (and
      (natp (putnam-1988-a5-arch-bound x))
      (putnam-1988-a5-less
       x
       (putnam-1988-a5-rational-embed
        (putnam-1988-a5-arch-bound x)))))))

(defun putnam-1988-a5-real-scalar-structure-p ()
  (and
   (putnam-1988-a5-scalar-p
    (putnam-1988-a5-zero))
   (putnam-1988-a5-scalar-p
    (putnam-1988-a5-one))
   (not
    (equal
     (putnam-1988-a5-zero)
     (putnam-1988-a5-one)))
   (equal
    (putnam-1988-a5-rational-embed 0)
    (putnam-1988-a5-zero))
   (equal
    (putnam-1988-a5-rational-embed 1)
    (putnam-1988-a5-one))
   (putnam-1988-a5-less
    (putnam-1988-a5-zero)
    (putnam-1988-a5-one))
   (putnam-1988-a5-field-laws-p)
   (putnam-1988-a5-order-laws-p)
   (putnam-1988-a5-rational-embedding-laws-p)
   (putnam-1988-a5-archimedean-p)))

(defun putnam-1988-a5-six-times (x)
  (putnam-1988-a5-multiply
   (putnam-1988-a5-rational-embed 6)
   x))

(defun putnam-1988-a5-function-value (function x)
  (apply$ function (list x)))

(defun-sk putnam-1988-a5-function-real-valued-p (function)
  (forall (x)
    (implies
     (putnam-1988-a5-scalar-p x)
     (putnam-1988-a5-scalar-p
      (putnam-1988-a5-function-value function x)))))

(defun-sk putnam-1988-a5-function-equations-p (function)
  (forall (x)
    (implies
     (putnam-1988-a5-positive-p x)
     (and
      (putnam-1988-a5-positive-p
       (putnam-1988-a5-function-value function x))
      (equal
       (putnam-1988-a5-function-value
        function
        (putnam-1988-a5-function-value function x))
       (putnam-1988-a5-subtract
        (putnam-1988-a5-six-times x)
        (putnam-1988-a5-function-value function x)))))))

(defun putnam-1988-a5-solution-p (function)
  (and
   (tamep-functionp function)
   (putnam-1988-a5-function-real-valued-p function)
   (putnam-1988-a5-function-equations-p function)))

(defun-sk putnam-1988-a5-agrees-on-positive-reals-p
    (solution competitor)
  (forall (x)
    (implies
     (putnam-1988-a5-positive-p x)
     (equal
      (putnam-1988-a5-function-value solution x)
      (putnam-1988-a5-function-value competitor x)))))

(defun-sk putnam-1988-a5-unique-solution-p (solution)
  (forall (competitor)
    (implies
     (putnam-1988-a5-solution-p competitor)
     (putnam-1988-a5-agrees-on-positive-reals-p
      solution competitor))))

(defun-sk putnam-1988-a5-exists-unique-solution-p ()
  (exists (solution)
    (and
     (putnam-1988-a5-solution-p solution)
     (putnam-1988-a5-unique-solution-p solution))))

(defun putnambench-putnam-1988-a5-statement ()
  (implies
   (putnam-1988-a5-real-scalar-structure-p)
   (putnam-1988-a5-exists-unique-solution-p)))

(value-triple :itpeval-statement-checked)
:q
