;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_246:
;; for real a and b, a real function equal everywhere to
;; a*x^4 - b*x^2 + x + 5 and satisfying f(-3) = 2 must satisfy f(3) = 8.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The context below presents the real field as a Dedekind-complete ordered
;; field, following the established ACL2 statement-only encoding.  The
;; conservative evaluator keeps f generic, and DEFUN-SK retains the source's
;; unbounded universal quantifier over every real x.

(defstub mathd-algebra-246-function-value
  (function x)
  t)

(defun mathd-algebra-246-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun mathd-algebra-246-unary-value (operation x)
  (apply$ operation (list x)))

(defun mathd-algebra-246-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk mathd-algebra-246-valid-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (mathd-algebra-246-member-p carrier x))))

(defun-sk mathd-algebra-246-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (mathd-algebra-246-member-p carrier x)
      (mathd-algebra-246-member-p carrier y)
      (mathd-algebra-246-member-p carrier z))
     (and
      (mathd-algebra-246-member-p
       carrier
       (mathd-algebra-246-binary-value add x y))
      (mathd-algebra-246-member-p
       carrier
       (mathd-algebra-246-binary-value multiply x y))
      (mathd-algebra-246-member-p
       carrier
       (mathd-algebra-246-unary-value negate x))
      (mathd-algebra-246-member-p
       carrier
       (mathd-algebra-246-unary-value inverse x))
      (equal
       (mathd-algebra-246-binary-value
        add
        (mathd-algebra-246-binary-value add x y)
        z)
       (mathd-algebra-246-binary-value
        add
        x
        (mathd-algebra-246-binary-value add y z)))
      (equal
       (mathd-algebra-246-binary-value add x y)
       (mathd-algebra-246-binary-value add y x))
      (equal
       (mathd-algebra-246-binary-value add x zero)
       x)
      (equal
       (mathd-algebra-246-binary-value
        add
        x
        (mathd-algebra-246-unary-value negate x))
       zero)
      (equal
       (mathd-algebra-246-binary-value
        multiply
        (mathd-algebra-246-binary-value multiply x y)
        z)
       (mathd-algebra-246-binary-value
        multiply
        x
        (mathd-algebra-246-binary-value multiply y z)))
      (equal
       (mathd-algebra-246-binary-value multiply x y)
       (mathd-algebra-246-binary-value multiply y x))
      (equal
       (mathd-algebra-246-binary-value multiply x one)
       x)
      (implies
       (equal x zero)
       (equal
        (mathd-algebra-246-unary-value inverse x)
        zero))
      (implies
       (not (equal x zero))
       (equal
        (mathd-algebra-246-binary-value
         multiply
         x
         (mathd-algebra-246-unary-value inverse x))
        one))
      (equal
       (mathd-algebra-246-binary-value
        multiply
        x
        (mathd-algebra-246-binary-value add y z))
       (mathd-algebra-246-binary-value
        add
        (mathd-algebra-246-binary-value multiply x y)
        (mathd-algebra-246-binary-value multiply x z)))))))

(defun-sk mathd-algebra-246-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (mathd-algebra-246-member-p carrier x)
      (mathd-algebra-246-member-p carrier y)
      (mathd-algebra-246-member-p carrier z))
     (and
      (not
       (mathd-algebra-246-binary-value less x x))
      (or
       (equal x y)
       (mathd-algebra-246-binary-value less x y)
       (mathd-algebra-246-binary-value less y x))
      (implies
       (and
        (mathd-algebra-246-binary-value less x y)
        (mathd-algebra-246-binary-value less y z))
       (mathd-algebra-246-binary-value less x z))
      (implies
       (mathd-algebra-246-binary-value less x y)
       (mathd-algebra-246-binary-value
        less
        (mathd-algebra-246-binary-value add x z)
        (mathd-algebra-246-binary-value add y z)))
      (implies
       (and
        (mathd-algebra-246-binary-value less zero x)
        (mathd-algebra-246-binary-value less zero y))
       (mathd-algebra-246-binary-value
        less
        zero
        (mathd-algebra-246-binary-value multiply x y)))))))

(defun-sk mathd-algebra-246-set-nonempty-p
    (carrier set)
  (exists (x)
    (and
     (mathd-algebra-246-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk mathd-algebra-246-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (mathd-algebra-246-member-p carrier x)
      (apply$ set (list x)))
     (not
      (mathd-algebra-246-binary-value less bound x)))))

(defun-sk mathd-algebra-246-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (mathd-algebra-246-member-p carrier bound)
     (mathd-algebra-246-upper-bound-p
      carrier less set bound))))

(defun-sk mathd-algebra-246-least-upper-bound-p
    (carrier less set supremum)
  (forall (bound)
    (implies
     (and
      (mathd-algebra-246-member-p carrier bound)
      (mathd-algebra-246-upper-bound-p
       carrier less set bound))
     (not
      (mathd-algebra-246-binary-value
       less bound supremum)))))

(defun mathd-algebra-246-supremum-p
    (carrier less set supremum)
  (and
   (mathd-algebra-246-member-p carrier supremum)
   (mathd-algebra-246-upper-bound-p
    carrier less set supremum)
   (mathd-algebra-246-least-upper-bound-p
    carrier less set supremum)))

(defun-sk mathd-algebra-246-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (mathd-algebra-246-supremum-p
     carrier less set supremum)))

(defun-sk mathd-algebra-246-dedekind-complete-p
    (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (mathd-algebra-246-valid-set-p carrier set)
      (mathd-algebra-246-set-nonempty-p carrier set)
      (mathd-algebra-246-bounded-above-p
       carrier less set))
     (mathd-algebra-246-has-supremum-p
      carrier less set))))

(defun mathd-algebra-246-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (mathd-algebra-246-member-p carrier zero)
   (mathd-algebra-246-member-p carrier one)
   (not (equal zero one))
   (mathd-algebra-246-field-laws-p
    carrier add multiply negate inverse zero one)
   (mathd-algebra-246-order-laws-p
    carrier add multiply zero less)
   (mathd-algebra-246-binary-value less zero one)
   (mathd-algebra-246-dedekind-complete-p
    carrier less)))

(defun mathd-algebra-246-carrier (context)
  (nth 0 context))

(defun mathd-algebra-246-zero (context)
  (nth 1 context))

(defun mathd-algebra-246-one (context)
  (nth 2 context))

(defun mathd-algebra-246-add (context)
  (nth 3 context))

(defun mathd-algebra-246-multiply (context)
  (nth 4 context))

(defun mathd-algebra-246-negate (context)
  (nth 5 context))

(defun mathd-algebra-246-inverse (context)
  (nth 6 context))

(defun mathd-algebra-246-less (context)
  (nth 7 context))

(defun mathd-algebra-246-context-p (context)
  (and
   (true-listp context)
   (equal (len context) 8)
   (mathd-algebra-246-real-field-p
    (mathd-algebra-246-carrier context)
    (mathd-algebra-246-add context)
    (mathd-algebra-246-multiply context)
    (mathd-algebra-246-negate context)
    (mathd-algebra-246-inverse context)
    (mathd-algebra-246-zero context)
    (mathd-algebra-246-one context)
    (mathd-algebra-246-less context))))

(defun mathd-algebra-246-real-p (context x)
  (mathd-algebra-246-member-p
   (mathd-algebra-246-carrier context)
   x))

(defun mathd-algebra-246-add-value (context x y)
  (mathd-algebra-246-binary-value
   (mathd-algebra-246-add context)
   x y))

(defun mathd-algebra-246-multiply-value (context x y)
  (mathd-algebra-246-binary-value
   (mathd-algebra-246-multiply context)
   x y))

(defun mathd-algebra-246-negate-value (context x)
  (mathd-algebra-246-unary-value
   (mathd-algebra-246-negate context)
   x))

(defun mathd-algebra-246-subtract-value (context x y)
  (mathd-algebra-246-add-value
   context
   x
   (mathd-algebra-246-negate-value context y)))

(defun mathd-algebra-246-natural-value (context n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (mathd-algebra-246-zero context)
    (mathd-algebra-246-add-value
     context
     (mathd-algebra-246-one context)
     (mathd-algebra-246-natural-value
      context
      (- n 1)))))

(defun mathd-algebra-246-power-value
    (context base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (mathd-algebra-246-one context)
    (mathd-algebra-246-multiply-value
     context
     base
     (mathd-algebra-246-power-value
      context base (- exponent 1)))))

(defun mathd-algebra-246-polynomial-value
    (context a b x)
  (mathd-algebra-246-add-value
   context
   (mathd-algebra-246-add-value
    context
    (mathd-algebra-246-subtract-value
     context
     (mathd-algebra-246-multiply-value
      context
      a
      (mathd-algebra-246-power-value context x 4))
     (mathd-algebra-246-multiply-value
      context
      b
      (mathd-algebra-246-power-value context x 2)))
    x)
   (mathd-algebra-246-natural-value context 5)))

(defun-sk mathd-algebra-246-real-function-p
    (context function)
  (forall (x)
    (implies
     (mathd-algebra-246-real-p context x)
     (mathd-algebra-246-real-p
      context
      (mathd-algebra-246-function-value function x)))))

(defun-sk mathd-algebra-246-polynomial-definition-p
    (context a b function)
  (forall (x)
    (implies
     (mathd-algebra-246-real-p context x)
     (equal
      (mathd-algebra-246-function-value function x)
      (mathd-algebra-246-polynomial-value
       context a b x)))))

(defun mathd-algebra-246-statement
    (context a b function)
  (let* ((three
          (mathd-algebra-246-natural-value context 3))
         (minus-three
          (mathd-algebra-246-negate-value context three))
         (two
          (mathd-algebra-246-natural-value context 2))
         (eight
          (mathd-algebra-246-natural-value context 8)))
    (implies
     (and
      (mathd-algebra-246-context-p context)
      (mathd-algebra-246-real-p context a)
      (mathd-algebra-246-real-p context b)
      (mathd-algebra-246-real-function-p
       context function)
      (mathd-algebra-246-polynomial-definition-p
       context a b function)
      (equal
       (mathd-algebra-246-function-value
        function minus-three)
       two))
     (equal
      (mathd-algebra-246-function-value function three)
      eight))))

(value-triple :itpeval-statement-checked)
:q
