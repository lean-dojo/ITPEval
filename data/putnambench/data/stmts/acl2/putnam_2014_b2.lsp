;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_b2:
;; the maximum of the integral of f(x)/x on [1,3], for real integrable f
;; bounded between -1 and 1 with integral zero, is ln(4/3). This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers up to the
;; unique ordered-field isomorphism. APPLY$ objects present arbitrary sets and
;; real-valued functions without replacing them by finite tables. Integrals
;; are defined below by the unbounded tagged-partition criterion for the
;; Riemann integral. This is the integral intended by the published problem;
;; changing open to closed interval endpoints does not change its value.

(defun p14b2-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p14b2-unary-value (operation x)
  (apply$ operation (list x)))

(defun p14b2-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p14b2-valid-scalar-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p14b2-member-p carrier x))))

(defun-sk p14b2-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p14b2-member-p carrier x)
      (p14b2-member-p carrier y)
      (p14b2-member-p carrier z))
     (and
      (p14b2-member-p
       carrier (p14b2-binary-value add x y))
      (p14b2-member-p
       carrier (p14b2-binary-value multiply x y))
      (p14b2-member-p
       carrier (p14b2-unary-value negate x))
      (p14b2-member-p
       carrier (p14b2-unary-value inverse x))
      (equal
       (p14b2-binary-value
        add (p14b2-binary-value add x y) z)
       (p14b2-binary-value
        add x (p14b2-binary-value add y z)))
      (equal
       (p14b2-binary-value add x y)
       (p14b2-binary-value add y x))
      (equal (p14b2-binary-value add x zero) x)
      (equal
       (p14b2-binary-value
        add x (p14b2-unary-value negate x))
       zero)
      (equal
       (p14b2-binary-value
        multiply (p14b2-binary-value multiply x y) z)
       (p14b2-binary-value
        multiply x (p14b2-binary-value multiply y z)))
      (equal
       (p14b2-binary-value multiply x y)
       (p14b2-binary-value multiply y x))
      (equal (p14b2-binary-value multiply x one) x)
      (equal (p14b2-unary-value inverse zero) zero)
      (implies
       (not (equal x zero))
       (equal
        (p14b2-binary-value
         multiply x (p14b2-unary-value inverse x))
        one))
      (equal
       (p14b2-binary-value
        multiply x (p14b2-binary-value add y z))
       (p14b2-binary-value
        add
        (p14b2-binary-value multiply x y)
        (p14b2-binary-value multiply x z)))))))

(defun-sk p14b2-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p14b2-member-p carrier x)
      (p14b2-member-p carrier y)
      (p14b2-member-p carrier z))
     (and
      (not (p14b2-binary-value less x x))
      (or
       (equal x y)
       (p14b2-binary-value less x y)
       (p14b2-binary-value less y x))
      (implies
       (and
        (p14b2-binary-value less x y)
        (p14b2-binary-value less y z))
       (p14b2-binary-value less x z))
      (implies
       (p14b2-binary-value less x y)
       (p14b2-binary-value
        less
        (p14b2-binary-value add x z)
        (p14b2-binary-value add y z)))
      (implies
       (and
        (p14b2-binary-value less zero x)
        (p14b2-binary-value less zero y))
       (p14b2-binary-value
        less zero (p14b2-binary-value multiply x y)))))))

(defun-sk p14b2-scalar-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p14b2-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p14b2-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p14b2-member-p carrier x)
      (apply$ set (list x)))
     (not (p14b2-binary-value less bound x)))))

(defun-sk p14b2-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p14b2-member-p carrier bound)
     (p14b2-upper-bound-p carrier less set bound))))

(defun-sk p14b2-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p14b2-member-p carrier supremum)
     (p14b2-upper-bound-p carrier less set supremum)
     (implies
      (and
       (p14b2-member-p carrier bound)
       (p14b2-upper-bound-p carrier less set bound))
      (not (p14b2-binary-value less bound supremum))))))

(defun-sk p14b2-has-supremum-p (carrier less set)
  (exists (supremum)
    (p14b2-supremum-p carrier less set supremum)))

(defun-sk p14b2-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p14b2-valid-scalar-set-p carrier set)
      (p14b2-scalar-set-nonempty-p carrier set)
      (p14b2-bounded-above-p carrier less set))
     (p14b2-has-supremum-p carrier less set))))

(defun p14b2-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p14b2-member-p carrier zero)
   (p14b2-member-p carrier one)
   (not (equal zero one))
   (p14b2-field-laws-p
    carrier add multiply negate inverse zero one)
   (p14b2-order-laws-p carrier add multiply zero less)
   (p14b2-binary-value less zero one)
   (p14b2-dedekind-complete-p carrier less)))

(defun p14b2-r-carrier (ctx) (nth 0 ctx))
(defun p14b2-r-zero (ctx) (nth 1 ctx))
(defun p14b2-r-one (ctx) (nth 2 ctx))
(defun p14b2-r-add (ctx) (nth 3 ctx))
(defun p14b2-r-mul (ctx) (nth 4 ctx))
(defun p14b2-r-neg (ctx) (nth 5 ctx))
(defun p14b2-r-inv (ctx) (nth 6 ctx))
(defun p14b2-r-lt (ctx) (nth 7 ctx))

(defun p14b2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p14b2-real-field-p
    (p14b2-r-carrier ctx)
    (p14b2-r-add ctx)
    (p14b2-r-mul ctx)
    (p14b2-r-neg ctx)
    (p14b2-r-inv ctx)
    (p14b2-r-zero ctx)
    (p14b2-r-one ctx)
    (p14b2-r-lt ctx))))

(defun p14b2-r-add-value (ctx x y)
  (p14b2-binary-value (p14b2-r-add ctx) x y))

(defun p14b2-r-mul-value (ctx x y)
  (p14b2-binary-value (p14b2-r-mul ctx) x y))

(defun p14b2-r-neg-value (ctx x)
  (p14b2-unary-value (p14b2-r-neg ctx) x))

(defun p14b2-r-inv-value (ctx x)
  (p14b2-unary-value (p14b2-r-inv ctx) x))

(defun p14b2-r-sub-value (ctx x y)
  (p14b2-r-add-value ctx x (p14b2-r-neg-value ctx y)))

(defun p14b2-r-div-value (ctx x y)
  (p14b2-r-mul-value ctx x (p14b2-r-inv-value ctx y)))

(defun p14b2-r-lt-p (ctx x y)
  (if (p14b2-binary-value (p14b2-r-lt ctx) x y) t nil))

(defun p14b2-r-le-p (ctx x y)
  (not (p14b2-r-lt-p ctx y x)))

(defun p14b2-r-abs-value (ctx x)
  (if (p14b2-r-lt-p ctx x (p14b2-r-zero ctx))
      (p14b2-r-neg-value ctx x)
    x))

(defun p14b2-positive-real-p (ctx x)
  (and
   (p14b2-member-p (p14b2-r-carrier ctx) x)
   (p14b2-r-lt-p ctx (p14b2-r-zero ctx) x)))

(defun p14b2-natural (ctx n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p14b2-r-zero ctx)
    (p14b2-r-add-value
     ctx
     (p14b2-r-one ctx)
     (p14b2-natural ctx (- n 1)))))

(defun p14b2-three (ctx)
  (p14b2-natural ctx 3))

(defun p14b2-four-thirds (ctx)
  (p14b2-r-div-value
   ctx (p14b2-natural ctx 4) (p14b2-three ctx)))

(defun-sk p14b2-real-function-p (ctx function)
  (forall (x)
    (implies
     (p14b2-member-p (p14b2-r-carrier ctx) x)
     (p14b2-member-p
      (p14b2-r-carrier ctx)
      (p14b2-unary-value function x)))))

(defun p14b2-real-list-p (ctx values)
  (if (consp values)
      (and
       (p14b2-member-p (p14b2-r-carrier ctx) (car values))
       (p14b2-real-list-p ctx (cdr values)))
    (equal values nil)))

(defun p14b2-strictly-increasing-p (ctx values)
  (if (and (consp values) (consp (cdr values)))
      (and
       (p14b2-r-lt-p ctx (car values) (cadr values))
       (p14b2-strictly-increasing-p ctx (cdr values)))
    (and (consp values) (endp (cdr values)))))

(defun p14b2-tags-fit-p (ctx nodes tags)
  (if (consp tags)
      (and
       (consp nodes)
       (consp (cdr nodes))
       (p14b2-r-le-p ctx (car nodes) (car tags))
       (p14b2-r-le-p ctx (car tags) (cadr nodes))
       (p14b2-tags-fit-p ctx (cdr nodes) (cdr tags)))
    (and
     (consp nodes)
     (endp (cdr nodes))
     (equal tags nil))))

(defun p14b2-tagged-partition-p (ctx a b nodes tags)
  (and
   (true-listp nodes)
   (true-listp tags)
   (p14b2-real-list-p ctx nodes)
   (p14b2-real-list-p ctx tags)
   (p14b2-strictly-increasing-p ctx nodes)
   (p14b2-tags-fit-p ctx nodes tags)
   (equal (car nodes) a)
   (equal (car (last nodes)) b)))

(defun p14b2-mesh-less-p (ctx nodes delta)
  (if (and (consp nodes) (consp (cdr nodes)))
      (and
       (p14b2-r-lt-p
        ctx
        (p14b2-r-sub-value ctx (cadr nodes) (car nodes))
        delta)
       (p14b2-mesh-less-p ctx (cdr nodes) delta))
    (and (consp nodes) (endp (cdr nodes)))))

(defun p14b2-integrand-value (ctx function mode x)
  (cond
   ((equal mode 'reciprocal)
    (p14b2-r-inv-value ctx x))
   ((equal mode 'divide-by-x)
    (p14b2-r-mul-value
     ctx
     (p14b2-unary-value function x)
     (p14b2-r-inv-value ctx x)))
   (t
    (p14b2-unary-value function x))))

(defun p14b2-riemann-sum (ctx function mode nodes tags)
  (if (consp tags)
      (p14b2-r-add-value
       ctx
       (p14b2-r-mul-value
        ctx
        (p14b2-integrand-value ctx function mode (car tags))
        (p14b2-r-sub-value ctx (cadr nodes) (car nodes)))
       (p14b2-riemann-sum
        ctx function mode (cdr nodes) (cdr tags)))
    (p14b2-r-zero ctx)))

(defun-sk p14b2-integral-delta-p
    (ctx function mode a b value epsilon delta)
  (forall (nodes tags)
    (implies
     (and
      (p14b2-tagged-partition-p ctx a b nodes tags)
      (p14b2-mesh-less-p ctx nodes delta))
     (p14b2-r-lt-p
      ctx
      (p14b2-r-abs-value
       ctx
       (p14b2-r-sub-value
        ctx
        (p14b2-riemann-sum ctx function mode nodes tags)
        value))
      epsilon))))

(defun-sk p14b2-integral-delta-exists-p
    (ctx function mode a b value epsilon)
  (exists (delta)
    (and
     (p14b2-positive-real-p ctx delta)
     (p14b2-integral-delta-p
      ctx function mode a b value epsilon delta))))

(defun-sk p14b2-integral-converges-p
    (ctx function mode a b value)
  (forall (epsilon)
    (implies
     (p14b2-positive-real-p ctx epsilon)
     (p14b2-integral-delta-exists-p
      ctx function mode a b value epsilon))))

(defun p14b2-integral-value-p
    (ctx function mode a b value)
  (and
   (p14b2-member-p (p14b2-r-carrier ctx) a)
   (p14b2-member-p (p14b2-r-carrier ctx) b)
   (p14b2-member-p (p14b2-r-carrier ctx) value)
   (p14b2-r-le-p ctx a b)
   (or
    (equal mode 'reciprocal)
    (and
     (tamep-functionp function)
     (p14b2-real-function-p ctx function)))
   (p14b2-integral-converges-p
    ctx function mode a b value)))

(defun p14b2-in-main-interval-p (ctx x)
  (and
   (p14b2-member-p (p14b2-r-carrier ctx) x)
   (p14b2-r-le-p ctx (p14b2-r-one ctx) x)
   (p14b2-r-le-p ctx x (p14b2-three ctx))))

(defun-sk p14b2-bounded-function-p (ctx function)
  (forall (x)
    (implies
     (p14b2-in-main-interval-p ctx x)
     (and
      (p14b2-r-le-p
       ctx
       (p14b2-r-neg-value ctx (p14b2-r-one ctx))
       (p14b2-unary-value function x))
      (p14b2-r-le-p
       ctx
       (p14b2-unary-value function x)
       (p14b2-r-one ctx))))))

(defun p14b2-feasible-value-p (ctx function value)
  (and
   (tamep-functionp function)
   (p14b2-real-function-p ctx function)
   (p14b2-bounded-function-p ctx function)
   (p14b2-integral-value-p
    ctx
    function
    'plain
    (p14b2-r-one ctx)
    (p14b2-three ctx)
    (p14b2-r-zero ctx))
   (p14b2-integral-value-p
    ctx
    function
    'divide-by-x
    (p14b2-r-one ctx)
    (p14b2-three ctx)
    value)))

(defun-sk p14b2-maximum-attained-p (ctx maximum)
  (exists (function)
    (p14b2-feasible-value-p ctx function maximum)))

(defun-sk p14b2-maximum-upper-bound-p (ctx maximum)
  (forall (function value)
    (implies
     (p14b2-feasible-value-p ctx function value)
     (p14b2-r-le-p ctx value maximum))))

(defun p14b2-is-maximum-p (ctx maximum)
  (and
   (p14b2-member-p (p14b2-r-carrier ctx) maximum)
   (p14b2-maximum-attained-p ctx maximum)
   (p14b2-maximum-upper-bound-p ctx maximum)))

;; On positive reals, ln(4/3) is definitionally the integral of 1/x from
;; 1 to 4/3. The solution remains an internal existential witness.

(defun-sk p14b2-conclusion-p (ctx)
  (exists (solution)
    (and
     (p14b2-integral-value-p
      ctx
      nil
      'reciprocal
      (p14b2-r-one ctx)
      (p14b2-four-thirds ctx)
      solution)
     (p14b2-is-maximum-p ctx solution))))

(defun putnambench-putnam-2014-b2-statement (ctx)
  (implies
   (p14b2-context-p ctx)
   (p14b2-conclusion-p ctx)))

(value-triple :itpeval-statement-checked)
:q
