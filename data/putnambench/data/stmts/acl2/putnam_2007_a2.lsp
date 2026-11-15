;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_a2:
;; the least Lebesgue area of a convex subset of the real plane meeting both
;; branches of xy = 1 and both branches of xy = -1 is 4. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers up to their
;; unique ordered-field isomorphism. Plane points are exact coordinate pairs,
;; and arbitrary planar sets and countable rectangle covers are unbounded tame
;; APPLY$ function objects.
;;
;; Planar Lebesgue outer area is the infimum of the convergent total areas of
;; countable open axis-aligned rectangle covers. Thus the lower-bound predicate
;; below also covers sets of infinite area. Since every convex subset of the
;; real plane is Lebesgue measurable, this outer-area formulation is
;; bidirectionally equivalent to the source use of volume. The final two
;; clauses are exactly membership and universal minimality for IsLeast at 4.

(defun p07a2-member-p (carrier value)
  (if (apply$ carrier (list value)) t nil))

(defun p07a2-unary-value (operation value)
  (apply$ operation (list value)))

(defun p07a2-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun-sk p07a2-valid-scalar-set-p (carrier set)
  (forall (value)
    (implies
     (apply$ set (list value))
     (p07a2-member-p carrier value))))

(defun-sk p07a2-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p07a2-member-p carrier x)
      (p07a2-member-p carrier y)
      (p07a2-member-p carrier z))
     (and
      (p07a2-member-p
       carrier (p07a2-binary-value add x y))
      (p07a2-member-p
       carrier (p07a2-binary-value multiply x y))
      (p07a2-member-p
       carrier (p07a2-unary-value negate x))
      (implies
       (not (equal x zero))
       (p07a2-member-p
        carrier (p07a2-unary-value inverse x)))
      (equal
       (p07a2-binary-value
        add (p07a2-binary-value add x y) z)
       (p07a2-binary-value
        add x (p07a2-binary-value add y z)))
      (equal
       (p07a2-binary-value add x y)
       (p07a2-binary-value add y x))
      (equal (p07a2-binary-value add x zero) x)
      (equal
       (p07a2-binary-value
        add x (p07a2-unary-value negate x))
       zero)
      (equal
       (p07a2-binary-value
        multiply (p07a2-binary-value multiply x y) z)
       (p07a2-binary-value
        multiply x (p07a2-binary-value multiply y z)))
      (equal
       (p07a2-binary-value multiply x y)
       (p07a2-binary-value multiply y x))
      (equal (p07a2-binary-value multiply x one) x)
      (implies
       (equal x zero)
       (equal (p07a2-unary-value inverse x) zero))
      (implies
       (not (equal x zero))
       (equal
        (p07a2-binary-value
         multiply x (p07a2-unary-value inverse x))
        one))
      (equal
       (p07a2-binary-value
        multiply x (p07a2-binary-value add y z))
       (p07a2-binary-value
        add
        (p07a2-binary-value multiply x y)
        (p07a2-binary-value multiply x z)))))))

(defun-sk p07a2-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p07a2-member-p carrier x)
      (p07a2-member-p carrier y)
      (p07a2-member-p carrier z))
     (and
      (not (p07a2-binary-value less x x))
      (or
       (equal x y)
       (p07a2-binary-value less x y)
       (p07a2-binary-value less y x))
      (implies
       (and
        (p07a2-binary-value less x y)
        (p07a2-binary-value less y z))
       (p07a2-binary-value less x z))
      (implies
       (p07a2-binary-value less x y)
       (p07a2-binary-value
        less
        (p07a2-binary-value add x z)
        (p07a2-binary-value add y z)))
      (implies
       (and
        (p07a2-binary-value less zero x)
        (p07a2-binary-value less zero y))
       (p07a2-binary-value
        less zero (p07a2-binary-value multiply x y)))))))

(defun-sk p07a2-scalar-set-nonempty-p (carrier set)
  (exists (value)
    (and
     (p07a2-member-p carrier value)
     (apply$ set (list value)))))

(defun-sk p07a2-upper-bound-p (carrier less set bound)
  (forall (value)
    (implies
     (and
      (p07a2-member-p carrier value)
      (apply$ set (list value)))
     (not (p07a2-binary-value less bound value)))))

(defun-sk p07a2-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p07a2-member-p carrier bound)
     (p07a2-upper-bound-p carrier less set bound))))

(defun-sk p07a2-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p07a2-member-p carrier supremum)
     (p07a2-upper-bound-p carrier less set supremum)
     (implies
      (and
       (p07a2-member-p carrier bound)
       (p07a2-upper-bound-p carrier less set bound))
      (not (p07a2-binary-value less bound supremum))))))

(defun-sk p07a2-has-supremum-p (carrier less set)
  (exists (supremum)
    (p07a2-supremum-p carrier less set supremum)))

(defun-sk p07a2-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p07a2-valid-scalar-set-p carrier set)
      (p07a2-scalar-set-nonempty-p carrier set)
      (p07a2-bounded-above-p carrier less set))
     (p07a2-has-supremum-p carrier less set))))

(defun p07a2-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p07a2-member-p carrier zero)
   (p07a2-member-p carrier one)
   (not (equal zero one))
   (p07a2-field-laws-p
    carrier add multiply negate inverse zero one)
   (p07a2-order-laws-p carrier add multiply zero less)
   (p07a2-binary-value less zero one)
   (p07a2-dedekind-complete-p carrier less)))

(defun p07a2-r-carrier (ctx) (nth 0 ctx))
(defun p07a2-r-zero (ctx) (nth 1 ctx))
(defun p07a2-r-one (ctx) (nth 2 ctx))
(defun p07a2-r-add (ctx) (nth 3 ctx))
(defun p07a2-r-mul (ctx) (nth 4 ctx))
(defun p07a2-r-neg (ctx) (nth 5 ctx))
(defun p07a2-r-inv (ctx) (nth 6 ctx))
(defun p07a2-r-lt (ctx) (nth 7 ctx))

(defun p07a2-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p07a2-real-field-p
    (p07a2-r-carrier ctx)
    (p07a2-r-add ctx)
    (p07a2-r-mul ctx)
    (p07a2-r-neg ctx)
    (p07a2-r-inv ctx)
    (p07a2-r-zero ctx)
    (p07a2-r-one ctx)
    (p07a2-r-lt ctx))))

(defun p07a2-r-add-value (ctx left right)
  (p07a2-binary-value (p07a2-r-add ctx) left right))

(defun p07a2-r-mul-value (ctx left right)
  (p07a2-binary-value (p07a2-r-mul ctx) left right))

(defun p07a2-r-neg-value (ctx value)
  (p07a2-unary-value (p07a2-r-neg ctx) value))

(defun p07a2-r-sub-value (ctx left right)
  (p07a2-r-add-value
   ctx left (p07a2-r-neg-value ctx right)))

(defun p07a2-r-lt-p (ctx left right)
  (if (p07a2-binary-value
       (p07a2-r-lt ctx) left right)
      t
    nil))

(defun p07a2-r-le-p (ctx left right)
  (not (p07a2-r-lt-p ctx right left)))

(defun p07a2-r-abs-value (ctx value)
  (if (p07a2-r-lt-p
       ctx value (p07a2-r-zero ctx))
      (p07a2-r-neg-value ctx value)
    value))

(defun p07a2-positive-real-p (ctx value)
  (and
   (p07a2-member-p (p07a2-r-carrier ctx) value)
   (p07a2-r-lt-p
    ctx (p07a2-r-zero ctx) value)))

(defun p07a2-nonnegative-real-p (ctx value)
  (and
   (p07a2-member-p (p07a2-r-carrier ctx) value)
   (p07a2-r-le-p
    ctx (p07a2-r-zero ctx) value)))

(defun p07a2-two (ctx)
  (p07a2-r-add-value
   ctx (p07a2-r-one ctx) (p07a2-r-one ctx)))

(defun p07a2-four (ctx)
  (let ((two (p07a2-two ctx)))
    (p07a2-r-add-value ctx two two)))

(defun p07a2-point-p (ctx point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (p07a2-member-p
    (p07a2-r-carrier ctx) (nth 0 point))
   (p07a2-member-p
    (p07a2-r-carrier ctx) (nth 1 point))))

(defun p07a2-set-member-p (set point)
  (if (apply$ set (list point)) t nil))

(defun-sk p07a2-valid-plane-set-p (ctx set)
  (forall (point)
    (implies
     (p07a2-set-member-p set point)
     (p07a2-point-p ctx point))))

(defun p07a2-scale-point (ctx scalar point)
  (list
   (p07a2-r-mul-value ctx scalar (nth 0 point))
   (p07a2-r-mul-value ctx scalar (nth 1 point))))

(defun p07a2-add-points (ctx left right)
  (list
   (p07a2-r-add-value
    ctx (nth 0 left) (nth 0 right))
   (p07a2-r-add-value
    ctx (nth 1 left) (nth 1 right))))

(defun-sk p07a2-convex-set-p (ctx set)
  (forall (a b left right)
    (implies
     (and
      (p07a2-nonnegative-real-p ctx a)
      (p07a2-nonnegative-real-p ctx b)
      (equal
       (p07a2-r-add-value ctx a b)
       (p07a2-r-one ctx))
      (p07a2-point-p ctx left)
      (p07a2-point-p ctx right)
      (p07a2-set-member-p set left)
      (p07a2-set-member-p set right))
     (p07a2-set-member-p
      set
      (p07a2-add-points
       ctx
       (p07a2-scale-point ctx a left)
       (p07a2-scale-point ctx b right))))))

(defun-sk p07a2-first-branch-positive-p (ctx set)
  (exists (x y)
    (and
     (p07a2-member-p (p07a2-r-carrier ctx) x)
     (p07a2-member-p (p07a2-r-carrier ctx) y)
     (p07a2-r-lt-p ctx (p07a2-r-zero ctx) x)
     (p07a2-r-lt-p ctx (p07a2-r-zero ctx) y)
     (equal
      (p07a2-r-mul-value ctx x y)
      (p07a2-r-one ctx))
     (p07a2-set-member-p set (list x y)))))

(defun-sk p07a2-first-branch-negative-p (ctx set)
  (exists (x y)
    (and
     (p07a2-member-p (p07a2-r-carrier ctx) x)
     (p07a2-member-p (p07a2-r-carrier ctx) y)
     (p07a2-r-lt-p ctx x (p07a2-r-zero ctx))
     (p07a2-r-lt-p ctx y (p07a2-r-zero ctx))
     (equal
      (p07a2-r-mul-value ctx x y)
      (p07a2-r-one ctx))
     (p07a2-set-member-p set (list x y)))))

(defun-sk p07a2-second-branch-upper-p (ctx set)
  (exists (x y)
    (and
     (p07a2-member-p (p07a2-r-carrier ctx) x)
     (p07a2-member-p (p07a2-r-carrier ctx) y)
     (p07a2-r-lt-p ctx x (p07a2-r-zero ctx))
     (p07a2-r-lt-p ctx (p07a2-r-zero ctx) y)
     (equal
      (p07a2-r-mul-value ctx x y)
      (p07a2-r-neg-value ctx (p07a2-r-one ctx)))
     (p07a2-set-member-p set (list x y)))))

(defun-sk p07a2-second-branch-lower-p (ctx set)
  (exists (x y)
    (and
     (p07a2-member-p (p07a2-r-carrier ctx) x)
     (p07a2-member-p (p07a2-r-carrier ctx) y)
     (p07a2-r-lt-p ctx (p07a2-r-zero ctx) x)
     (p07a2-r-lt-p ctx y (p07a2-r-zero ctx))
     (equal
      (p07a2-r-mul-value ctx x y)
      (p07a2-r-neg-value ctx (p07a2-r-one ctx)))
     (p07a2-set-member-p set (list x y)))))

(defun p07a2-feasible-set-p (ctx set)
  (and
   (tamep-functionp set)
   (p07a2-valid-plane-set-p ctx set)
   (p07a2-convex-set-p ctx set)
   (p07a2-first-branch-positive-p ctx set)
   (p07a2-first-branch-negative-p ctx set)
   (p07a2-second-branch-upper-p ctx set)
   (p07a2-second-branch-lower-p ctx set)))

;; A rectangle is (x-lower x-upper y-lower y-upper). Membership uses strict
;; inequalities, so a degenerate rectangle is empty and has area zero.

(defun p07a2-rectangle-p (ctx rectangle)
  (and
   (true-listp rectangle)
   (equal (len rectangle) 4)
   (p07a2-member-p
    (p07a2-r-carrier ctx) (nth 0 rectangle))
   (p07a2-member-p
    (p07a2-r-carrier ctx) (nth 1 rectangle))
   (p07a2-member-p
    (p07a2-r-carrier ctx) (nth 2 rectangle))
   (p07a2-member-p
    (p07a2-r-carrier ctx) (nth 3 rectangle))
   (p07a2-r-le-p
    ctx (nth 0 rectangle) (nth 1 rectangle))
   (p07a2-r-le-p
    ctx (nth 2 rectangle) (nth 3 rectangle))))

(defun p07a2-point-in-rectangle-p (ctx point rectangle)
  (and
   (p07a2-point-p ctx point)
   (p07a2-rectangle-p ctx rectangle)
   (p07a2-r-lt-p
    ctx (nth 0 rectangle) (nth 0 point))
   (p07a2-r-lt-p
    ctx (nth 0 point) (nth 1 rectangle))
   (p07a2-r-lt-p
    ctx (nth 2 rectangle) (nth 1 point))
   (p07a2-r-lt-p
    ctx (nth 1 point) (nth 3 rectangle))))

(defun p07a2-rectangle-area (ctx rectangle)
  (p07a2-r-mul-value
   ctx
   (p07a2-r-sub-value
    ctx (nth 1 rectangle) (nth 0 rectangle))
   (p07a2-r-sub-value
    ctx (nth 3 rectangle) (nth 2 rectangle))))

(defun p07a2-cover-rectangle (cover index)
  (apply$ cover (list index)))

(defun-sk p07a2-valid-rectangle-cover-sequence-p
    (ctx cover)
  (forall (index)
    (implies
     (natp index)
     (p07a2-rectangle-p
      ctx (p07a2-cover-rectangle cover index)))))

(defun p07a2-cover-partial-area (ctx cover count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p07a2-r-zero ctx)
    (let ((index (- (nfix count) 1)))
      (p07a2-r-add-value
       ctx
       (p07a2-cover-partial-area ctx cover index)
       (p07a2-rectangle-area
        ctx (p07a2-cover-rectangle cover index))))))

(defun-sk p07a2-cover-area-tail-p
    (ctx cover total epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (p07a2-r-lt-p
      ctx
      (p07a2-r-abs-value
       ctx
       (p07a2-r-sub-value
        ctx
        (p07a2-cover-partial-area ctx cover count)
        total))
      epsilon))))

(defun-sk p07a2-cover-area-cutoff-exists-p
    (ctx cover total epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p07a2-cover-area-tail-p
      ctx cover total epsilon cutoff))))

(defun-sk p07a2-cover-area-converges-to-p
    (ctx cover total)
  (forall (epsilon)
    (implies
     (p07a2-positive-real-p ctx epsilon)
     (p07a2-cover-area-cutoff-exists-p
      ctx cover total epsilon))))

(defun p07a2-finite-cover-cost-p (ctx cover total)
  (and
   (tamep-functionp cover)
   (p07a2-valid-rectangle-cover-sequence-p ctx cover)
   (p07a2-nonnegative-real-p ctx total)
   (p07a2-cover-area-converges-to-p
    ctx cover total)))

(defun-sk p07a2-set-point-covered-p
    (ctx cover point)
  (exists (index)
    (and
     (natp index)
     (p07a2-point-in-rectangle-p
      ctx point (p07a2-cover-rectangle cover index)))))

(defun-sk p07a2-set-cover-p (ctx set cover)
  (forall (point)
    (implies
     (and
      (p07a2-point-p ctx point)
      (p07a2-set-member-p set point))
     (p07a2-set-point-covered-p
      ctx cover point))))

;; AREA is the infimum of all finite total costs of countable open-rectangle
;; covers: it is a lower bound, and covers occur within every positive
;; epsilon above it.

(defun-sk p07a2-area-lower-bound-p (ctx set area)
  (forall (cover total)
    (implies
     (and
      (p07a2-finite-cover-cost-p ctx cover total)
      (p07a2-set-cover-p ctx set cover))
     (p07a2-r-le-p ctx area total))))

(defun-sk p07a2-near-cover-exists-p
    (ctx set area epsilon)
  (exists (cover total)
    (and
     (p07a2-finite-cover-cost-p ctx cover total)
     (p07a2-set-cover-p ctx set cover)
     (p07a2-r-lt-p
      ctx total (p07a2-r-add-value ctx area epsilon)))))

(defun-sk p07a2-near-covers-p (ctx set area)
  (forall (epsilon)
    (implies
     (p07a2-positive-real-p ctx epsilon)
     (p07a2-near-cover-exists-p
      ctx set area epsilon))))

(defun p07a2-outer-area-p (ctx set area)
  (and
   (p07a2-nonnegative-real-p ctx area)
   (p07a2-area-lower-bound-p ctx set area)
   (p07a2-near-covers-p ctx set area)))

(defun-sk p07a2-four-attained-p (ctx)
  (exists (set)
    (and
     (p07a2-feasible-set-p ctx set)
     (p07a2-outer-area-p
      ctx set (p07a2-four ctx)))))

(defun-sk p07a2-four-lower-bound-p (ctx)
  (forall (set)
    (implies
     (p07a2-feasible-set-p ctx set)
     (p07a2-area-lower-bound-p
      ctx set (p07a2-four ctx)))))

(defun-sk putnambench-putnam-2007-a2-statement ()
  (forall (ctx)
    (implies
     (p07a2-context-p ctx)
     (and
      (p07a2-four-attained-p ctx)
      (p07a2-four-lower-bound-p ctx)))))

(value-triple :itpeval-statement-checked)
:q
