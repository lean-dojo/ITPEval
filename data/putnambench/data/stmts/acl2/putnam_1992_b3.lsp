;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_b3:
;; the Lebesgue area of the real points whose recursively defined sequence
;; converges is 4 plus pi. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real scalars up to the
;; unique ordered-field isomorphism. Points are pairs over that field, and the
;; sequence family is an unbounded tame APPLY$ function object. All recurrence
;; and convergence quantifiers remain explicit.
;;
;; For a bounded planar set, Lebesgue outer area is equivalently the infimum
;; of the convergent total areas of countable open axis-aligned rectangle
;; covers. The two outer-area predicates below use this definition directly,
;; so neither the real plane nor the measured sets are replaced by finite
;; grids or rational samples. Pi is defined as the outer area of the open unit
;; disk, which is the standard geometric definition in any presentation of
;; the real field.

(defun p92b3-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun p92b3-unary-value (operation x)
  (apply$ operation (list x)))

(defun p92b3-binary-value (operation x y)
  (apply$ operation (list x y)))

(defun-sk p92b3-valid-scalar-set-p (carrier set)
  (forall (x)
    (implies
     (apply$ set (list x))
     (p92b3-member-p carrier x))))

(defun-sk p92b3-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and
      (p92b3-member-p carrier x)
      (p92b3-member-p carrier y)
      (p92b3-member-p carrier z))
     (and
      (p92b3-member-p carrier
                      (p92b3-binary-value add x y))
      (p92b3-member-p carrier
                      (p92b3-binary-value multiply x y))
      (p92b3-member-p carrier
                      (p92b3-unary-value negate x))
      (implies
       (not (equal x zero))
       (p92b3-member-p carrier
                       (p92b3-unary-value inverse x)))
      (equal
       (p92b3-binary-value
        add (p92b3-binary-value add x y) z)
       (p92b3-binary-value
        add x (p92b3-binary-value add y z)))
      (equal
       (p92b3-binary-value add x y)
       (p92b3-binary-value add y x))
      (equal (p92b3-binary-value add x zero) x)
      (equal
       (p92b3-binary-value add x (p92b3-unary-value negate x))
       zero)
      (equal
       (p92b3-binary-value
        multiply (p92b3-binary-value multiply x y) z)
       (p92b3-binary-value
        multiply x (p92b3-binary-value multiply y z)))
      (equal
       (p92b3-binary-value multiply x y)
       (p92b3-binary-value multiply y x))
      (equal (p92b3-binary-value multiply x one) x)
      (implies
       (not (equal x zero))
       (equal
        (p92b3-binary-value
         multiply x (p92b3-unary-value inverse x))
        one))
      (equal
       (p92b3-binary-value
        multiply x (p92b3-binary-value add y z))
       (p92b3-binary-value
        add
        (p92b3-binary-value multiply x y)
        (p92b3-binary-value multiply x z)))))))

(defun-sk p92b3-order-laws-p
    (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and
      (p92b3-member-p carrier x)
      (p92b3-member-p carrier y)
      (p92b3-member-p carrier z))
     (and
      (not (p92b3-binary-value less x x))
      (or
       (equal x y)
       (p92b3-binary-value less x y)
       (p92b3-binary-value less y x))
      (implies
       (and
        (p92b3-binary-value less x y)
        (p92b3-binary-value less y z))
       (p92b3-binary-value less x z))
      (implies
       (p92b3-binary-value less x y)
       (p92b3-binary-value
        less
        (p92b3-binary-value add x z)
        (p92b3-binary-value add y z)))
      (implies
       (and
        (p92b3-binary-value less zero x)
        (p92b3-binary-value less zero y))
       (p92b3-binary-value
        less zero (p92b3-binary-value multiply x y)))))))

(defun-sk p92b3-scalar-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (p92b3-member-p carrier x)
     (apply$ set (list x)))))

(defun-sk p92b3-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and
      (p92b3-member-p carrier x)
      (apply$ set (list x)))
     (not (p92b3-binary-value less bound x)))))

(defun-sk p92b3-bounded-above-p (carrier less set)
  (exists (bound)
    (and
     (p92b3-member-p carrier bound)
     (p92b3-upper-bound-p carrier less set bound))))

(defun-sk p92b3-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (p92b3-member-p carrier supremum)
     (p92b3-upper-bound-p carrier less set supremum)
     (implies
      (and
       (p92b3-member-p carrier bound)
       (p92b3-upper-bound-p carrier less set bound))
      (not (p92b3-binary-value less bound supremum))))))

(defun-sk p92b3-has-supremum-p (carrier less set)
  (exists (supremum)
    (p92b3-supremum-p carrier less set supremum)))

(defun-sk p92b3-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (p92b3-valid-scalar-set-p carrier set)
      (p92b3-scalar-set-nonempty-p carrier set)
      (p92b3-bounded-above-p carrier less set))
     (p92b3-has-supremum-p carrier less set))))

(defun p92b3-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (p92b3-member-p carrier zero)
   (p92b3-member-p carrier one)
   (not (equal zero one))
   (p92b3-field-laws-p
    carrier add multiply negate inverse zero one)
   (p92b3-order-laws-p carrier add multiply zero less)
   (p92b3-binary-value less zero one)
   (p92b3-dedekind-complete-p carrier less)))

(defun p92b3-r-carrier (ctx) (nth 0 ctx))
(defun p92b3-r-zero (ctx) (nth 1 ctx))
(defun p92b3-r-one (ctx) (nth 2 ctx))
(defun p92b3-r-add (ctx) (nth 3 ctx))
(defun p92b3-r-mul (ctx) (nth 4 ctx))
(defun p92b3-r-neg (ctx) (nth 5 ctx))
(defun p92b3-r-inv (ctx) (nth 6 ctx))
(defun p92b3-r-lt (ctx) (nth 7 ctx))

(defun p92b3-context-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (p92b3-real-field-p
    (p92b3-r-carrier ctx)
    (p92b3-r-add ctx)
    (p92b3-r-mul ctx)
    (p92b3-r-neg ctx)
    (p92b3-r-inv ctx)
    (p92b3-r-zero ctx)
    (p92b3-r-one ctx)
    (p92b3-r-lt ctx))))

(defun p92b3-r-add-value (ctx x y)
  (p92b3-binary-value (p92b3-r-add ctx) x y))

(defun p92b3-r-mul-value (ctx x y)
  (p92b3-binary-value (p92b3-r-mul ctx) x y))

(defun p92b3-r-neg-value (ctx x)
  (p92b3-unary-value (p92b3-r-neg ctx) x))

(defun p92b3-r-inv-value (ctx x)
  (p92b3-unary-value (p92b3-r-inv ctx) x))

(defun p92b3-r-sub-value (ctx x y)
  (p92b3-r-add-value ctx x (p92b3-r-neg-value ctx y)))

(defun p92b3-r-lt-p (ctx x y)
  (if (p92b3-binary-value (p92b3-r-lt ctx) x y) t nil))

(defun p92b3-r-le-p (ctx x y)
  (not (p92b3-r-lt-p ctx y x)))

(defun p92b3-r-abs-value (ctx x)
  (if (p92b3-r-lt-p ctx x (p92b3-r-zero ctx))
      (p92b3-r-neg-value ctx x)
    x))

(defun p92b3-positive-real-p (ctx x)
  (and
   (p92b3-member-p (p92b3-r-carrier ctx) x)
   (p92b3-r-lt-p ctx (p92b3-r-zero ctx) x)))

(defun p92b3-nonnegative-real-p (ctx x)
  (and
   (p92b3-member-p (p92b3-r-carrier ctx) x)
   (p92b3-r-le-p ctx (p92b3-r-zero ctx) x)))

(defun p92b3-two (ctx)
  (p92b3-r-add-value
   ctx (p92b3-r-one ctx) (p92b3-r-one ctx)))

(defun p92b3-four (ctx)
  (p92b3-r-add-value
   ctx (p92b3-two ctx) (p92b3-two ctx)))

(defun p92b3-half (ctx)
  (p92b3-r-inv-value ctx (p92b3-two ctx)))

(defun p92b3-point-p (ctx point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (p92b3-member-p (p92b3-r-carrier ctx) (nth 0 point))
   (p92b3-member-p (p92b3-r-carrier ctx) (nth 1 point))))

(defun p92b3-sequence-value (family point n)
  (apply$ family (list point n)))

(defun-sk p92b3-real-sequence-family-p (ctx family)
  (forall (point n)
    (implies
     (and
      (p92b3-point-p ctx point)
      (natp n))
     (p92b3-member-p
      (p92b3-r-carrier ctx)
      (p92b3-sequence-value family point n)))))

(defun-sk p92b3-recurrence-p (ctx family)
  (forall (point n)
    (implies
     (and
      (p92b3-point-p ctx point)
      (natp n))
     (and
      (implies
       (equal n 0)
       (equal
        (p92b3-sequence-value family point 0)
        (nth 0 point)))
      (equal
       (p92b3-sequence-value family point (+ n 1))
       (p92b3-r-mul-value
        ctx
        (p92b3-r-add-value
         ctx
         (p92b3-r-mul-value
          ctx
          (p92b3-sequence-value family point n)
          (p92b3-sequence-value family point n))
         (p92b3-r-mul-value
          ctx (nth 1 point) (nth 1 point)))
        (p92b3-half ctx)))))))

(defun-sk p92b3-limit-tail-p
    (ctx family point limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (<= cutoff n))
     (p92b3-r-lt-p
      ctx
      (p92b3-r-abs-value
       ctx
       (p92b3-r-sub-value
        ctx
        (p92b3-sequence-value family point n)
        limit))
      epsilon))))

(defun-sk p92b3-limit-cutoff-exists-p
    (ctx family point limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p92b3-limit-tail-p
      ctx family point limit epsilon cutoff))))

(defun-sk p92b3-converges-to-p (ctx family point limit)
  (forall (epsilon)
    (implies
     (p92b3-positive-real-p ctx epsilon)
     (p92b3-limit-cutoff-exists-p
      ctx family point limit epsilon))))

(defun-sk p92b3-converges-p (ctx family point)
  (exists (limit)
    (and
     (p92b3-member-p (p92b3-r-carrier ctx) limit)
     (p92b3-converges-to-p ctx family point limit))))

;; A rectangle is (x-lower x-upper y-lower y-upper), with open sides.

(defun p92b3-rectangle-p (ctx rectangle)
  (and
   (true-listp rectangle)
   (equal (len rectangle) 4)
   (p92b3-member-p
    (p92b3-r-carrier ctx) (nth 0 rectangle))
   (p92b3-member-p
    (p92b3-r-carrier ctx) (nth 1 rectangle))
   (p92b3-member-p
    (p92b3-r-carrier ctx) (nth 2 rectangle))
   (p92b3-member-p
    (p92b3-r-carrier ctx) (nth 3 rectangle))
   (p92b3-r-lt-p ctx (nth 0 rectangle) (nth 1 rectangle))
   (p92b3-r-lt-p ctx (nth 2 rectangle) (nth 3 rectangle))))

(defun p92b3-point-in-rectangle-p (ctx point rectangle)
  (and
   (p92b3-point-p ctx point)
   (p92b3-rectangle-p ctx rectangle)
   (p92b3-r-lt-p ctx (nth 0 rectangle) (nth 0 point))
   (p92b3-r-lt-p ctx (nth 0 point) (nth 1 rectangle))
   (p92b3-r-lt-p ctx (nth 2 rectangle) (nth 1 point))
   (p92b3-r-lt-p ctx (nth 1 point) (nth 3 rectangle))))

(defun p92b3-rectangle-area (ctx rectangle)
  (p92b3-r-mul-value
   ctx
   (p92b3-r-sub-value
    ctx (nth 1 rectangle) (nth 0 rectangle))
   (p92b3-r-sub-value
    ctx (nth 3 rectangle) (nth 2 rectangle))))

(defun p92b3-cover-rectangle (cover n)
  (apply$ cover (list n)))

(defun-sk p92b3-valid-rectangle-cover-sequence-p (ctx cover)
  (forall (n)
    (implies
     (natp n)
     (p92b3-rectangle-p
      ctx (p92b3-cover-rectangle cover n)))))

(defun p92b3-cover-partial-area (ctx cover count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (p92b3-r-zero ctx)
    (let ((index (- (nfix count) 1)))
      (p92b3-r-add-value
       ctx
       (p92b3-cover-partial-area ctx cover index)
       (p92b3-rectangle-area
        ctx (p92b3-cover-rectangle cover index))))))

(defun-sk p92b3-cover-area-tail-p
    (ctx cover total epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (<= cutoff count))
     (p92b3-r-lt-p
      ctx
      (p92b3-r-abs-value
       ctx
       (p92b3-r-sub-value
        ctx
        (p92b3-cover-partial-area ctx cover count)
        total))
      epsilon))))

(defun-sk p92b3-cover-area-cutoff-exists-p
    (ctx cover total epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (p92b3-cover-area-tail-p
      ctx cover total epsilon cutoff))))

(defun-sk p92b3-cover-area-converges-to-p
    (ctx cover total)
  (forall (epsilon)
    (implies
     (p92b3-positive-real-p ctx epsilon)
     (p92b3-cover-area-cutoff-exists-p
      ctx cover total epsilon))))

(defun p92b3-finite-cover-cost-p (ctx cover total)
  (and
   (tamep-functionp cover)
   (p92b3-valid-rectangle-cover-sequence-p ctx cover)
   (p92b3-nonnegative-real-p ctx total)
   (p92b3-cover-area-converges-to-p ctx cover total)))

(defun-sk p92b3-region-point-covered-p
    (ctx family cover point)
  (exists (n)
    (and
     (natp n)
     (p92b3-point-in-rectangle-p
      ctx point (p92b3-cover-rectangle cover n)))))

(defun-sk p92b3-region-cover-p (ctx family cover)
  (forall (point)
    (implies
     (and
      (p92b3-point-p ctx point)
      (p92b3-converges-p ctx family point))
     (p92b3-region-point-covered-p
      ctx family cover point))))

(defun p92b3-unit-disk-point-p (ctx point)
  (and
   (p92b3-point-p ctx point)
   (p92b3-r-lt-p
    ctx
    (p92b3-r-add-value
     ctx
     (p92b3-r-mul-value
      ctx (nth 0 point) (nth 0 point))
     (p92b3-r-mul-value
      ctx (nth 1 point) (nth 1 point)))
    (p92b3-r-one ctx))))

(defun-sk p92b3-unit-disk-point-covered-p
    (ctx cover point)
  (exists (n)
    (and
     (natp n)
     (p92b3-point-in-rectangle-p
      ctx point (p92b3-cover-rectangle cover n)))))

(defun-sk p92b3-unit-disk-cover-p (ctx cover)
  (forall (point)
    (implies
     (p92b3-unit-disk-point-p ctx point)
     (p92b3-unit-disk-point-covered-p
      ctx cover point))))

;; AREA is the infimum of all finite total costs of countable open-rectangle
;; covers: it is a lower bound, and covers occur within every positive
;; epsilon above it.

(defun-sk p92b3-region-area-lower-bound-p
    (ctx family area)
  (forall (cover total)
    (implies
     (and
      (p92b3-finite-cover-cost-p ctx cover total)
      (p92b3-region-cover-p ctx family cover))
     (p92b3-r-le-p ctx area total))))

(defun-sk p92b3-region-near-cover-exists-p
    (ctx family area epsilon)
  (exists (cover total)
    (and
     (p92b3-finite-cover-cost-p ctx cover total)
     (p92b3-region-cover-p ctx family cover)
     (p92b3-r-lt-p
      ctx total (p92b3-r-add-value ctx area epsilon)))))

(defun-sk p92b3-region-near-covers-p
    (ctx family area)
  (forall (epsilon)
    (implies
     (p92b3-positive-real-p ctx epsilon)
     (p92b3-region-near-cover-exists-p
      ctx family area epsilon))))

(defun p92b3-region-outer-area-p (ctx family area)
  (and
   (p92b3-nonnegative-real-p ctx area)
   (p92b3-region-area-lower-bound-p ctx family area)
   (p92b3-region-near-covers-p ctx family area)))

(defun-sk p92b3-unit-disk-area-lower-bound-p (ctx area)
  (forall (cover total)
    (implies
     (and
      (p92b3-finite-cover-cost-p ctx cover total)
      (p92b3-unit-disk-cover-p ctx cover))
     (p92b3-r-le-p ctx area total))))

(defun-sk p92b3-unit-disk-near-cover-exists-p
    (ctx area epsilon)
  (exists (cover total)
    (and
     (p92b3-finite-cover-cost-p ctx cover total)
     (p92b3-unit-disk-cover-p ctx cover)
     (p92b3-r-lt-p
      ctx total (p92b3-r-add-value ctx area epsilon)))))

(defun-sk p92b3-unit-disk-near-covers-p (ctx area)
  (forall (epsilon)
    (implies
     (p92b3-positive-real-p ctx epsilon)
     (p92b3-unit-disk-near-cover-exists-p
      ctx area epsilon))))

(defun p92b3-unit-disk-outer-area-p (ctx area)
  (and
   (p92b3-nonnegative-real-p ctx area)
   (p92b3-unit-disk-area-lower-bound-p ctx area)
   (p92b3-unit-disk-near-covers-p ctx area)))

(defun-sk putnambench-putnam-1992-b3-statement (ctx family)
  (exists (region-area unit-disk-area)
    (implies
     (and
      (p92b3-context-p ctx)
      (tamep-functionp family)
      (p92b3-real-sequence-family-p ctx family)
      (p92b3-recurrence-p ctx family))
     (and
      (p92b3-region-outer-area-p
       ctx family region-area)
      (p92b3-unit-disk-outer-area-p
       ctx unit-disk-area)
      (equal
       region-area
       (p92b3-r-add-value
        ctx (p92b3-four ctx) unit-disk-area))))))

(value-triple :itpeval-statement-checked)
:q
