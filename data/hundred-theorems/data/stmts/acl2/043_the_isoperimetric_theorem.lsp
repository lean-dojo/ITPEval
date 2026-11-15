;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__043, "The Isoperimetric Theorem": every rectifiable
;; simple closed planar path of length L encloses area at most L^2/(4*pi), and
;; equality implies that its path image is a Euclidean circle. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar arguments present the real numbers as a Dedekind-complete
;; ordered field. Paths and auxiliary functions are arbitrary tame APPLY$
;; functions on the full represented real unit interval, not finite tables.

(defun ht043-member-p (carrier x)
  (if (apply$ carrier (list x)) t nil))

(defun ht043-unary (function x)
  (apply$ function (list x)))

(defun ht043-binary (function x y)
  (apply$ function (list x y)))

(defun-sk ht043-field-laws-p
    (carrier add multiply negate inverse zero one)
  (forall (x y z)
    (implies
     (and (ht043-member-p carrier x)
          (ht043-member-p carrier y)
          (ht043-member-p carrier z))
     (and
      (ht043-member-p carrier (ht043-binary add x y))
      (ht043-member-p carrier (ht043-binary multiply x y))
      (ht043-member-p carrier (ht043-unary negate x))
      (ht043-member-p carrier (ht043-unary inverse x))
      (equal (ht043-binary add (ht043-binary add x y) z)
             (ht043-binary add x (ht043-binary add y z)))
      (equal (ht043-binary add x y) (ht043-binary add y x))
      (equal (ht043-binary add x zero) x)
      (equal (ht043-binary add x (ht043-unary negate x)) zero)
      (equal
       (ht043-binary multiply (ht043-binary multiply x y) z)
       (ht043-binary multiply x (ht043-binary multiply y z)))
      (equal (ht043-binary multiply x y)
             (ht043-binary multiply y x))
      (equal (ht043-binary multiply x one) x)
      (implies (equal x zero)
               (equal (ht043-unary inverse x) zero))
      (implies
       (not (equal x zero))
       (equal (ht043-binary multiply x (ht043-unary inverse x)) one))
      (equal
       (ht043-binary multiply x (ht043-binary add y z))
       (ht043-binary
        add
        (ht043-binary multiply x y)
        (ht043-binary multiply x z)))))))

(defun-sk ht043-order-laws-p (carrier add multiply zero less)
  (forall (x y z)
    (implies
     (and (ht043-member-p carrier x)
          (ht043-member-p carrier y)
          (ht043-member-p carrier z))
     (and
      (not (ht043-binary less x x))
      (or (equal x y)
          (ht043-binary less x y)
          (ht043-binary less y x))
      (implies
       (and (ht043-binary less x y)
            (ht043-binary less y z))
       (ht043-binary less x z))
      (implies
       (ht043-binary less x y)
       (ht043-binary
        less (ht043-binary add x z) (ht043-binary add y z)))
      (implies
       (and (ht043-binary less zero x)
            (ht043-binary less zero y))
       (ht043-binary less zero (ht043-binary multiply x y)))))))

(defun ht043-less-p (less x y)
  (if (ht043-binary less x y) t nil))

(defun ht043-leq-p (less x y)
  (not (ht043-less-p less y x)))

(defun-sk ht043-set-nonempty-p (carrier set)
  (exists (x)
    (and (ht043-member-p carrier x)
         (apply$ set (list x)))))

(defun-sk ht043-upper-bound-p (carrier less set bound)
  (forall (x)
    (implies
     (and (ht043-member-p carrier x)
          (apply$ set (list x)))
     (ht043-leq-p less x bound))))

(defun-sk ht043-bounded-above-p (carrier less set)
  (exists (bound)
    (and (ht043-member-p carrier bound)
         (ht043-upper-bound-p carrier less set bound))))

(defun-sk ht043-is-supremum-p (carrier less set supremum)
  (forall (bound)
    (and
     (ht043-member-p carrier supremum)
     (ht043-upper-bound-p carrier less set supremum)
     (implies
      (and (ht043-member-p carrier bound)
           (ht043-upper-bound-p carrier less set bound))
      (ht043-leq-p less supremum bound)))))

(defun-sk ht043-has-supremum-p (carrier less set)
  (exists (supremum)
    (ht043-is-supremum-p carrier less set supremum)))

(defun-sk ht043-dedekind-complete-p (carrier less)
  (forall (set)
    (implies
     (and (tamep-functionp set)
          (ht043-set-nonempty-p carrier set)
          (ht043-bounded-above-p carrier less set))
     (ht043-has-supremum-p carrier less set))))

(defun ht043-real-field-p
    (carrier add multiply negate inverse zero one less)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (tamep-functionp inverse)
   (tamep-functionp less)
   (ht043-member-p carrier zero)
   (ht043-member-p carrier one)
   (not (equal zero one))
   (ht043-field-laws-p
    carrier add multiply negate inverse zero one)
   (ht043-order-laws-p carrier add multiply zero less)
   (ht043-less-p less zero one)
   (ht043-dedekind-complete-p carrier less)))

(defun ht043-add (add x y)
  (ht043-binary add x y))

(defun ht043-neg (negate x)
  (ht043-unary negate x))

(defun ht043-sub (add negate x y)
  (ht043-add add x (ht043-neg negate y)))

(defun ht043-mul (multiply x y)
  (ht043-binary multiply x y))

(defun ht043-inv (inverse x)
  (ht043-unary inverse x))

(defun ht043-div (multiply inverse x y)
  (ht043-mul multiply x (ht043-inv inverse y)))

(defun ht043-square (multiply x)
  (ht043-mul multiply x x))

(defun ht043-abs (less negate zero x)
  (if (ht043-less-p less x zero)
      (ht043-neg negate x)
    x))

(defun ht043-max (less x y)
  (if (ht043-less-p less x y) y x))

(defun ht043-positive-p (carrier less zero x)
  (and (ht043-member-p carrier x)
       (ht043-less-p less zero x)))

(defun ht043-nat (add zero one n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      zero
    (ht043-add add one (ht043-nat add zero one (1- n)))))

(defun ht043-four (add zero one)
  (ht043-nat add zero one 4))

(defun-sk ht043-unary-real-function-p (carrier function)
  (forall (x)
    (implies
     (ht043-member-p carrier x)
     (ht043-member-p carrier (ht043-unary function x)))))

(defun ht043-valid-unary-function-p (carrier function)
  (and (tamep-functionp function)
       (ht043-unary-real-function-p carrier function)))

;; SQRT is fixed by the nonnegative square-root characterization.

(defun-sk ht043-square-root-laws-p
    (carrier multiply zero less square-root)
  (forall (x)
    (implies
     (and (ht043-member-p carrier x)
          (ht043-leq-p less zero x))
     (let ((root (ht043-unary square-root x)))
       (and
        (ht043-member-p carrier root)
        (ht043-leq-p less zero root)
        (equal (ht043-square multiply root) x))))))

(defun ht043-square-root-p
    (carrier multiply zero less square-root)
  (and
   (tamep-functionp square-root)
   (ht043-square-root-laws-p
    carrier multiply zero less square-root)))

(defun ht043-plane-distance
    (add multiply negate square-root x1 y1 x2 y2)
  (let ((dx (ht043-sub add negate x1 x2))
        (dy (ht043-sub add negate y1 y2)))
    (ht043-unary
     square-root
     (ht043-add
      add
      (ht043-square multiply dx)
      (ht043-square multiply dy)))))

;; Pi is fixed as the limit of Machin's arctangent series.

(defun ht043-power (multiply one base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (ht043-mul
     multiply base
     (ht043-power multiply one base (1- exponent)))))

(defun ht043-arctan-prefix
    (add multiply negate inverse zero one z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      zero
    (let* ((index (1- terms))
           (exponent (+ (* 2 index) 1))
           (denominator (ht043-nat add zero one exponent))
           (unsigned
            (ht043-div
             multiply inverse
             (ht043-power multiply one z exponent)
             denominator))
           (term
            (if (equal (mod index 2) 0)
                unsigned
              (ht043-neg negate unsigned))))
      (ht043-add
       add
       (ht043-arctan-prefix
        add multiply negate inverse zero one z index)
       term))))

(defun ht043-pi-prefix
    (add multiply negate inverse zero one terms)
  (let* ((five (ht043-nat add zero one 5))
         (two-thirty-nine (ht043-nat add zero one 239))
         (sixteen (ht043-nat add zero one 16))
         (four (ht043-four add zero one)))
    (ht043-sub
     add negate
     (ht043-mul
      multiply sixteen
      (ht043-arctan-prefix
       add multiply negate inverse zero one
       (ht043-div multiply inverse one five)
       terms))
     (ht043-mul
      multiply four
      (ht043-arctan-prefix
       add multiply negate inverse zero one
       (ht043-div multiply inverse one two-thirty-nine)
       terms)))))

(defun-sk ht043-pi-tail-p
    (carrier add multiply negate inverse zero one less
             pi-value epsilon cutoff)
  (forall (terms)
    (implies
     (and (natp terms)
          (natp cutoff)
          (<= cutoff terms))
     (ht043-less-p
      less
      (ht043-abs
       less negate zero
       (ht043-sub
        add negate
        (ht043-pi-prefix
         add multiply negate inverse zero one terms)
        pi-value))
      epsilon))))

(defun-sk ht043-pi-cutoff-exists-p
    (carrier add multiply negate inverse zero one less
             pi-value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht043-pi-tail-p
      carrier add multiply negate inverse zero one less
      pi-value epsilon cutoff))))

(defun-sk ht043-pi-limit-p
    (carrier add multiply negate inverse zero one less pi-value)
  (forall (epsilon)
    (implies
     (ht043-positive-p carrier less zero epsilon)
     (ht043-pi-cutoff-exists-p
      carrier add multiply negate inverse zero one less
      pi-value epsilon))))

(defun ht043-pi-p
    (carrier add multiply negate inverse zero one less pi-value)
  (and
   (ht043-positive-p carrier less zero pi-value)
   (ht043-pi-limit-p
    carrier add multiply negate inverse zero one less pi-value)))

;; Continuity and the standard simple-closed-path condition on [0,1].

(defun ht043-in-unit-interval-p (less zero one x)
  (and (ht043-leq-p less zero x)
       (ht043-leq-p less x one)))

(defun-sk ht043-continuity-neighborhood-p
    (carrier gx gy add multiply negate square-root
             zero one less parameter epsilon delta)
  (forall (other)
    (implies
     (and
      (ht043-member-p carrier other)
      (ht043-in-unit-interval-p less zero one other)
      (ht043-less-p
       less
       (ht043-abs
        less negate zero
        (ht043-sub add negate other parameter))
       delta))
     (ht043-less-p
      less
      (ht043-plane-distance
       add multiply negate square-root
       (ht043-unary gx other)
       (ht043-unary gy other)
       (ht043-unary gx parameter)
       (ht043-unary gy parameter))
      epsilon))))

(defun-sk ht043-continuity-radius-exists-p
    (carrier gx gy add multiply negate square-root
             zero one less parameter epsilon)
  (exists (delta)
    (and
     (ht043-positive-p carrier less zero delta)
     (ht043-continuity-neighborhood-p
      carrier gx gy add multiply negate square-root
      zero one less parameter epsilon delta))))

(defun-sk ht043-continuous-path-p
    (carrier gx gy add multiply negate square-root zero one less)
  (forall (parameter epsilon)
    (implies
     (and
      (ht043-member-p carrier parameter)
      (ht043-in-unit-interval-p less zero one parameter)
      (ht043-positive-p carrier less zero epsilon))
     (ht043-continuity-radius-exists-p
      carrier gx gy add multiply negate square-root
      zero one less parameter epsilon))))

(defun-sk ht043-simple-path-p (carrier gx gy zero one less)
  (forall (s time)
    (implies
     (and
      (ht043-member-p carrier s)
      (ht043-member-p carrier time)
      (ht043-in-unit-interval-p less zero one s)
      (ht043-in-unit-interval-p less zero one time)
      (equal (ht043-unary gx s) (ht043-unary gx time))
      (equal (ht043-unary gy s) (ht043-unary gy time)))
     (or
      (equal s time)
      (and (equal s zero) (equal time one))
      (and (equal s one) (equal time zero))))))

(defun ht043-closed-path-p (gx gy zero one)
  (and
   (equal (ht043-unary gx zero) (ht043-unary gx one))
   (equal (ht043-unary gy zero) (ht043-unary gy one))))

(defun-sk ht043-path-hits-point-p (carrier gx gy zero one less x y)
  (exists (parameter)
    (and
     (ht043-member-p carrier parameter)
     (ht043-in-unit-interval-p less zero one parameter)
     (equal (ht043-unary gx parameter) x)
     (equal (ht043-unary gy parameter) y))))

;; Rectifiability and path_length(g)=L are expressed together by saying that
;; L is the least upper bound of all Euclidean polygonal variation sums over
;; arbitrary finite partitions of the full unit interval.

(defun ht043-partition-from-p
    (carrier less current finish points)
  (if (consp points)
      (let ((next (car points)))
        (and
         (ht043-member-p carrier next)
         (ht043-less-p less current next)
         (ht043-partition-from-p
          carrier less next finish (cdr points))))
    (and (equal points nil)
         (equal current finish))))

(defun ht043-partition-p (carrier less zero one points)
  (and
   (true-listp points)
   (ht043-partition-from-p carrier less zero one points)))

(defun ht043-path-variation-sum
    (gx gy add multiply negate square-root start points)
  (if (consp points)
      (let ((next (car points)))
        (ht043-add
         add
         (ht043-plane-distance
          add multiply negate square-root
          (ht043-unary gx start)
          (ht043-unary gy start)
          (ht043-unary gx next)
          (ht043-unary gy next))
         (ht043-path-variation-sum
          gx gy add multiply negate square-root next (cdr points))))
    (ht043-sub add negate start start)))

(defun-sk ht043-path-length-upper-bound-p
    (carrier gx gy add multiply negate square-root
             zero one less bound)
  (forall (points)
    (implies
     (ht043-partition-p carrier less zero one points)
     (ht043-leq-p
      less
      (ht043-path-variation-sum
       gx gy add multiply negate square-root zero points)
      bound))))

(defun-sk ht043-path-length-least-p
    (carrier gx gy add multiply negate square-root
             zero one less length)
  (forall (bound)
    (implies
     (and
      (ht043-member-p carrier bound)
      (ht043-path-length-upper-bound-p
       carrier gx gy add multiply negate square-root
       zero one less bound))
     (ht043-leq-p less length bound))))

(defun ht043-has-path-length-p
    (carrier gx gy add multiply negate square-root
             zero one less length)
  (and
   (ht043-member-p carrier length)
   (ht043-path-length-upper-bound-p
    carrier gx gy add multiply negate square-root
    zero one less length)
   (ht043-path-length-least-p
    carrier gx gy add multiply negate square-root
    zero one less length)))

;; A complement point is outside when it can be joined, through the
;; complement of the path image, to a point beyond a square containing the
;; image. Its negation is exactly membership in the union of bounded
;; complement components, i.e. inside(path_image g).

(defun-sk ht043-path-image-in-square-p
    (carrier gx gy zero one less negate bound)
  (forall (parameter)
    (implies
     (and
      (ht043-member-p carrier parameter)
      (ht043-in-unit-interval-p less zero one parameter))
     (and
      (ht043-leq-p
       less
       (ht043-abs
        less negate zero (ht043-unary gx parameter))
       bound)
      (ht043-leq-p
       less
       (ht043-abs
        less negate zero (ht043-unary gy parameter))
       bound)))))

(defun-sk ht043-connector-avoids-image-p
    (carrier gx gy hx hy zero one less)
  (forall (parameter)
    (implies
     (and
      (ht043-member-p carrier parameter)
      (ht043-in-unit-interval-p less zero one parameter))
     (not
      (ht043-path-hits-point-p
       carrier gx gy zero one less
       (ht043-unary hx parameter)
       (ht043-unary hy parameter))))))

(defun ht043-outside-connector-p
    (carrier gx gy hx hy x y bound
             add multiply negate square-root zero one less)
  (and
   (ht043-valid-unary-function-p carrier hx)
   (ht043-valid-unary-function-p carrier hy)
   (ht043-continuous-path-p
    carrier hx hy add multiply negate square-root zero one less)
   (equal (ht043-unary hx zero) x)
   (equal (ht043-unary hy zero) y)
   (or
    (ht043-less-p
     less bound
     (ht043-abs less negate zero (ht043-unary hx one)))
    (ht043-less-p
     less bound
     (ht043-abs less negate zero (ht043-unary hy one))))
   (ht043-connector-avoids-image-p
    carrier gx gy hx hy zero one less)))

(defun-sk ht043-outside-connector-exists-p
    (carrier gx gy x y bound
             add multiply negate square-root zero one less)
  (exists (hx hy)
    (ht043-outside-connector-p
     carrier gx gy hx hy x y bound
     add multiply negate square-root zero one less)))

(defun ht043-inside-at-bound-p
    (carrier gx gy x y bound
             add multiply negate square-root zero one less)
  (and
   (ht043-member-p carrier x)
   (ht043-member-p carrier y)
   (not
    (ht043-path-hits-point-p
     carrier gx gy zero one less x y))
   (not
    (ht043-outside-connector-exists-p
     carrier gx gy x y bound
     add multiply negate square-root zero one less))))

;; The enclosed area is planar outer area: the infimum of the costs of
;; countable rectangle covers of the bounded complement components. A
;; rectangle is (lower-x upper-x lower-y upper-y); reversed or degenerate
;; intervals have zero area, as in ENNReal.ofReal in the Lean statement.

(defun ht043-rectangle-p (carrier rectangle)
  (and
   (true-listp rectangle)
   (equal (len rectangle) 4)
   (ht043-member-p carrier (car rectangle))
   (ht043-member-p carrier (cadr rectangle))
   (ht043-member-p carrier (caddr rectangle))
   (ht043-member-p carrier (cadddr rectangle))))

(defun ht043-point-in-rectangle-p (less x y rectangle)
  (and
   (ht043-leq-p less (car rectangle) x)
   (ht043-leq-p less x (cadr rectangle))
   (ht043-leq-p less (caddr rectangle) y)
   (ht043-leq-p less y (cadddr rectangle))))

(defun ht043-rectangle-area
    (add multiply negate zero less rectangle)
  (let ((width
         (ht043-max
          less zero
          (ht043-sub add negate
                     (cadr rectangle) (car rectangle))))
        (height
         (ht043-max
          less zero
          (ht043-sub add negate
                     (cadddr rectangle) (caddr rectangle)))))
    (ht043-mul multiply width height)))

(defun-sk ht043-rectangle-sequence-values-p (carrier rectangles)
  (forall (index)
    (implies
     (natp index)
     (ht043-rectangle-p
      carrier (ht043-unary rectangles index)))))

(defun ht043-rectangle-sequence-p (carrier rectangles)
  (and
   (tamep-functionp rectangles)
   (ht043-rectangle-sequence-values-p carrier rectangles)))

(defun-sk ht043-point-covered-p (rectangles less x y)
  (exists (index)
    (and
     (natp index)
     (ht043-point-in-rectangle-p
      less x y (ht043-unary rectangles index)))))

(defun-sk ht043-rectangles-cover-inside-p
    (carrier gx gy bound add multiply negate square-root
             zero one less rectangles)
  (forall (x y)
    (implies
     (ht043-inside-at-bound-p
      carrier gx gy x y bound
      add multiply negate square-root zero one less)
     (ht043-point-covered-p rectangles less x y))))

(defun ht043-countable-inside-cover-p
    (carrier gx gy bound add multiply negate square-root
             zero one less rectangles)
  (and
   (ht043-rectangle-sequence-p carrier rectangles)
   (ht043-rectangles-cover-inside-p
    carrier gx gy bound add multiply negate square-root
    zero one less rectangles)))

(defun ht043-cover-area-prefix
    (rectangles add multiply negate zero less count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      zero
    (let ((index (1- count)))
      (ht043-add
       add
       (ht043-cover-area-prefix
        rectangles add multiply negate zero less index)
       (ht043-rectangle-area
        add multiply negate zero less
        (ht043-unary rectangles index))))))

;; This says threshold is at most the supremum of the nondecreasing partial
;; area sums. It also covers divergent series, whose cost is +infinity.
(defun-sk ht043-cover-prefix-witness-p
    (rectangles add multiply negate zero less threshold epsilon)
  (exists (count)
    (and
     (natp count)
     (ht043-less-p
      less
      (ht043-sub add negate threshold epsilon)
      (ht043-cover-area-prefix
       rectangles add multiply negate zero less count)))))

(defun-sk ht043-cover-series-at-least-p
    (carrier rectangles add multiply negate zero less threshold)
  (forall (epsilon)
    (implies
     (ht043-positive-p carrier less zero epsilon)
     (ht043-cover-prefix-witness-p
      rectangles add multiply negate zero less threshold epsilon))))

(defun-sk ht043-inside-area-lower-bound-p
    (carrier gx gy bound add multiply negate square-root
             zero one less candidate)
  (forall (rectangles)
    (implies
     (ht043-countable-inside-cover-p
      carrier gx gy bound add multiply negate square-root
      zero one less rectangles)
     (ht043-cover-series-at-least-p
      carrier rectangles add multiply negate zero less candidate))))

;; The lower cut determines the greatest lower bound of all countable-cover
;; costs without choosing a particular convergent series representation.
(defun-sk ht043-is-outer-area-at-bound-p
    (carrier gx gy bound add multiply negate square-root
             zero one less area)
  (forall (candidate)
    (implies
     (ht043-member-p carrier candidate)
     (iff
      (ht043-leq-p less candidate area)
      (ht043-inside-area-lower-bound-p
       carrier gx gy bound add multiply negate square-root
       zero one less candidate)))))

(defun-sk ht043-has-inside-area-p
    (carrier gx gy add multiply negate square-root zero one less area)
  (exists (bound)
    (and
     (ht043-member-p carrier area)
     (ht043-leq-p less zero area)
     (ht043-positive-p carrier less zero bound)
     (ht043-path-image-in-square-p
      carrier gx gy zero one less negate bound)
     (ht043-is-outer-area-at-bound-p
      carrier gx gy bound add multiply negate square-root
      zero one less area))))

;; Equality with sphere(a,r) is extensional equality of the path image and
;; the full Euclidean circle. The center and radius are internal witnesses.

(defun-sk ht043-path-image-is-circle-p
    (carrier gx gy center-x center-y radius
             add multiply negate zero one less)
  (forall (x y)
    (implies
     (and
      (ht043-member-p carrier x)
      (ht043-member-p carrier y))
     (iff
      (ht043-path-hits-point-p
       carrier gx gy zero one less x y)
      (equal
       (ht043-add
        add
        (ht043-square
         multiply (ht043-sub add negate x center-x))
        (ht043-square
         multiply (ht043-sub add negate y center-y)))
       (ht043-square multiply radius))))))

(defun-sk ht043-circle-witness-exists-p
    (carrier gx gy add multiply negate zero one less)
  (exists (center-x center-y radius)
    (and
     (ht043-member-p carrier center-x)
     (ht043-member-p carrier center-y)
     (ht043-member-p carrier radius)
     (ht043-leq-p less zero radius)
     (ht043-path-image-is-circle-p
      carrier gx gy center-x center-y radius
      add multiply negate zero one less))))

(defun-sk ht043-isoperimetric-conclusion-p
    (carrier gx gy length pi-value
             add multiply negate inverse square-root zero one less)
  (exists (area)
    (let* ((four (ht043-four add zero one))
           (denominator (ht043-mul multiply four pi-value))
           (bound
            (ht043-div
             multiply inverse
             (ht043-square multiply length)
             denominator)))
      (and
       (ht043-member-p carrier area)
       (ht043-has-inside-area-p
        carrier gx gy add multiply negate square-root
        zero one less area)
       (ht043-leq-p less area bound)
       (implies
        (equal area bound)
        (ht043-circle-witness-exists-p
         carrier gx gy add multiply negate zero one less))))))

(defun hundred-theorems-043-isoperimetric-theorem-statement
    (carrier add multiply negate inverse square-root zero one less
             gx gy pi-value length)
  (implies
   (and
    (ht043-real-field-p
     carrier add multiply negate inverse zero one less)
    (ht043-square-root-p
     carrier multiply zero less square-root)
    (ht043-pi-p
     carrier add multiply negate inverse zero one less pi-value)
    (ht043-valid-unary-function-p carrier gx)
    (ht043-valid-unary-function-p carrier gy)
    (ht043-continuous-path-p
     carrier gx gy add multiply negate square-root zero one less)
    (ht043-simple-path-p carrier gx gy zero one less)
    (ht043-closed-path-p gx gy zero one)
    (ht043-has-path-length-p
     carrier gx gy add multiply negate square-root
     zero one less length))
   (ht043-isoperimetric-conclusion-p
    carrier gx gy length pi-value
    add multiply negate inverse square-root zero one less)))

(value-triple :itpeval-statement-checked)
:q
