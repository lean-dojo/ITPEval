;; Statement-only formalization of Hundred Theorems item 036,
;; "Brouwer Fixed Point Theorem": every continuous self-map of a nonempty
;; compact convex subset of a finite-dimensional real normed space has a
;; fixed point. This file contains no proof.
;;
;; Semantic status: the direct DEFUN-SK formulation below repairs the former
;; vacuous APPLY$ quantifiers, but standard ACL2 still ranges only over tame
;; coded scalar sets, vector sets, sequences, and maps. It therefore does not
;; preserve the source's unrestricted real-space quantification and is not
;; counted as a faithful translation.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Function-valued objects are represented by tame APPLY$ objects. Every
;; mathematical quantifier below is a direct DEFUN-SK quantifier; no generated
;; lambda calls a user-defined ACL2 function.

(defun ht036-member-p (predicate object)
  (if (apply$ predicate (list object)) t nil))

(defun ht036-unary-value (function argument)
  (apply$ function (list argument)))

(defun ht036-binary-value (function left right)
  (apply$ function (list left right)))

;; A scalar context contains a carrier predicate, zero, one, addition,
;; multiplication, negation, inversion, and strict order.

(defun ht036-r-carrier (ctx) (nth 0 ctx))
(defun ht036-r-zero (ctx) (nth 1 ctx))
(defun ht036-r-one (ctx) (nth 2 ctx))
(defun ht036-r-add (ctx) (nth 3 ctx))
(defun ht036-r-multiply (ctx) (nth 4 ctx))
(defun ht036-r-negate (ctx) (nth 5 ctx))
(defun ht036-r-inverse (ctx) (nth 6 ctx))
(defun ht036-r-less (ctx) (nth 7 ctx))

(defun ht036-real-p (ctx value)
  (ht036-member-p (ht036-r-carrier ctx) value))

(defun ht036-zero (ctx)
  (ht036-r-zero ctx))

(defun ht036-one (ctx)
  (ht036-r-one ctx))

(defun ht036-add (ctx left right)
  (ht036-binary-value
   (ht036-r-add ctx) left right))

(defun ht036-multiply (ctx left right)
  (ht036-binary-value
   (ht036-r-multiply ctx) left right))

(defun ht036-negate (ctx value)
  (ht036-unary-value
   (ht036-r-negate ctx) value))

(defun ht036-inverse (ctx value)
  (ht036-unary-value
   (ht036-r-inverse ctx) value))

(defun ht036-less (ctx left right)
  (if
      (ht036-binary-value
       (ht036-r-less ctx) left right)
      t nil))

(defun ht036-subtract (ctx left right)
  (ht036-add ctx left (ht036-negate ctx right)))

(defun ht036-less-equal-p (ctx left right)
  (not (ht036-less ctx right left)))

(defun ht036-absolute-value (ctx value)
  (if (ht036-less ctx value (ht036-zero ctx))
      (ht036-negate ctx value)
    value))

(defun ht036-positive-real-p (ctx value)
  (and
   (ht036-real-p ctx value)
   (ht036-less ctx (ht036-zero ctx) value)))

(defun-sk ht036-field-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (ht036-real-p ctx a)
      (ht036-real-p ctx b)
      (ht036-real-p ctx c))
     (let* ((ab-add (ht036-add ctx a b))
            (bc-add (ht036-add ctx b c))
            (ab-mul (ht036-multiply ctx a b))
            (bc-mul (ht036-multiply ctx b c))
            (neg-a (ht036-negate ctx a))
            (inv-a (ht036-inverse ctx a))
            (zero (ht036-zero ctx))
            (one (ht036-one ctx)))
       (and
        (ht036-real-p ctx ab-add)
        (ht036-real-p ctx ab-mul)
        (ht036-real-p ctx neg-a)
        (ht036-real-p ctx inv-a)
        (equal
         (ht036-add ctx ab-add c)
         (ht036-add ctx a bc-add))
        (equal ab-add (ht036-add ctx b a))
        (equal (ht036-add ctx a zero) a)
        (equal (ht036-add ctx a neg-a) zero)
        (equal
         (ht036-multiply ctx ab-mul c)
         (ht036-multiply ctx a bc-mul))
        (equal ab-mul (ht036-multiply ctx b a))
        (equal (ht036-multiply ctx a one) a)
        (implies
         (equal a zero)
         (equal inv-a zero))
        (implies
         (not (equal a zero))
         (equal (ht036-multiply ctx a inv-a) one))
        (equal
         (ht036-multiply ctx a bc-add)
         (ht036-add
          ctx
          (ht036-multiply ctx a b)
          (ht036-multiply ctx a c))))))))

(defun-sk ht036-order-laws-p (ctx)
  (forall (a b c)
    (implies
     (and
      (ht036-real-p ctx a)
      (ht036-real-p ctx b)
      (ht036-real-p ctx c))
     (and
      (not (ht036-less ctx a a))
      (or
       (ht036-less ctx a b)
       (equal a b)
       (ht036-less ctx b a))
      (implies
       (and
        (ht036-less ctx a b)
        (ht036-less ctx b c))
       (ht036-less ctx a c))
      (implies
       (ht036-less ctx a b)
       (ht036-less
        ctx
        (ht036-add ctx a c)
        (ht036-add ctx b c)))
      (implies
       (and
        (ht036-less ctx (ht036-zero ctx) a)
        (ht036-less ctx (ht036-zero ctx) b))
       (ht036-less
        ctx
        (ht036-zero ctx)
        (ht036-multiply ctx a b)))))))

;; Dedekind completeness pins the scalar field down to a presentation of the
;; real numbers under the corpus's tame-function convention.

(defun ht036-scalar-set-member-p (ctx set value)
  (declare (ignore ctx))
  (ht036-member-p set value))

(defun-sk ht036-valid-scalar-set-p (ctx set)
  (forall (value)
    (implies
     (ht036-scalar-set-member-p ctx set value)
     (ht036-real-p ctx value))))

(defun ht036-extensional-scalar-set-p (ctx set)
  (and
   (tamep-functionp set)
   (ht036-valid-scalar-set-p ctx set)))

(defun-sk ht036-scalar-set-nonempty-p (ctx set)
  (exists (value)
    (and
     (ht036-real-p ctx value)
     (ht036-scalar-set-member-p ctx set value))))

(defun-sk ht036-upper-bound-p (ctx set upper)
  (forall (value)
    (implies
     (and
      (ht036-real-p ctx value)
      (ht036-scalar-set-member-p ctx set value))
     (not (ht036-less ctx upper value)))))

(defun-sk ht036-bounded-above-p (ctx set)
  (exists (upper)
    (and
     (ht036-real-p ctx upper)
     (ht036-upper-bound-p ctx set upper))))

(defun-sk ht036-least-upper-bound-p
    (ctx set supremum)
  (forall (upper)
    (implies
     (and
      (ht036-real-p ctx upper)
      (ht036-upper-bound-p ctx set upper))
     (not (ht036-less ctx upper supremum)))))

(defun ht036-is-supremum-p (ctx set supremum)
  (and
   (ht036-real-p ctx supremum)
   (ht036-upper-bound-p ctx set supremum)
   (ht036-least-upper-bound-p ctx set supremum)))

(defun-sk ht036-has-supremum-p (ctx set)
  (exists (supremum)
    (ht036-is-supremum-p ctx set supremum)))

(defun-sk ht036-completeness-p (ctx)
  (forall (set)
    (implies
     (and
      (ht036-extensional-scalar-set-p ctx set)
      (ht036-scalar-set-nonempty-p ctx set)
      (ht036-bounded-above-p ctx set))
     (ht036-has-supremum-p ctx set))))

(defun ht036-real-field-p (ctx)
  (and
   (true-listp ctx)
   (equal (len ctx) 8)
   (tamep-functionp (ht036-r-carrier ctx))
   (tamep-functionp (ht036-r-add ctx))
   (tamep-functionp (ht036-r-multiply ctx))
   (tamep-functionp (ht036-r-negate ctx))
   (tamep-functionp (ht036-r-inverse ctx))
   (tamep-functionp (ht036-r-less ctx))
   (ht036-real-p ctx (ht036-zero ctx))
   (ht036-real-p ctx (ht036-one ctx))
   (not (equal (ht036-zero ctx) (ht036-one ctx)))
   (ht036-field-laws-p ctx)
   (ht036-order-laws-p ctx)
   (ht036-completeness-p ctx)
   (ht036-less ctx (ht036-zero ctx) (ht036-one ctx))))

;; A vector-space context contains a carrier predicate, zero, addition,
;; negation, scalar multiplication, and norm.

(defun ht036-v-carrier (space) (nth 0 space))
(defun ht036-v-zero (space) (nth 1 space))
(defun ht036-v-add (space) (nth 2 space))
(defun ht036-v-negate (space) (nth 3 space))
(defun ht036-v-smul (space) (nth 4 space))
(defun ht036-v-norm (space) (nth 5 space))

(defun ht036-vector-p (space value)
  (ht036-member-p (ht036-v-carrier space) value))

(defun ht036-vector-zero (space)
  (ht036-v-zero space))

(defun ht036-vector-add (space left right)
  (ht036-binary-value
   (ht036-v-add space) left right))

(defun ht036-vector-negate (space value)
  (ht036-unary-value
   (ht036-v-negate space) value))

(defun ht036-scalar-multiply (space scalar vector)
  (ht036-binary-value
   (ht036-v-smul space) scalar vector))

(defun ht036-norm (space vector)
  (ht036-unary-value
   (ht036-v-norm space) vector))

(defun ht036-distance (real space left right)
  (declare (ignore real))
  (ht036-norm
   space
   (ht036-vector-add
    space left (ht036-vector-negate space right))))

(defun-sk ht036-vector-laws-p (real space)
  (forall (a b x y z)
    (implies
     (and
      (ht036-real-p real a)
      (ht036-real-p real b)
      (ht036-vector-p space x)
      (ht036-vector-p space y)
      (ht036-vector-p space z))
     (let* ((xy (ht036-vector-add space x y))
            (yz (ht036-vector-add space y z))
            (neg-x (ht036-vector-negate space x))
            (ax (ht036-scalar-multiply space a x))
            (bx (ht036-scalar-multiply space b x))
            (ay (ht036-scalar-multiply space a y))
            (zero (ht036-vector-zero space)))
       (and
        (ht036-vector-p space xy)
        (ht036-vector-p space neg-x)
        (ht036-vector-p space ax)
        (equal
         (ht036-vector-add space xy z)
         (ht036-vector-add space x yz))
        (equal xy (ht036-vector-add space y x))
        (equal (ht036-vector-add space x zero) x)
        (equal (ht036-vector-add space x neg-x) zero)
        (equal
         (ht036-scalar-multiply space (ht036-one real) x)
         x)
        (equal
         (ht036-scalar-multiply
          space (ht036-add real a b) x)
         (ht036-vector-add space ax bx))
        (equal
         (ht036-scalar-multiply space a xy)
         (ht036-vector-add space ax ay))
        (equal
         (ht036-scalar-multiply
          space (ht036-multiply real a b) x)
         (ht036-scalar-multiply space a bx)))))))

(defun-sk ht036-norm-laws-p (real space)
  (forall (a x y)
    (implies
     (and
      (ht036-real-p real a)
      (ht036-vector-p space x)
      (ht036-vector-p space y))
     (let* ((norm-x (ht036-norm space x))
            (norm-y (ht036-norm space y))
            (norm-sum
             (ht036-norm
              space (ht036-vector-add space x y)))
            (norm-scale
             (ht036-norm
              space
              (ht036-scalar-multiply space a x))))
       (and
        (ht036-real-p real norm-x)
        (ht036-real-p real norm-y)
        (ht036-real-p real norm-sum)
        (ht036-real-p real norm-scale)
        (ht036-less-equal-p
         real (ht036-zero real) norm-x)
        (iff
         (equal norm-x (ht036-zero real))
         (equal x (ht036-vector-zero space)))
        (ht036-less-equal-p
         real
         norm-sum
         (ht036-add real norm-x norm-y))
        (equal
         norm-scale
         (ht036-multiply
          real
          (ht036-absolute-value real a)
          norm-x)))))))

(defun ht036-normed-vector-space-p (real space)
  (and
   (true-listp space)
   (equal (len space) 6)
   (tamep-functionp (ht036-v-carrier space))
   (tamep-functionp (ht036-v-add space))
   (tamep-functionp (ht036-v-negate space))
   (tamep-functionp (ht036-v-smul space))
   (tamep-functionp (ht036-v-norm space))
   (ht036-vector-p space (ht036-vector-zero space))
   (ht036-vector-laws-p real space)
   (ht036-norm-laws-p real space)))

;; A finite basis and its coordinate map witness finite dimensionality.

(defun ht036-basis-value (basis index)
  (ht036-unary-value basis index))

(defun ht036-coordinate-value
    (coordinates vector index)
  (ht036-binary-value coordinates vector index))

(defun ht036-linear-combination
    (space basis coordinates vector count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht036-vector-zero space)
    (let* ((index (- count 1))
           (coefficient
            (ht036-coordinate-value
             coordinates vector index))
           (term
            (ht036-scalar-multiply
             space coefficient
             (ht036-basis-value basis index))))
      (ht036-vector-add
       space
       (ht036-linear-combination
        space basis coordinates vector index)
       term))))

(defun-sk ht036-basis-values-p
    (space basis dimension)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index dimension))
     (ht036-vector-p
      space (ht036-basis-value basis index)))))

(defun-sk ht036-coordinate-values-p
    (real space coordinates dimension)
  (forall (vector index)
    (implies
     (and
      (ht036-vector-p space vector)
      (natp index)
      (< index dimension))
     (ht036-real-p
      real
      (ht036-coordinate-value
       coordinates vector index)))))

(defun-sk ht036-coordinate-basis-law-p
    (real space basis coordinates dimension)
  (forall (row column)
    (implies
     (and
      (natp row)
      (< row dimension)
      (natp column)
      (< column dimension))
     (equal
      (ht036-coordinate-value
       coordinates
       (ht036-basis-value basis row)
       column)
      (if (equal row column)
          (ht036-one real)
        (ht036-zero real))))))

(defun-sk ht036-coordinate-reconstruction-p
    (real space basis coordinates dimension)
  (forall (vector)
    (implies
     (ht036-vector-p space vector)
     (equal
      (ht036-linear-combination
       space basis coordinates vector dimension)
      vector))))

(defun ht036-finite-coordinate-system-p
    (real space dimension basis coordinates)
  (and
   (natp dimension)
   (< 0 dimension)
   (tamep-functionp basis)
   (tamep-functionp coordinates)
   (ht036-basis-values-p space basis dimension)
   (ht036-coordinate-values-p
    real space coordinates dimension)
   (ht036-coordinate-basis-law-p
    real space basis coordinates dimension)
   (ht036-coordinate-reconstruction-p
    real space basis coordinates dimension)))

;; Extensional subsets and maps of the vector space.

(defun ht036-set-member-p (set vector)
  (ht036-member-p set vector))

(defun ht036-function-value (function vector)
  (ht036-unary-value function vector))

(defun-sk ht036-valid-vector-set-p (space set)
  (forall (vector)
    (implies
     (ht036-set-member-p set vector)
     (ht036-vector-p space vector))))

(defun ht036-extensional-vector-set-p (space set)
  (and
   (tamep-functionp set)
   (ht036-valid-vector-set-p space set)))

(defun-sk ht036-set-nonempty-p (space set)
  (exists (vector)
    (and
     (ht036-vector-p space vector)
     (ht036-set-member-p set vector))))

(defun-sk ht036-endomap-p (space function)
  (forall (vector)
    (implies
     (ht036-vector-p space vector)
     (ht036-vector-p
      space (ht036-function-value function vector)))))

(defun ht036-extensional-endomap-p (space function)
  (and
   (tamep-functionp function)
   (ht036-endomap-p space function)))

;; Sequential compactness in the norm metric. In finite-dimensional real
;; normed spaces this is equivalent to the source provers' compactness.

(defun ht036-sequence-value (sequence index)
  (ht036-unary-value sequence index))

(defun ht036-subsequence-index
    (subsequence index)
  (ht036-unary-value subsequence index))

(defun-sk ht036-sequence-in-set-p
    (space set sequence)
  (forall (index)
    (implies
     (natp index)
     (let ((value
            (ht036-sequence-value sequence index)))
       (and
        (ht036-vector-p space value)
        (ht036-set-member-p set value))))))

(defun-sk ht036-subsequence-natural-p (subsequence)
  (forall (index)
    (implies
     (natp index)
     (natp
      (ht036-subsequence-index
       subsequence index)))))

(defun-sk ht036-subsequence-increasing-p (subsequence)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (< left right))
     (<
      (ht036-subsequence-index subsequence left)
      (ht036-subsequence-index subsequence right)))))

(defun ht036-strict-subsequence-p (subsequence)
  (and
   (tamep-functionp subsequence)
   (ht036-subsequence-natural-p subsequence)
   (ht036-subsequence-increasing-p subsequence)))

(defun-sk ht036-convergence-tail-p
    (real space sequence subsequence limit epsilon start)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= start index))
     (ht036-less
      real
      (ht036-distance
       real
       space
       (ht036-sequence-value
        sequence
        (ht036-subsequence-index
         subsequence index))
       limit)
      epsilon))))

(defun-sk ht036-convergence-start-exists-p
    (real space sequence subsequence limit epsilon)
  (exists (start)
    (and
     (natp start)
     (ht036-convergence-tail-p
      real space sequence subsequence
      limit epsilon start))))

(defun-sk ht036-converges-to-p
    (real space sequence subsequence limit)
  (forall (epsilon)
    (implies
     (ht036-positive-real-p real epsilon)
     (ht036-convergence-start-exists-p
      real space sequence subsequence
      limit epsilon))))

(defun ht036-compact-witness-p
    (real space set sequence subsequence limit)
  (and
   (ht036-strict-subsequence-p subsequence)
   (ht036-vector-p space limit)
   (ht036-set-member-p set limit)
   (ht036-converges-to-p
    real space sequence subsequence limit)))

(defun-sk ht036-compact-witness-exists-p
    (real space set sequence)
  (exists (subsequence limit)
    (ht036-compact-witness-p
     real space set sequence subsequence limit)))

(defun-sk ht036-compact-set-quantifier-p
    (real space set)
  (forall (sequence)
    (implies
     (and
      (tamep-functionp sequence)
      (ht036-sequence-in-set-p
       space set sequence))
     (ht036-compact-witness-exists-p
      real space set sequence))))

(defun ht036-compact-set-p (real space set)
  (and
   (ht036-extensional-vector-set-p space set)
   (ht036-compact-set-quantifier-p
    real space set)))

;; Convexity uses the standard affine combination (1-t)x + ty.

(defun ht036-convex-combination
    (real space parameter left right)
  (ht036-vector-add
   space
   (ht036-scalar-multiply
    space
    (ht036-subtract
     real (ht036-one real) parameter)
    left)
   (ht036-scalar-multiply
    space parameter right)))

(defun-sk ht036-convex-set-quantifier-p
    (real space set)
  (forall (left right parameter)
    (implies
     (and
      (ht036-vector-p space left)
      (ht036-vector-p space right)
      (ht036-set-member-p set left)
      (ht036-set-member-p set right)
      (ht036-real-p real parameter)
      (ht036-less-equal-p
       real (ht036-zero real) parameter)
      (ht036-less-equal-p
       real parameter (ht036-one real)))
     (ht036-set-member-p
      set
      (ht036-convex-combination
       real space parameter left right)))))

(defun ht036-convex-set-p (real space set)
  (and
   (ht036-extensional-vector-set-p space set)
   (ht036-convex-set-quantifier-p
    real space set)))

;; Epsilon-delta continuity relative to the subset.

(defun-sk ht036-continuity-nearby-p
    (real space set function point epsilon delta)
  (forall (nearby)
    (implies
     (and
      (ht036-vector-p space nearby)
      (ht036-set-member-p set nearby)
      (ht036-less
       real
       (ht036-distance
        real space nearby point)
       delta))
     (ht036-less
      real
      (ht036-distance
       real
       space
       (ht036-function-value function nearby)
       (ht036-function-value function point))
      epsilon))))

(defun-sk ht036-continuity-delta-exists-p
    (real space set function point epsilon)
  (exists (delta)
    (and
     (ht036-positive-real-p real delta)
     (ht036-continuity-nearby-p
      real space set function point
      epsilon delta))))

(defun-sk ht036-continuous-within-at-p
    (real space set function point)
  (forall (epsilon)
    (implies
     (ht036-positive-real-p real epsilon)
     (ht036-continuity-delta-exists-p
      real space set function point epsilon))))

(defun-sk ht036-continuous-on-quantifier-p
    (real space set function)
  (forall (point)
    (implies
     (and
      (ht036-vector-p space point)
      (ht036-set-member-p set point))
     (ht036-continuous-within-at-p
      real space set function point))))

(defun ht036-continuous-on-p
    (real space set function)
  (and
   (ht036-extensional-vector-set-p space set)
   (ht036-extensional-endomap-p space function)
   (ht036-continuous-on-quantifier-p
    real space set function)))

(defun-sk ht036-self-map-p (space set function)
  (forall (point)
    (implies
     (and
      (ht036-vector-p space point)
      (ht036-set-member-p set point))
     (ht036-set-member-p
      set (ht036-function-value function point)))))

(defun-sk ht036-fixed-point-exists-p
    (space set function)
  (exists (point)
    (and
     (ht036-vector-p space point)
     (ht036-set-member-p set point)
     (equal
      (ht036-function-value function point)
      point))))

(defun-sk
    hundred-theorems-036-brouwer-fixed-point-theorem-statement ()
  (forall (real space dimension basis coordinates set function)
    (implies
     (and
      (ht036-real-field-p real)
      (ht036-normed-vector-space-p real space)
      (ht036-finite-coordinate-system-p
       real space dimension basis coordinates)
      (ht036-extensional-vector-set-p space set)
      (ht036-extensional-endomap-p space function)
      (ht036-compact-set-p real space set)
      (ht036-convex-set-p real space set)
      (ht036-set-nonempty-p space set)
      (ht036-continuous-on-p
       real space set function)
      (ht036-self-map-p space set function))
     (ht036-fixed-point-exists-p
      space set function))))

(value-triple :itpeval-statement-checked)
:q
