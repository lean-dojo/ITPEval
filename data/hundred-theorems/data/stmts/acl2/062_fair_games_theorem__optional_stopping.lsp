;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__062, "Fair Games Theorem (Optional Stopping)".
;;
;; The five indexed statements below cover the bounded-stopping-time
;; characterization of submartingales and the standard optional-stopping
;; conclusions under the three hypotheses used by the Rocq source.
;; This file contains no proof.
;;
;; Semantic status: the first-order rewrite below repairs the former vacuous
;; APPLY$ quantifiers, but its stub-coded events, random variables, filtrations,
;; and expectations do not range over the unrestricted probability objects in
;; the source. Standard ACL2 therefore cannot count this as a faithful
;; translation.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The mathematical structures are ordinary first-order codes.  These
;; unconstrained operations provide their generic signature; every required
;; law is stated explicitly in the hypotheses below.  In particular, no
;; generated lambda or APPLY$ warrant is used to encode a quantifier.

;; Scalar field.

(defstub ht062-scalar-p (field value) t)
(defstub ht062-zero (field) t)
(defstub ht062-one (field) t)
(defstub ht062-add (field left right) t)
(defstub ht062-multiply (field left right) t)
(defstub ht062-negate (field value) t)
(defstub ht062-inverse (field value) t)
(defstub ht062-less (field left right) t)
(defstub ht062-real-set-p (field set) t)
(defstub ht062-real-set-member-p (field set value) t)
(defstub ht062-supremum (field set) t)

;; Sample spaces, events, sigma-algebras, and measures.

(defstub ht062-sample-p (space omega) t)
(defstub ht062-event-p (space event) t)
(defstub ht062-event-member-p (space event omega) t)
(defstub ht062-empty-event (space) t)
(defstub ht062-full-event (space) t)
(defstub ht062-complement-event (space event) t)
(defstub ht062-intersection-event (space left right) t)
(defstub ht062-sequence-event (space sequence index) t)
(defstub ht062-countable-union-event (space sequence) t)
(defstub ht062-sigma-event-p (space sigma event) t)
(defstub ht062-measure-value (field space measure event) t)
(defstub ht062-filtration-sigma (space filtration index) t)

;; Random-variable and process codes.

(defstub ht062-variable-p (field space variable) t)
(defstub ht062-variable-value (field space variable omega) t)
(defstub ht062-sublevel-event
  (field space variable threshold) t)
(defstub ht062-level-event
  (field space variable positivep threshold) t)
(defstub ht062-process-p (field space process) t)
(defstub ht062-process-value
  (field space process index omega) t)
(defstub ht062-process-fiber
  (field space process index) t)
(defstub ht062-restricted-variable
  (field space variable event) t)

;; Extended-natural stopping-time codes and their canonical constructions.

(defstub ht062-stopping-code-p (space stopping-time) t)
(defstub ht062-stopping-finite-p
  (space stopping-time omega) t)
(defstub ht062-stopping-index
  (space stopping-time omega) t)
(defstub ht062-stopping-le-event
  (space stopping-time bound) t)
(defstub ht062-stopped-variable
  (field space process stopping-time) t)
(defstub ht062-stopping-value-variable
  (field space stopping-time) t)
(defstub ht062-stopped-process
  (field space process stopping-time) t)

;; Ordered-field operations.

(defun ht062-leq-p (field left right)
  (not (ht062-less field right left)))

(defun ht062-subtract (field left right)
  (ht062-add field left (ht062-negate field right)))

(defun ht062-divide (field numerator denominator)
  (ht062-multiply
   field numerator (ht062-inverse field denominator)))

(defun ht062-absolute-value (field value)
  (if (ht062-less field value (ht062-zero field))
      (ht062-negate field value)
    value))

(defun ht062-maximum (field left right)
  (if (ht062-less field left right) right left))

(defun ht062-real-nat (field index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (ht062-zero field)
    (ht062-add
     field
     (ht062-one field)
     (ht062-real-nat field (1- index)))))

(defun-sk ht062-field-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (ht062-scalar-p field x)
      (ht062-scalar-p field y)
      (ht062-scalar-p field z))
     (and
      (ht062-scalar-p field (ht062-add field x y))
      (ht062-scalar-p field (ht062-multiply field x y))
      (ht062-scalar-p field (ht062-negate field x))
      (ht062-scalar-p field (ht062-inverse field x))
      (equal
       (ht062-add field (ht062-add field x y) z)
       (ht062-add field x (ht062-add field y z)))
      (equal (ht062-add field x y) (ht062-add field y x))
      (equal (ht062-add field x (ht062-zero field)) x)
      (equal
       (ht062-add field x (ht062-negate field x))
       (ht062-zero field))
      (equal
       (ht062-multiply field (ht062-multiply field x y) z)
       (ht062-multiply field x (ht062-multiply field y z)))
      (equal
       (ht062-multiply field x y)
       (ht062-multiply field y x))
      (equal
       (ht062-multiply field x (ht062-one field))
       x)
      (implies
       (equal x (ht062-zero field))
       (equal
        (ht062-inverse field x)
        (ht062-zero field)))
      (implies
       (not (equal x (ht062-zero field)))
       (equal
        (ht062-multiply field x (ht062-inverse field x))
        (ht062-one field)))
      (equal
       (ht062-multiply field x (ht062-add field y z))
       (ht062-add
        field
        (ht062-multiply field x y)
        (ht062-multiply field x z)))))))

(defun-sk ht062-order-laws-p (field)
  (forall (x y z)
    (implies
     (and
      (ht062-scalar-p field x)
      (ht062-scalar-p field y)
      (ht062-scalar-p field z))
     (and
      (not (ht062-less field x x))
      (or
       (equal x y)
       (ht062-less field x y)
       (ht062-less field y x))
      (implies
       (and
        (ht062-less field x y)
        (ht062-less field y z))
       (ht062-less field x z))
      (implies
       (ht062-less field x y)
       (ht062-less
        field
        (ht062-add field x z)
        (ht062-add field y z)))
      (implies
       (and
        (ht062-less field (ht062-zero field) x)
        (ht062-less field (ht062-zero field) y))
       (ht062-less
        field
        (ht062-zero field)
        (ht062-multiply field x y)))))))

(defun-sk ht062-real-set-nonempty-p (field set)
  (exists (value)
    (and
     (ht062-scalar-p field value)
     (ht062-real-set-member-p field set value))))

(defun-sk ht062-real-set-upper-bound-p (field set bound)
  (forall (value)
    (implies
     (and
      (ht062-scalar-p field value)
      (ht062-real-set-member-p field set value))
     (ht062-leq-p field value bound))))

(defun-sk ht062-real-set-bounded-above-p (field set)
  (exists (bound)
    (and
     (ht062-scalar-p field bound)
     (ht062-real-set-upper-bound-p field set bound))))

(defun-sk ht062-supremum-least-p (field set)
  (forall (bound)
    (implies
     (and
      (ht062-scalar-p field bound)
      (ht062-real-set-upper-bound-p field set bound))
     (ht062-leq-p
      field (ht062-supremum field set) bound))))

(defun-sk ht062-completeness-p (field)
  (forall (set)
    (implies
     (and
      (ht062-real-set-p field set)
      (ht062-real-set-nonempty-p field set)
      (ht062-real-set-bounded-above-p field set))
     (and
      (ht062-scalar-p field (ht062-supremum field set))
      (ht062-real-set-upper-bound-p
       field set (ht062-supremum field set))
      (ht062-supremum-least-p field set)))))

(defun-sk ht062-archimedean-witness-p (field value)
  (exists (index)
    (and
     (natp index)
     (ht062-less
      field value (ht062-real-nat field index)))))

(defun-sk ht062-archimedean-p (field)
  (forall (value)
    (implies
     (ht062-scalar-p field value)
     (ht062-archimedean-witness-p field value))))

(defun ht062-real-field-p (field)
  (and
   (ht062-scalar-p field (ht062-zero field))
   (ht062-scalar-p field (ht062-one field))
   (not (equal (ht062-zero field) (ht062-one field)))
   (ht062-less field (ht062-zero field) (ht062-one field))
   (ht062-field-laws-p field)
   (ht062-order-laws-p field)
   (ht062-completeness-p field)
   (ht062-archimedean-p field)))

;; Event and sigma-algebra structure.

(defun-sk ht062-events-extensionally-equal-p
    (space left right)
  (forall (omega)
    (implies
     (ht062-sample-p space omega)
     (iff
      (ht062-event-member-p space left omega)
      (ht062-event-member-p space right omega)))))

(defun-sk ht062-events-contained-p (space)
  (forall (event omega)
    (implies
     (and
      (ht062-event-p space event)
      (ht062-event-member-p space event omega))
     (ht062-sample-p space omega))))

(defun-sk ht062-empty-full-laws-p (space)
  (forall (omega)
    (implies
     (ht062-sample-p space omega)
     (and
      (not
       (ht062-event-member-p
        space (ht062-empty-event space) omega))
      (ht062-event-member-p
       space (ht062-full-event space) omega)))))

(defun-sk ht062-complement-laws-p (space)
  (forall (event omega)
    (implies
     (and
      (ht062-event-p space event)
      (ht062-sample-p space omega))
     (and
      (ht062-event-p
       space (ht062-complement-event space event))
      (iff
       (ht062-event-member-p
        space (ht062-complement-event space event) omega)
       (not
        (ht062-event-member-p space event omega)))))))

(defun-sk ht062-intersection-laws-p (space)
  (forall (left right omega)
    (implies
     (and
      (ht062-event-p space left)
      (ht062-event-p space right)
      (ht062-sample-p space omega))
     (and
      (ht062-event-p
       space (ht062-intersection-event space left right))
      (iff
       (ht062-event-member-p
        space
        (ht062-intersection-event space left right)
        omega)
       (and
        (ht062-event-member-p space left omega)
        (ht062-event-member-p space right omega)))))))

(defun-sk ht062-event-sequence-p (space sequence)
  (forall (index)
    (implies
     (natp index)
     (ht062-event-p
      space (ht062-sequence-event space sequence index)))))

(defun-sk ht062-point-in-sequence-p
    (space sequence omega)
  (exists (index)
    (and
     (natp index)
     (ht062-event-member-p
      space
      (ht062-sequence-event space sequence index)
      omega))))

(defun-sk ht062-countable-union-laws-p (space)
  (forall (sequence omega)
    (implies
     (and
      (ht062-event-sequence-p space sequence)
      (ht062-sample-p space omega))
     (and
      (ht062-event-p
       space (ht062-countable-union-event space sequence))
      (iff
       (ht062-event-member-p
        space
        (ht062-countable-union-event space sequence)
        omega)
       (ht062-point-in-sequence-p
        space sequence omega))))))

(defun ht062-event-structure-p (space)
  (and
   (ht062-event-p space (ht062-empty-event space))
   (ht062-event-p space (ht062-full-event space))
   (ht062-events-contained-p space)
   (ht062-empty-full-laws-p space)
   (ht062-complement-laws-p space)
   (ht062-intersection-laws-p space)
   (ht062-countable-union-laws-p space)))

(defun-sk ht062-sigma-events-are-events-p (space sigma)
  (forall (event)
    (implies
     (ht062-sigma-event-p space sigma event)
     (ht062-event-p space event))))

(defun-sk ht062-sigma-extensional-p (space sigma)
  (forall (left right)
    (implies
     (and
      (ht062-event-p space left)
      (ht062-event-p space right)
      (ht062-events-extensionally-equal-p space left right)
      (ht062-sigma-event-p space sigma left))
     (ht062-sigma-event-p space sigma right))))

(defun-sk ht062-sigma-complement-closed-p (space sigma)
  (forall (event)
    (implies
     (ht062-sigma-event-p space sigma event)
     (ht062-sigma-event-p
      space sigma (ht062-complement-event space event)))))

(defun-sk ht062-sigma-intersection-closed-p (space sigma)
  (forall (left right)
    (implies
     (and
      (ht062-sigma-event-p space sigma left)
      (ht062-sigma-event-p space sigma right))
     (ht062-sigma-event-p
      space
      sigma
      (ht062-intersection-event space left right)))))

(defun-sk ht062-sigma-event-sequence-p
    (space sigma sequence)
  (forall (index)
    (implies
     (natp index)
     (ht062-sigma-event-p
      space
      sigma
      (ht062-sequence-event space sequence index)))))

(defun-sk ht062-sigma-countable-union-closed-p
    (space sigma)
  (forall (sequence)
    (implies
     (ht062-sigma-event-sequence-p space sigma sequence)
     (ht062-sigma-event-p
      space
      sigma
      (ht062-countable-union-event space sequence)))))

(defun ht062-sigma-algebra-p (space sigma)
  (and
   (ht062-sigma-events-are-events-p space sigma)
   (ht062-sigma-event-p
    space sigma (ht062-empty-event space))
   (ht062-sigma-event-p
    space sigma (ht062-full-event space))
   (ht062-sigma-extensional-p space sigma)
   (ht062-sigma-complement-closed-p space sigma)
   (ht062-sigma-intersection-closed-p space sigma)
   (ht062-sigma-countable-union-closed-p space sigma)))

(defun-sk ht062-sub-sigma-algebra-p
    (space smaller larger)
  (forall (event)
    (implies
     (ht062-sigma-event-p space smaller event)
     (ht062-sigma-event-p space larger event))))

;; Countable additivity is stated through convergence of finite partial sums.

(defun-sk ht062-events-disjoint-p
    (space left right)
  (forall (omega)
    (implies
     (ht062-sample-p space omega)
     (not
      (and
       (ht062-event-member-p space left omega)
       (ht062-event-member-p space right omega))))))

(defun-sk ht062-pairwise-disjoint-sequence-p
    (space sequence)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (not (equal left-index right-index)))
     (ht062-events-disjoint-p
      space
      (ht062-sequence-event space sequence left-index)
      (ht062-sequence-event space sequence right-index)))))

(defun ht062-measure-prefix
    (field space measure sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht062-zero field)
    (let ((index (1- count)))
      (ht062-add
       field
       (ht062-measure-prefix
        field space measure sequence index)
       (ht062-measure-value
        field
        space
        measure
        (ht062-sequence-event space sequence index))))))

(defun-sk ht062-measure-limit-tail-p
    (field space measure sequence limit epsilon cutoff)
  (forall (count)
    (implies
     (and
      (natp count)
      (natp cutoff)
      (<= cutoff count))
     (ht062-less
      field
      (ht062-absolute-value
       field
       (ht062-subtract
        field
        (ht062-measure-prefix
         field space measure sequence count)
        limit))
      epsilon))))

(defun-sk ht062-measure-limit-cutoff-exists-p
    (field space measure sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht062-measure-limit-tail-p
      field space measure sequence limit epsilon cutoff))))

(defun-sk ht062-measure-prefix-converges-p
    (field space measure sequence limit)
  (forall (epsilon)
    (implies
     (and
      (ht062-scalar-p field epsilon)
      (ht062-less field (ht062-zero field) epsilon))
     (ht062-measure-limit-cutoff-exists-p
      field space measure sequence limit epsilon))))

(defun-sk ht062-measure-values-p
    (field space sigma measure)
  (forall (event)
    (implies
     (ht062-sigma-event-p space sigma event)
     (and
      (ht062-scalar-p
       field (ht062-measure-value field space measure event))
      (ht062-leq-p
       field
       (ht062-zero field)
       (ht062-measure-value field space measure event))
      (ht062-leq-p
       field
       (ht062-measure-value field space measure event)
       (ht062-one field))))))

(defun-sk ht062-measure-extensional-p
    (field space sigma measure)
  (forall (left right)
    (implies
     (and
      (ht062-sigma-event-p space sigma left)
      (ht062-sigma-event-p space sigma right)
      (ht062-events-extensionally-equal-p space left right))
     (equal
      (ht062-measure-value field space measure left)
      (ht062-measure-value field space measure right)))))

(defun-sk ht062-countably-additive-p
    (field space sigma measure)
  (forall (sequence)
    (implies
     (and
      (ht062-sigma-event-sequence-p space sigma sequence)
      (ht062-pairwise-disjoint-sequence-p space sequence))
     (ht062-measure-prefix-converges-p
      field
      space
      measure
      sequence
      (ht062-measure-value
       field
       space
       measure
       (ht062-countable-union-event space sequence))))))

(defun ht062-probability-space-p
    (field space sigma measure)
  (and
   (ht062-real-field-p field)
   (ht062-event-structure-p space)
   (ht062-sigma-algebra-p space sigma)
   (ht062-measure-values-p field space sigma measure)
   (ht062-measure-extensional-p field space sigma measure)
   (equal
    (ht062-measure-value
     field space measure (ht062-empty-event space))
    (ht062-zero field))
   (equal
    (ht062-measure-value
     field space measure (ht062-full-event space))
    (ht062-one field))
   (ht062-countably-additive-p field space sigma measure)))

;; Random variables and their signed Lebesgue expectations.  The positive
;; and negative parts are characterized by the standard dyadic lower sums
;;
;;   2^-n * sum_{1 <= k <= n*2^n} P(k/2^n <= Y).

(defun ht062-positive-part (field value)
  (ht062-maximum field (ht062-zero field) value))

(defun ht062-negative-part (field value)
  (ht062-maximum
   field (ht062-zero field) (ht062-negate field value)))

(defun ht062-signed-part (field positivep value)
  (if positivep
      (ht062-positive-part field value)
    (ht062-negative-part field value)))

(defun-sk ht062-variable-values-p (field space)
  (forall (variable omega)
    (implies
     (and
      (ht062-variable-p field space variable)
      (ht062-sample-p space omega))
     (ht062-scalar-p
      field
      (ht062-variable-value field space variable omega)))))

(defun-sk ht062-sublevel-event-laws-p (field space)
  (forall (variable threshold omega)
    (implies
     (and
      (ht062-variable-p field space variable)
      (ht062-scalar-p field threshold)
      (ht062-sample-p space omega))
     (and
      (ht062-event-p
       space
       (ht062-sublevel-event
        field space variable threshold))
      (iff
       (ht062-event-member-p
        space
        (ht062-sublevel-event
         field space variable threshold)
        omega)
       (ht062-leq-p
        field
        (ht062-variable-value field space variable omega)
        threshold))))))

(defun-sk ht062-level-event-laws-p (field space)
  (forall (variable positivep threshold omega)
    (implies
     (and
      (ht062-variable-p field space variable)
      (booleanp positivep)
      (ht062-scalar-p field threshold)
      (ht062-leq-p field (ht062-zero field) threshold)
      (ht062-sample-p space omega))
     (and
      (ht062-event-p
       space
       (ht062-level-event
        field space variable positivep threshold))
      (iff
       (ht062-event-member-p
        space
        (ht062-level-event
         field space variable positivep threshold)
        omega)
       (ht062-leq-p
        field
        threshold
        (ht062-signed-part
         field
         positivep
         (ht062-variable-value
          field space variable omega))))))))

(defun-sk ht062-process-value-laws-p (field space)
  (forall (process index omega)
    (implies
     (and
      (ht062-process-p field space process)
      (natp index)
      (ht062-sample-p space omega))
     (and
      (ht062-scalar-p
       field
       (ht062-process-value
        field space process index omega))
      (ht062-variable-p
       field
       space
       (ht062-process-fiber field space process index))
      (equal
       (ht062-variable-value
        field
        space
        (ht062-process-fiber field space process index)
        omega)
       (ht062-process-value
        field space process index omega))))))

(defun-sk ht062-restricted-variable-laws-p (field space)
  (forall (variable event omega)
    (implies
     (and
      (ht062-variable-p field space variable)
      (ht062-event-p space event)
      (ht062-sample-p space omega))
     (and
      (ht062-variable-p
       field
       space
       (ht062-restricted-variable
        field space variable event))
      (equal
       (ht062-variable-value
        field
        space
        (ht062-restricted-variable
         field space variable event)
        omega)
       (if (ht062-event-member-p space event omega)
           (ht062-variable-value
            field space variable omega)
         (ht062-zero field)))))))

(defun ht062-basic-variable-structure-p (field space)
  (and
   (ht062-variable-values-p field space)
   (ht062-sublevel-event-laws-p field space)
   (ht062-level-event-laws-p field space)
   (ht062-process-value-laws-p field space)
   (ht062-restricted-variable-laws-p field space)))

(defun-sk ht062-random-variable-p
    (field space sigma variable)
  (forall (threshold)
    (implies
     (ht062-scalar-p field threshold)
     (and
      (ht062-sigma-event-p
       space
       sigma
       (ht062-sublevel-event
        field space variable threshold))
      (implies
       (ht062-leq-p field (ht062-zero field) threshold)
       (and
        (ht062-sigma-event-p
         space
         sigma
         (ht062-level-event
          field space variable t threshold))
        (ht062-sigma-event-p
         space
         sigma
         (ht062-level-event
          field space variable nil threshold))))))))

(defun ht062-dyadic-denominator (field exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht062-one field)
    (ht062-multiply
     field
     (ht062-add
      field (ht062-one field) (ht062-one field))
     (ht062-dyadic-denominator field (1- exponent)))))

(defun ht062-level-measure-sum
    (field space measure variable positivep denominator count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht062-zero field)
    (let* ((index (nfix count))
           (threshold
            (ht062-divide
             field
             (ht062-real-nat field index)
             denominator)))
      (ht062-add
       field
       (ht062-level-measure-sum
        field
        space
        measure
        variable
        positivep
        denominator
        (1- count))
       (ht062-measure-value
        field
        space
        measure
        (ht062-level-event
         field space variable positivep threshold))))))

(defun ht062-expectation-approximation
    (field space measure variable positivep index)
  (let* ((native-index (nfix index))
         (native-power (expt 2 native-index))
         (count (* native-index native-power))
         (denominator
          (ht062-dyadic-denominator field native-index)))
    (ht062-multiply
     field
     (ht062-inverse field denominator)
     (ht062-level-measure-sum
      field
      space
      measure
      variable
      positivep
      denominator
      count))))

(defun-sk ht062-expectation-limit-tail-p
    (field space measure variable positivep
           limit epsilon cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (natp cutoff)
      (<= cutoff index))
     (ht062-less
      field
      (ht062-absolute-value
       field
       (ht062-subtract
        field
        (ht062-expectation-approximation
         field space measure variable positivep index)
        limit))
      epsilon))))

(defun-sk ht062-expectation-limit-cutoff-exists-p
    (field space measure variable positivep limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht062-expectation-limit-tail-p
      field
      space
      measure
      variable
      positivep
      limit
      epsilon
      cutoff))))

(defun-sk ht062-nonnegative-expectation-p
    (field space measure variable positivep limit)
  (forall (epsilon)
    (implies
     (and
      (ht062-scalar-p field epsilon)
      (ht062-less field (ht062-zero field) epsilon))
     (and
      (ht062-scalar-p field limit)
      (ht062-leq-p field (ht062-zero field) limit)
      (ht062-expectation-limit-cutoff-exists-p
       field
       space
       measure
       variable
       positivep
       limit
       epsilon)))))

(defun-sk ht062-has-expectation-p
    (field space sigma measure variable value)
  (exists (positive-value negative-value)
    (and
     (ht062-variable-p field space variable)
     (ht062-random-variable-p field space sigma variable)
     (ht062-nonnegative-expectation-p
      field space measure variable t positive-value)
     (ht062-nonnegative-expectation-p
      field space measure variable nil negative-value)
     (ht062-scalar-p field value)
     (equal
      value
      (ht062-subtract
       field positive-value negative-value)))))

(defun-sk ht062-integrable-p
    (field space sigma measure variable)
  (exists (value)
    (ht062-has-expectation-p
     field space sigma measure variable value)))

(defun-sk ht062-expectation-le-p
    (field space sigma measure left right)
  (exists (left-value right-value)
    (and
     (ht062-has-expectation-p
      field space sigma measure left left-value)
     (ht062-has-expectation-p
      field space sigma measure right right-value)
     (ht062-leq-p field left-value right-value))))

(defun-sk ht062-expectation-equal-p
    (field space sigma measure left right)
  (exists (left-value right-value)
    (and
     (ht062-has-expectation-p
      field space sigma measure left left-value)
     (ht062-has-expectation-p
      field space sigma measure right right-value)
     (equal left-value right-value))))

;; Filtrations and set-integral martingales.

(defun-sk ht062-filtration-levels-p
    (space sigma filtration)
  (forall (index)
    (implies
     (natp index)
     (let ((level
            (ht062-filtration-sigma space filtration index)))
       (and
        (ht062-sigma-algebra-p space level)
        (ht062-sub-sigma-algebra-p
         space level sigma))))))

(defun-sk ht062-filtration-monotone-p
    (space filtration)
  (forall (left-index right-index)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (<= left-index right-index))
     (ht062-sub-sigma-algebra-p
      space
      (ht062-filtration-sigma
       space filtration left-index)
      (ht062-filtration-sigma
       space filtration right-index)))))

(defun ht062-filtration-p (space sigma filtration)
  (and
   (ht062-filtration-levels-p space sigma filtration)
   (ht062-filtration-monotone-p space filtration)))

(defun-sk ht062-cover-contains-point-p
    (space sequence omega)
  (exists (index)
    (and
     (natp index)
     (ht062-event-member-p
      space
      (ht062-sequence-event space sequence index)
      omega))))

(defun-sk ht062-cover-covers-space-p (space sequence)
  (forall (omega)
    (implies
     (ht062-sample-p space omega)
     (ht062-cover-contains-point-p
      space sequence omega))))

(defun-sk ht062-sigma-finite-p
    (field space sigma measure)
  (exists (cover)
    (and
     (ht062-sigma-event-sequence-p space sigma cover)
     (ht062-cover-covers-space-p space cover)
     (ht062-measure-values-p field space sigma measure))))

(defun-sk ht062-sigma-finite-filtration-p
    (field space measure filtration)
  (forall (index)
    (implies
     (natp index)
     (ht062-sigma-finite-p
      field
      space
      (ht062-filtration-sigma space filtration index)
      measure))))

(defun-sk ht062-adapted-p
    (field space filtration process)
  (forall (index)
    (implies
     (natp index)
     (ht062-random-variable-p
      field
      space
      (ht062-filtration-sigma space filtration index)
      (ht062-process-fiber field space process index)))))

(defun ht062-strongly-adapted-p
    (field space filtration process)
  (ht062-adapted-p field space filtration process))

(defun-sk ht062-integrable-process-p
    (field space sigma measure process)
  (forall (index)
    (implies
     (natp index)
     (ht062-integrable-p
      field
      space
      sigma
      measure
      (ht062-process-fiber
       field space process index)))))

(defun-sk ht062-submartingale-relation-p
    (field space sigma measure filtration process)
  (forall (left-index right-index event)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (<= left-index right-index)
      (ht062-sigma-event-p
       space
       (ht062-filtration-sigma
        space filtration left-index)
       event))
     (ht062-expectation-le-p
      field
      space
      sigma
      measure
      (ht062-restricted-variable
       field
       space
       (ht062-process-fiber
        field space process left-index)
       event)
      (ht062-restricted-variable
       field
       space
       (ht062-process-fiber
        field space process right-index)
       event)))))

(defun-sk ht062-martingale-relation-p
    (field space sigma measure filtration process)
  (forall (left-index right-index event)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (<= left-index right-index)
      (ht062-sigma-event-p
       space
       (ht062-filtration-sigma
        space filtration left-index)
       event))
     (ht062-expectation-equal-p
      field
      space
      sigma
      measure
      (ht062-restricted-variable
       field
       space
       (ht062-process-fiber
        field space process left-index)
       event)
      (ht062-restricted-variable
       field
       space
       (ht062-process-fiber
        field space process right-index)
       event)))))

(defun-sk ht062-supermartingale-relation-p
    (field space sigma measure filtration process)
  (forall (left-index right-index event)
    (implies
     (and
      (natp left-index)
      (natp right-index)
      (<= left-index right-index)
      (ht062-sigma-event-p
       space
       (ht062-filtration-sigma
        space filtration left-index)
       event))
     (ht062-expectation-le-p
      field
      space
      sigma
      measure
      (ht062-restricted-variable
       field
       space
       (ht062-process-fiber
        field space process right-index)
       event)
      (ht062-restricted-variable
       field
       space
       (ht062-process-fiber
        field space process left-index)
       event)))))

(defun ht062-submartingale-p
    (field space sigma measure filtration process)
  (and
   (ht062-process-p field space process)
   (ht062-adapted-p field space filtration process)
   (ht062-integrable-process-p
    field space sigma measure process)
   (ht062-submartingale-relation-p
    field space sigma measure filtration process)))

(defun ht062-martingale-p
    (field space sigma measure filtration process)
  (and
   (ht062-process-p field space process)
   (ht062-adapted-p field space filtration process)
   (ht062-integrable-process-p
    field space sigma measure process)
   (ht062-martingale-relation-p
    field space sigma measure filtration process)))

(defun ht062-supermartingale-p
    (field space sigma measure filtration process)
  (and
   (ht062-process-p field space process)
   (ht062-adapted-p field space filtration process)
   (ht062-integrable-process-p
    field space sigma measure process)
   (ht062-supermartingale-relation-p
    field space sigma measure filtration process)))

;; Stopping times, stopped variables, and stopped processes.

(defun-sk ht062-stopping-code-laws-p (space)
  (forall (stopping-time omega)
    (implies
     (and
      (ht062-stopping-code-p space stopping-time)
      (ht062-sample-p space omega))
     (if (ht062-stopping-finite-p
          space stopping-time omega)
         (natp
          (ht062-stopping-index
           space stopping-time omega))
       (equal
        (ht062-stopping-index
         space stopping-time omega)
        0)))))

(defun-sk ht062-stopping-event-laws-p (space)
  (forall (stopping-time bound omega)
    (implies
     (and
      (ht062-stopping-code-p space stopping-time)
      (natp bound)
      (ht062-sample-p space omega))
     (and
      (ht062-event-p
       space
       (ht062-stopping-le-event
        space stopping-time bound))
      (iff
       (ht062-event-member-p
        space
        (ht062-stopping-le-event
         space stopping-time bound)
        omega)
       (and
        (ht062-stopping-finite-p
         space stopping-time omega)
        (<=
         (ht062-stopping-index
          space stopping-time omega)
         bound)))))))

(defun-sk ht062-stopped-variable-laws-p (field space)
  (forall (process stopping-time omega)
    (implies
     (and
      (ht062-process-p field space process)
      (ht062-stopping-code-p space stopping-time)
      (ht062-sample-p space omega))
     (and
      (ht062-variable-p
       field
       space
       (ht062-stopped-variable
        field space process stopping-time))
      (equal
       (ht062-variable-value
        field
        space
        (ht062-stopped-variable
         field space process stopping-time)
        omega)
       (if (ht062-stopping-finite-p
            space stopping-time omega)
           (ht062-process-value
            field
            space
            process
            (ht062-stopping-index
             space stopping-time omega)
            omega)
         (ht062-zero field)))))))

(defun-sk ht062-stopping-value-laws-p (field space)
  (forall (stopping-time omega)
    (implies
     (and
      (ht062-stopping-code-p space stopping-time)
      (ht062-sample-p space omega))
     (and
      (ht062-variable-p
       field
       space
       (ht062-stopping-value-variable
        field space stopping-time))
      (equal
       (ht062-variable-value
        field
        space
        (ht062-stopping-value-variable
         field space stopping-time)
        omega)
       (if (ht062-stopping-finite-p
            space stopping-time omega)
           (ht062-real-nat
            field
            (ht062-stopping-index
             space stopping-time omega))
         (ht062-zero field)))))))

(defun-sk ht062-stopped-process-laws-p (field space)
  (forall (process stopping-time index omega)
    (implies
     (and
      (ht062-process-p field space process)
      (ht062-stopping-code-p space stopping-time)
      (natp index)
      (ht062-sample-p space omega))
     (let ((stopped-process
            (ht062-stopped-process
             field space process stopping-time)))
       (and
        (ht062-process-p field space stopped-process)
        (equal
         (ht062-process-value
          field space stopped-process index omega)
         (if
          (and
           (ht062-stopping-finite-p
            space stopping-time omega)
           (<=
            (ht062-stopping-index
             space stopping-time omega)
            index))
          (ht062-process-value
           field
           space
           process
           (ht062-stopping-index
            space stopping-time omega)
           omega)
          (ht062-process-value
           field space process index omega))))))))

(defun ht062-stopping-structure-p (field space)
  (and
   (ht062-stopping-code-laws-p space)
   (ht062-stopping-event-laws-p space)
   (ht062-stopped-variable-laws-p field space)
   (ht062-stopping-value-laws-p field space)
   (ht062-stopped-process-laws-p field space)))

(defun-sk ht062-stopping-time-wrt-p
    (space filtration stopping-time)
  (forall (bound)
    (implies
     (natp bound)
     (and
      (ht062-stopping-code-p space stopping-time)
      (ht062-sigma-event-p
       space
       (ht062-filtration-sigma
        space filtration bound)
       (ht062-stopping-le-event
        space stopping-time bound))))))

(defun ht062-extended-time-le-p
    (space left right omega)
  (if (ht062-stopping-finite-p space left omega)
      (or
       (not
        (ht062-stopping-finite-p space right omega))
       (<=
        (ht062-stopping-index space left omega)
        (ht062-stopping-index space right omega)))
    (not
     (ht062-stopping-finite-p space right omega))))

(defun-sk ht062-stopping-times-ordered-p
    (space left right)
  (forall (omega)
    (implies
     (ht062-sample-p space omega)
     (ht062-extended-time-le-p
      space left right omega))))

(defun-sk ht062-bounded-stopping-time-at-p
    (space stopping-time bound)
  (forall (omega)
    (implies
     (ht062-sample-p space omega)
     (and
      (ht062-stopping-finite-p
       space stopping-time omega)
      (<=
       (ht062-stopping-index
        space stopping-time omega)
       bound)))))

(defun-sk ht062-bounded-stopping-time-p
    (space stopping-time)
  (exists (bound)
    (and
     (natp bound)
     (ht062-bounded-stopping-time-at-p
      space stopping-time bound))))

(defun ht062-almost-sure-event-p
    (field space sigma measure event)
  (and
   (ht062-sigma-event-p space sigma event)
   (equal
    (ht062-measure-value field space measure event)
    (ht062-one field))))

(defun-sk ht062-time-bounded-on-event-p
    (space stopping-time bound event)
  (forall (omega)
    (implies
     (and
      (ht062-sample-p space omega)
      (ht062-event-member-p space event omega))
     (and
      (ht062-stopping-finite-p
       space stopping-time omega)
      (<=
       (ht062-stopping-index
        space stopping-time omega)
       bound)))))

(defun-sk ht062-almost-surely-bounded-p
    (field space sigma measure stopping-time)
  (exists (bound event)
    (and
     (natp bound)
     (ht062-almost-sure-event-p
      field space sigma measure event)
     (ht062-time-bounded-on-event-p
      space stopping-time bound event))))

(defun-sk ht062-time-finite-on-event-p
    (space stopping-time event)
  (forall (omega)
    (implies
     (and
      (ht062-sample-p space omega)
      (ht062-event-member-p space event omega))
     (ht062-stopping-finite-p
      space stopping-time omega))))

(defun-sk ht062-almost-surely-finite-p
    (field space sigma measure stopping-time)
  (exists (event)
    (and
     (ht062-almost-sure-event-p
      field space sigma measure event)
     (ht062-time-finite-on-event-p
      space stopping-time event))))

(defun-sk ht062-process-level-bounded-on-event-p
    (field space process index bound event)
  (forall (omega)
    (implies
     (and
      (ht062-sample-p space omega)
      (ht062-event-member-p space event omega))
     (ht062-less
      field
      (ht062-absolute-value
       field
       (ht062-process-value
        field space process index omega))
      bound))))

(defun-sk ht062-process-level-bound-witness-p
    (field space sigma measure process index bound)
  (exists (event)
    (and
     (ht062-almost-sure-event-p
      field space sigma measure event)
     (ht062-process-level-bounded-on-event-p
      field space process index bound event))))

(defun-sk ht062-all-process-levels-bounded-p
    (field space sigma measure process bound)
  (forall (index)
    (implies
     (natp index)
     (ht062-process-level-bound-witness-p
      field
      space
      sigma
      measure
      process
      index
      bound))))

(defun-sk ht062-uniformly-bounded-process-p
    (field space sigma measure process)
  (exists (bound)
    (and
     (ht062-scalar-p field bound)
     (ht062-all-process-levels-bounded-p
      field space sigma measure process bound))))

(defun-sk ht062-increment-bounded-on-event-p
    (field space process index bound event)
  (forall (omega)
    (implies
     (and
      (ht062-sample-p space omega)
      (ht062-event-member-p space event omega))
     (ht062-leq-p
      field
      (ht062-absolute-value
       field
       (ht062-subtract
        field
        (ht062-process-value
         field space process (1+ index) omega)
        (ht062-process-value
         field space process index omega)))
      bound))))

(defun-sk ht062-increment-bound-witness-p
    (field space sigma measure process index bound)
  (exists (event)
    (and
     (ht062-almost-sure-event-p
      field space sigma measure event)
     (ht062-increment-bounded-on-event-p
      field space process index bound event))))

(defun-sk ht062-all-increments-bounded-p
    (field space sigma measure process bound)
  (forall (index)
    (implies
     (natp index)
     (ht062-increment-bound-witness-p
      field
      space
      sigma
      measure
      process
      index
      bound))))

(defun-sk ht062-bounded-process-increments-p
    (field space sigma measure process)
  (exists (bound)
    (and
     (ht062-scalar-p field bound)
     (ht062-all-increments-bounded-p
      field space sigma measure process bound))))

(defun ht062-finite-expected-stopping-time-p
    (field space sigma measure stopping-time)
  (and
   (ht062-almost-surely-finite-p
    field space sigma measure stopping-time)
   (ht062-integrable-p
    field
    space
    sigma
    measure
    (ht062-stopping-value-variable
     field space stopping-time))))

(defun ht062-optional-stopping-conditions-p
    (field space sigma measure process stopping-time)
  (or
   (ht062-almost-surely-bounded-p
    field space sigma measure stopping-time)
   (and
    (ht062-almost-surely-finite-p
     field space sigma measure stopping-time)
    (ht062-uniformly-bounded-process-p
     field space sigma measure process))
   (and
    (ht062-finite-expected-stopping-time-p
     field space sigma measure stopping-time)
    (ht062-bounded-process-increments-p
     field space sigma measure process))))

;; Contexts and the five indexed statements.

(defun ht062-characterization-context-p
    (field space sigma measure filtration process)
  (and
   (ht062-probability-space-p field space sigma measure)
   (ht062-basic-variable-structure-p field space)
   (ht062-stopping-structure-p field space)
   (ht062-filtration-p space sigma filtration)
   (ht062-sigma-finite-filtration-p
    field space measure filtration)
   (ht062-process-p field space process)
   (ht062-strongly-adapted-p
    field space filtration process)
   (ht062-integrable-process-p
    field space sigma measure process)))

(defun-sk ht062-bounded-stopped-expectations-monotone-p
    (field space sigma measure filtration process)
  (forall (earlier-time later-time)
    (implies
     (and
      (ht062-stopping-time-wrt-p
       space filtration earlier-time)
      (ht062-stopping-time-wrt-p
       space filtration later-time)
      (ht062-stopping-times-ordered-p
       space earlier-time later-time)
      (ht062-bounded-stopping-time-p
       space later-time))
     (ht062-expectation-le-p
      field
      space
      sigma
      measure
      (ht062-stopped-variable
       field space process earlier-time)
      (ht062-stopped-variable
       field space process later-time)))))

(defun hundred-theorems-062-submartingale-characterization-statement
    (field space sigma measure filtration process)
  (implies
   (ht062-characterization-context-p
    field space sigma measure filtration process)
   (iff
    (ht062-submartingale-p
     field space sigma measure filtration process)
    (ht062-bounded-stopped-expectations-monotone-p
     field space sigma measure filtration process))))

(defun ht062-single-stop-context-p
    (field space sigma measure filtration process stopping-time)
  (and
   (ht062-probability-space-p field space sigma measure)
   (ht062-basic-variable-structure-p field space)
   (ht062-stopping-structure-p field space)
   (ht062-filtration-p space sigma filtration)
   (ht062-process-p field space process)
   (ht062-adapted-p field space filtration process)
   (ht062-integrable-process-p
    field space sigma measure process)
   (ht062-stopping-time-wrt-p
    space filtration stopping-time)
   (ht062-optional-stopping-conditions-p
    field space sigma measure process stopping-time)))

(defun hundred-theorems-062-stopped-process-integrable-statement
    (field space sigma measure filtration process stopping-time)
  (implies
   (ht062-single-stop-context-p
    field
    space
    sigma
    measure
    filtration
    process
    stopping-time)
   (ht062-integrable-p
    field
    space
    sigma
    measure
    (ht062-stopped-variable
     field space process stopping-time))))

(defun hundred-theorems-062-martingale-optional-stopping-statement
    (field space sigma measure filtration process stopping-time)
  (implies
   (and
    (ht062-single-stop-context-p
     field
     space
     sigma
     measure
     filtration
     process
     stopping-time)
    (ht062-martingale-p
     field space sigma measure filtration process))
   (ht062-expectation-equal-p
    field
    space
    sigma
    measure
    (ht062-stopped-variable
     field space process stopping-time)
    (ht062-process-fiber field space process 0))))

(defun hundred-theorems-062-submartingale-optional-stopping-statement
    (field space sigma measure filtration process stopping-time)
  (implies
   (and
    (ht062-single-stop-context-p
     field
     space
     sigma
     measure
     filtration
     process
     stopping-time)
    (ht062-submartingale-p
     field space sigma measure filtration process))
   (ht062-expectation-le-p
    field
    space
    sigma
    measure
    (ht062-process-fiber field space process 0)
    (ht062-stopped-variable
     field space process stopping-time))))

(defun hundred-theorems-062-supermartingale-optional-stopping-statement
    (field space sigma measure filtration process stopping-time)
  (implies
   (and
    (ht062-single-stop-context-p
     field
     space
     sigma
     measure
     filtration
     process
     stopping-time)
    (ht062-supermartingale-p
     field space sigma measure filtration process))
   (ht062-expectation-le-p
    field
    space
    sigma
    measure
    (ht062-stopped-variable
     field space process stopping-time)
    (ht062-process-fiber field space process 0))))

(value-triple :itpeval-statement-checked)
:q
