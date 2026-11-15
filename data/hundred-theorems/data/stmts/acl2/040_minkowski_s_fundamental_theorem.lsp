;; Statement-only formalization of Hundred Theorems item 040,
;; "Minkowski's Fundamental Theorem." In positive-dimensional real
;; coordinate space, a measurable convex set symmetric about the origin and
;; of Lebesgue volume greater than 2^n contains a nonzero integer point. The
;; compact form permits volume equal to 2^n. The corresponding concrete
;; Blichfeldt principle is included as in the other corpus formalizations.
;; This file contains no proof.
;;
;; Semantic status: the first-order rewrite below repairs the former vacuous
;; generated-lambda encoding, but its stub-coded real sets and measures have
;; no comprehension principle. It cannot preserve the source's full real
;; measurable-set and Lebesgue-volume domains in standard ACL2, so it is not
;; counted as a faithful translation.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Generic first-order application interfaces interpret tags as predicates
;; and unary functions. All mathematical quantifiers are direct DEFUN-SK
;; quantifiers; no generated lambda is passed through APPLY$.

(defstub ht040-apply1 (function argument) t)

(defstub ht040-apply2 (function left right) t)

(defun ht040-member-p (predicate object)
  (if (ht040-apply1 predicate object) t nil))

;; A scalar context consists of a carrier predicate, zero, one, addition,
;; multiplication, negation, inversion, and strict order.

(defun ht040-r-carrier (real) (nth 0 real))
(defun ht040-r-zero (real) (nth 1 real))
(defun ht040-r-one (real) (nth 2 real))
(defun ht040-r-add (real) (nth 3 real))
(defun ht040-r-multiply (real) (nth 4 real))
(defun ht040-r-negate (real) (nth 5 real))
(defun ht040-r-inverse (real) (nth 6 real))
(defun ht040-r-less (real) (nth 7 real))

(defun ht040-real-p (real value)
  (ht040-member-p (ht040-r-carrier real) value))

(defun ht040-zero (real)
  (ht040-r-zero real))

(defun ht040-one (real)
  (ht040-r-one real))

(defun ht040-add (real left right)
  (ht040-apply2 (ht040-r-add real) left right))

(defun ht040-multiply (real left right)
  (ht040-apply2 (ht040-r-multiply real) left right))

(defun ht040-negate (real value)
  (ht040-apply1 (ht040-r-negate real) value))

(defun ht040-inverse (real value)
  (ht040-apply1 (ht040-r-inverse real) value))

(defun ht040-less (real left right)
  (if (ht040-apply2 (ht040-r-less real) left right)
      t
    nil))

(defun ht040-subtract (real left right)
  (ht040-add real left (ht040-negate real right)))

(defun ht040-less-equal-p (real left right)
  (not (ht040-less real right left)))

(defun ht040-absolute-value (real value)
  (if (ht040-less real value (ht040-zero real))
      (ht040-negate real value)
    value))

(defun ht040-positive-real-p (real value)
  (and
   (ht040-real-p real value)
   (ht040-less real (ht040-zero real) value)))

;; A Dedekind-complete ordered field presents the real numbers.

(defun-sk ht040-field-laws-p (real)
  (forall (a b c)
    (implies
     (and
      (ht040-real-p real a)
      (ht040-real-p real b)
      (ht040-real-p real c))
     (let* ((ab-add (ht040-add real a b))
            (bc-add (ht040-add real b c))
            (ab-mul (ht040-multiply real a b))
            (bc-mul (ht040-multiply real b c))
            (neg-a (ht040-negate real a))
            (inv-a (ht040-inverse real a))
            (zero (ht040-zero real))
            (one (ht040-one real)))
       (and
        (ht040-real-p real ab-add)
        (ht040-real-p real ab-mul)
        (ht040-real-p real neg-a)
        (ht040-real-p real inv-a)
        (equal
         (ht040-add real ab-add c)
         (ht040-add real a bc-add))
        (equal ab-add (ht040-add real b a))
        (equal (ht040-add real a zero) a)
        (equal (ht040-add real a neg-a) zero)
        (equal
         (ht040-multiply real ab-mul c)
         (ht040-multiply real a bc-mul))
        (equal ab-mul (ht040-multiply real b a))
        (equal (ht040-multiply real a one) a)
        (equal
         (ht040-multiply real a bc-add)
         (ht040-add
          real
          (ht040-multiply real a b)
          (ht040-multiply real a c)))
        (implies
         (equal a zero)
         (equal inv-a zero))
        (implies
         (not (equal a zero))
         (equal
          (ht040-multiply real a inv-a)
          one)))))))

(defun-sk ht040-order-laws-p (real)
  (forall (a b c)
    (implies
     (and
      (ht040-real-p real a)
      (ht040-real-p real b)
      (ht040-real-p real c))
     (and
      (not (ht040-less real a a))
      (or
       (ht040-less real a b)
       (equal a b)
       (ht040-less real b a))
      (implies
       (and
        (ht040-less real a b)
        (ht040-less real b c))
       (ht040-less real a c))
      (implies
       (ht040-less real a b)
       (ht040-less
        real
        (ht040-add real a c)
        (ht040-add real b c)))
      (implies
       (and
        (ht040-less real (ht040-zero real) a)
        (ht040-less real (ht040-zero real) b))
       (ht040-less
        real
        (ht040-zero real)
        (ht040-multiply real a b)))))))

(defun-sk ht040-valid-real-set-p (real set)
  (forall (value)
    (implies
     (ht040-member-p set value)
     (ht040-real-p real value))))

(defun-sk ht040-real-set-nonempty-p (real set)
  (exists (value)
    (and
     (ht040-real-p real value)
     (ht040-member-p set value))))

(defun-sk ht040-real-upper-bound-p
    (real set upper)
  (forall (value)
    (implies
     (and
      (ht040-real-p real value)
      (ht040-member-p set value))
     (ht040-less-equal-p real value upper))))

(defun-sk ht040-real-bounded-above-p
    (real set)
  (exists (upper)
    (and
     (ht040-real-p real upper)
     (ht040-real-upper-bound-p
      real set upper))))

(defun-sk ht040-real-supremum-p
    (real set supremum)
  (forall (upper)
    (and
     (ht040-real-p real supremum)
     (ht040-real-upper-bound-p
      real set supremum)
     (implies
      (and
       (ht040-real-p real upper)
       (ht040-real-upper-bound-p
        real set upper))
      (ht040-less-equal-p
       real supremum upper)))))

(defun-sk ht040-real-has-supremum-p
    (real set)
  (exists (supremum)
    (ht040-real-supremum-p
     real set supremum)))

(defun-sk ht040-completeness-p (real)
  (forall (set)
    (implies
     (and
      (ht040-valid-real-set-p real set)
      (ht040-real-set-nonempty-p real set)
      (ht040-real-bounded-above-p real set))
     (ht040-real-has-supremum-p
      real set))))

(defun ht040-field-natural (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (ht040-zero real)
    (ht040-add
     real
     (ht040-one real)
     (ht040-field-natural real (- n 1)))))

(defun-sk ht040-archimedean-witness-exists-p
    (real value)
  (exists (natural)
    (and
     (natp natural)
     (ht040-less
      real
      value
      (ht040-field-natural real natural)))))

(defun-sk ht040-archimedean-p (real)
  (forall (value)
    (implies
     (ht040-real-p real value)
     (ht040-archimedean-witness-exists-p
      real value))))

(defun ht040-real-field-p (real)
  (and
   (true-listp real)
   (equal (len real) 8)
   (ht040-real-p real (ht040-zero real))
   (ht040-real-p real (ht040-one real))
   (not
    (equal
     (ht040-zero real)
     (ht040-one real)))
   (ht040-less
    real (ht040-zero real) (ht040-one real))
   (ht040-field-laws-p real)
   (ht040-order-laws-p real)
   (ht040-completeness-p real)
   (ht040-archimedean-p real)))

;; Natural powers and the canonical integer embedding into the real field.

(defun ht040-field-power (real base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (ht040-one real)
    (ht040-multiply
     real
     base
     (ht040-field-power
      real base (- exponent 1)))))

(defun ht040-two-power (real dimension)
  (ht040-field-power
   real
   (ht040-add
    real (ht040-one real) (ht040-one real))
   dimension))

(defun ht040-field-integer (real integer)
  (if (< integer 0)
      (ht040-negate
       real
       (ht040-field-natural real (- integer)))
    (ht040-field-natural real integer)))

(defun-sk ht040-scalar-integer-p
    (real value)
  (exists (integer)
    (and
     (integerp integer)
     (equal
      value
      (ht040-field-integer real integer)))))

;; Points of R^n are exact lists of n real coordinates.

(defun ht040-point-p (real dimension point)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      (equal point nil)
    (and
     (consp point)
     (ht040-real-p real (car point))
     (ht040-point-p
      real (- dimension 1) (cdr point)))))

(defun ht040-zero-point (real dimension)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      nil
    (cons
     (ht040-zero real)
     (ht040-zero-point real (- dimension 1)))))

(defun ht040-point-add
    (real dimension left right)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      nil
    (cons
     (ht040-add real (car left) (car right))
     (ht040-point-add
      real
      (- dimension 1)
      (cdr left)
      (cdr right)))))

(defun ht040-point-negate
    (real dimension point)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      nil
    (cons
     (ht040-negate real (car point))
     (ht040-point-negate
      real (- dimension 1) (cdr point)))))

(defun ht040-point-subtract
    (real dimension left right)
  (ht040-point-add
   real
   dimension
   left
   (ht040-point-negate real dimension right)))

(defun ht040-point-scale
    (real dimension scalar point)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      nil
    (cons
     (ht040-multiply real scalar (car point))
     (ht040-point-scale
      real
      (- dimension 1)
      scalar
      (cdr point)))))

(defun ht040-point-close-p
    (real dimension left right epsilon)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      t
    (and
     (ht040-less
      real
      (ht040-absolute-value
       real
       (ht040-subtract
        real (car left) (car right)))
      epsilon)
     (ht040-point-close-p
      real
      (- dimension 1)
      (cdr left)
      (cdr right)
      epsilon))))

(defun ht040-integer-point-p
    (real dimension point)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      (equal point nil)
    (and
     (consp point)
     (ht040-scalar-integer-p real (car point))
     (ht040-integer-point-p
      real (- dimension 1) (cdr point)))))

;; Region descriptors make intersection and difference explicit without
;; constructing executable lambdas.

(defun ht040-base-region (predicate)
  (list :ht040-base predicate))

(defun ht040-intersection-region (left right)
  (list :ht040-intersection left right))

(defun ht040-difference-region (left right)
  (list :ht040-difference left right))

(defun ht040-base-region-p (region)
  (and
   (true-listp region)
   (equal (len region) 2)
   (equal (car region) :ht040-base)))

(defun ht040-base-region-member-p
    (region point)
  (and
   (ht040-base-region-p region)
   (ht040-member-p (cadr region) point)))

(defun ht040-region-member-p (region point)
  (cond
   ((ht040-base-region-p region)
    (ht040-base-region-member-p region point))
   ((and
     (true-listp region)
     (equal (len region) 3)
     (equal (car region) :ht040-intersection)
     (ht040-base-region-p (cadr region))
     (ht040-base-region-p (caddr region)))
    (and
     (ht040-base-region-member-p
      (cadr region) point)
     (ht040-base-region-member-p
      (caddr region) point)))
   ((and
     (true-listp region)
     (equal (len region) 3)
     (equal (car region) :ht040-difference)
     (ht040-base-region-p (cadr region))
     (ht040-base-region-p (caddr region)))
    (and
     (ht040-base-region-member-p
      (cadr region) point)
     (not
      (ht040-base-region-member-p
       (caddr region) point))))
   (t nil)))

(defun-sk ht040-region-valid-p
    (real dimension region)
  (forall (point)
    (implies
     (ht040-region-member-p region point)
     (ht040-point-p real dimension point))))

;; Countable open-box covers and their nonnegative volume series define
;; Lebesgue outer volume by its lower Dedekind cut.

(defun ht040-valid-box-p
    (real dimension lower upper)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      (and (equal lower nil) (equal upper nil))
    (and
     (consp lower)
     (consp upper)
     (ht040-real-p real (car lower))
     (ht040-real-p real (car upper))
     (ht040-less real (car lower) (car upper))
     (ht040-valid-box-p
      real
      (- dimension 1)
      (cdr lower)
      (cdr upper)))))

(defun ht040-open-box-member-p
    (real dimension lower upper point)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      (equal point nil)
    (and
     (consp lower)
     (consp upper)
     (consp point)
     (ht040-less real (car lower) (car point))
     (ht040-less real (car point) (car upper))
     (ht040-open-box-member-p
      real
      (- dimension 1)
      (cdr lower)
      (cdr upper)
      (cdr point)))))

(defun-sk ht040-box-sequences-valid-p
    (real dimension lower-sequence upper-sequence)
  (forall (index)
    (implies
     (natp index)
     (ht040-valid-box-p
      real
      dimension
      (ht040-apply1 lower-sequence index)
      (ht040-apply1 upper-sequence index)))))

(defun-sk ht040-cover-index-exists-p
    (real dimension lower-sequence upper-sequence point)
  (exists (index)
    (and
     (natp index)
     (ht040-open-box-member-p
      real
      dimension
      (ht040-apply1 lower-sequence index)
      (ht040-apply1 upper-sequence index)
      point))))

(defun-sk ht040-box-sequences-cover-p
    (real dimension region lower-sequence upper-sequence)
  (forall (point)
    (implies
     (ht040-region-member-p region point)
     (ht040-cover-index-exists-p
      real
      dimension
      lower-sequence
      upper-sequence
      point))))

(defun ht040-countable-open-box-cover-p
    (real dimension region lower-sequence upper-sequence)
  (and
   (ht040-box-sequences-valid-p
    real dimension lower-sequence upper-sequence)
   (ht040-box-sequences-cover-p
    real dimension region lower-sequence upper-sequence)))

(defun ht040-box-volume
    (real dimension lower upper)
  (declare (xargs :measure (nfix dimension)))
  (if (zp dimension)
      (ht040-one real)
    (ht040-multiply
     real
     (ht040-subtract
      real (car upper) (car lower))
     (ht040-box-volume
      real
      (- dimension 1)
      (cdr lower)
      (cdr upper)))))

(defun ht040-box-volume-at
    (real dimension lower-sequence upper-sequence index)
  (ht040-box-volume
   real
   dimension
   (ht040-apply1 lower-sequence index)
   (ht040-apply1 upper-sequence index)))

(defun ht040-box-volume-partial-sum
    (real dimension lower-sequence upper-sequence count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (ht040-zero real)
    (let ((index (- count 1)))
      (ht040-add
       real
       (ht040-box-volume-partial-sum
        real
        dimension
        lower-sequence
        upper-sequence
        index)
       (ht040-box-volume-at
        real
        dimension
        lower-sequence
        upper-sequence
        index)))))

(defun-sk ht040-series-cutoff-exists-p
    (real dimension lower-sequence upper-sequence
          threshold epsilon)
  (exists (count)
    (and
     (natp count)
     (ht040-less
      real
      (ht040-subtract real threshold epsilon)
      (ht040-box-volume-partial-sum
       real
       dimension
       lower-sequence
       upper-sequence
       count)))))

(defun-sk ht040-nonnegative-series-ge-p
    (real dimension lower-sequence upper-sequence threshold)
  (forall (epsilon)
    (implies
     (ht040-positive-real-p real epsilon)
     (ht040-series-cutoff-exists-p
      real
      dimension
      lower-sequence
      upper-sequence
      threshold
      epsilon))))

(defun-sk ht040-lebesgue-outer-volume-ge-p
    (real dimension region threshold)
  (forall (lower-sequence upper-sequence)
    (implies
     (ht040-countable-open-box-cover-p
      real
      dimension
      region
      lower-sequence
      upper-sequence)
     (ht040-nonnegative-series-ge-p
      real
      dimension
      lower-sequence
      upper-sequence
      threshold))))

(defun-sk ht040-outer-volume-sum-ge-p
    (real dimension left right threshold)
  (exists (left-bound right-bound)
    (and
     (ht040-real-p real left-bound)
     (ht040-real-p real right-bound)
     (ht040-lebesgue-outer-volume-ge-p
      real dimension left left-bound)
     (ht040-lebesgue-outer-volume-ge-p
      real dimension right right-bound)
     (ht040-less-equal-p
      real
      threshold
      (ht040-add real left-bound right-bound)))))

;; Caratheodory measurability for the concrete outer volume above.

(defun-sk ht040-lebesgue-measurable-p
    (real dimension body)
  (forall (test-predicate threshold)
    (let ((test (ht040-base-region test-predicate)))
      (implies
       (and
        (ht040-real-p real threshold)
        (ht040-region-valid-p real dimension test))
       (iff
        (ht040-lebesgue-outer-volume-ge-p
         real dimension test threshold)
        (ht040-outer-volume-sum-ge-p
         real
         dimension
         (ht040-intersection-region test body)
         (ht040-difference-region test body)
         threshold))))))

(defun-sk ht040-lebesgue-volume-gt-p
    (real dimension region threshold)
  (exists (margin)
    (and
     (ht040-positive-real-p real margin)
     (ht040-lebesgue-outer-volume-ge-p
      real
      dimension
      region
      (ht040-add real threshold margin)))))

;; Convexity, central symmetry, and sequential compactness in R^n.

(defun ht040-affine-combination
    (real dimension parameter left right)
  (ht040-point-add
   real
   dimension
   (ht040-point-scale
    real
    dimension
    (ht040-subtract
     real (ht040-one real) parameter)
    left)
   (ht040-point-scale
    real dimension parameter right)))

(defun-sk ht040-convex-region-p
    (real dimension region)
  (forall (left right parameter)
    (implies
     (and
      (ht040-point-p real dimension left)
      (ht040-point-p real dimension right)
      (ht040-region-member-p region left)
      (ht040-region-member-p region right)
      (ht040-real-p real parameter)
      (ht040-less-equal-p
       real (ht040-zero real) parameter)
      (ht040-less-equal-p
       real parameter (ht040-one real)))
     (ht040-region-member-p
      region
      (ht040-affine-combination
       real dimension parameter left right)))))

(defun-sk ht040-origin-symmetric-p
    (real dimension region)
  (forall (point)
    (implies
     (and
      (ht040-point-p real dimension point)
      (ht040-region-member-p region point))
     (ht040-region-member-p
      region
      (ht040-point-negate
       real dimension point)))))

(defun-sk ht040-sequence-in-region-p
    (real dimension region sequence)
  (forall (index)
    (implies
     (natp index)
     (let ((point (ht040-apply1 sequence index)))
       (and
        (ht040-point-p real dimension point)
        (ht040-region-member-p region point))))))

(defun-sk ht040-index-sequence-natural-p
    (indices)
  (forall (index)
    (implies
     (natp index)
     (natp (ht040-apply1 indices index)))))

(defun-sk ht040-index-sequence-strict-p
    (indices)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (< left right))
     (<
      (ht040-apply1 indices left)
      (ht040-apply1 indices right)))))

(defun-sk ht040-convergence-cutoff-p
    (real dimension sequence indices limit epsilon cutoff)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= cutoff index))
     (ht040-point-close-p
      real
      dimension
      (ht040-apply1
       sequence
       (ht040-apply1 indices index))
      limit
      epsilon))))

(defun-sk ht040-convergence-cutoff-exists-p
    (real dimension sequence indices limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (ht040-convergence-cutoff-p
      real
      dimension
      sequence
      indices
      limit
      epsilon
      cutoff))))

(defun-sk ht040-subsequence-converges-p
    (real dimension sequence indices limit)
  (forall (epsilon)
    (implies
     (ht040-positive-real-p real epsilon)
     (ht040-convergence-cutoff-exists-p
      real
      dimension
      sequence
      indices
      limit
      epsilon))))

(defun-sk ht040-compact-witness-exists-p
    (real dimension region sequence)
  (exists (indices limit)
    (and
     (ht040-index-sequence-natural-p indices)
     (ht040-index-sequence-strict-p indices)
     (ht040-point-p real dimension limit)
     (ht040-region-member-p region limit)
     (ht040-subsequence-converges-p
      real dimension sequence indices limit))))

(defun-sk ht040-compact-region-p
    (real dimension region)
  (forall (sequence)
    (implies
     (ht040-sequence-in-region-p
      real dimension region sequence)
     (ht040-compact-witness-exists-p
      real dimension region sequence))))

;; Lattice-point witnesses.

(defun-sk ht040-blichfeldt-witness-p
    (real dimension region)
  (exists (left right)
    (and
     (ht040-point-p real dimension left)
     (ht040-point-p real dimension right)
     (ht040-region-member-p region left)
     (ht040-region-member-p region right)
     (not (equal left right))
     (ht040-integer-point-p
      real
      dimension
      (ht040-point-subtract
       real dimension left right)))))

(defun-sk ht040-minkowski-witness-p
    (real dimension region)
  (exists (point)
    (and
     (ht040-point-p real dimension point)
     (ht040-region-member-p region point)
     (not
      (equal
       point
       (ht040-zero-point real dimension)))
     (ht040-integer-point-p
      real dimension point))))

(defun-sk
    hundred-theorems-040-blichfeldt-principle-statement ()
  (forall (real dimension body-predicate)
    (let ((body (ht040-base-region body-predicate)))
      (implies
       (and
        (ht040-real-field-p real)
        (posp dimension)
        (ht040-region-valid-p
         real dimension body)
        (ht040-lebesgue-measurable-p
         real dimension body)
        (ht040-lebesgue-volume-gt-p
         real
         dimension
         body
         (ht040-one real)))
       (ht040-blichfeldt-witness-p
        real dimension body)))))

(defun-sk
    hundred-theorems-040-minkowski-fundamental-theorem-statement ()
  (forall (real dimension body-predicate)
    (let ((body (ht040-base-region body-predicate)))
      (implies
       (and
        (ht040-real-field-p real)
        (posp dimension)
        (ht040-region-valid-p
         real dimension body)
        (ht040-convex-region-p
         real dimension body)
        (ht040-origin-symmetric-p
         real dimension body)
        (ht040-lebesgue-measurable-p
         real dimension body)
        (ht040-lebesgue-volume-gt-p
         real
         dimension
         body
         (ht040-two-power real dimension)))
       (ht040-minkowski-witness-p
        real dimension body)))))

(defun-sk
    hundred-theorems-040-minkowski-compact-statement ()
  (forall (real dimension body-predicate)
    (let ((body (ht040-base-region body-predicate)))
      (implies
       (and
        (ht040-real-field-p real)
        (posp dimension)
        (ht040-region-valid-p
         real dimension body)
        (ht040-convex-region-p
         real dimension body)
        (ht040-compact-region-p
         real dimension body)
        (ht040-origin-symmetric-p
         real dimension body)
        (ht040-lebesgue-outer-volume-ge-p
         real
         dimension
         body
         (ht040-two-power real dimension)))
       (ht040-minkowski-witness-p
        real dimension body)))))

(value-triple :itpeval-statement-checked)
:q
