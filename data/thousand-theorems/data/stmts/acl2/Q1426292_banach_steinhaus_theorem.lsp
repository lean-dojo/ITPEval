;; Statement-only formalization of thousand-theorems corpus artifact Q1426292,
;; "Banach–Steinhaus theorem": a pointwise bounded family of continuous
;; semilinear maps from a complete seminormed space is uniformly bounded in
;; operator norm. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces present arbitrary carriers, operations, subsets,
;; sequences, and map families. Every algebraic, norm, completeness, typing,
;; continuity, and semilinearity law used by the source statement is explicit
;; in the predicates below.

(defstub q1426292-member-p (carrier-tag value) t)
(defstub q1426292-zero (carrier-tag) t)
(defstub q1426292-one (carrier-tag) t)
(defstub q1426292-add (carrier-tag left right) t)
(defstub q1426292-multiply (carrier-tag left right) t)
(defstub q1426292-negate (carrier-tag value) t)
(defstub q1426292-inverse (carrier-tag value) t)
(defstub q1426292-less (real-type left right) t)
(defstub q1426292-norm (real-type carrier-tag value) t)
(defstub q1426292-smul
  (scalar-type vector-type scalar vector)
  t)
(defstub q1426292-ring-hom
  (source-field target-field hom-tag scalar)
  t)
(defstub q1426292-set-member-p (set-tag value) t)
(defstub q1426292-sequence-value
  (vector-type sequence-tag index)
  t)
(defstub q1426292-family-value
  (index-type domain-type codomain-type family-tag index vector)
  t)

(defun q1426292-leq (real-type left right)
  (not (q1426292-less real-type right left)))

(defun q1426292-subtract (carrier-tag left right)
  (q1426292-add
   carrier-tag
   left
   (q1426292-negate carrier-tag right)))

(defun-sk q1426292-field-laws-p (field-type)
  (forall (x y z)
    (implies
     (and
      (q1426292-member-p field-type x)
      (q1426292-member-p field-type y)
      (q1426292-member-p field-type z))
     (let ((zero (q1426292-zero field-type))
           (one (q1426292-one field-type)))
       (and
        (q1426292-member-p
         field-type (q1426292-add field-type x y))
        (q1426292-member-p
         field-type (q1426292-multiply field-type x y))
        (q1426292-member-p
         field-type (q1426292-negate field-type x))
        (q1426292-member-p
         field-type (q1426292-inverse field-type x))
        (equal
         (q1426292-add
          field-type (q1426292-add field-type x y) z)
         (q1426292-add
          field-type x (q1426292-add field-type y z)))
        (equal
         (q1426292-add field-type x y)
         (q1426292-add field-type y x))
        (equal (q1426292-add field-type x zero) x)
        (equal
         (q1426292-add
          field-type x (q1426292-negate field-type x))
         zero)
        (equal
         (q1426292-multiply
          field-type (q1426292-multiply field-type x y) z)
         (q1426292-multiply
          field-type x (q1426292-multiply field-type y z)))
        (equal
         (q1426292-multiply field-type x y)
         (q1426292-multiply field-type y x))
        (equal (q1426292-multiply field-type x one) x)
        (equal
         (q1426292-inverse field-type zero)
         zero)
        (implies
         (not (equal x zero))
         (equal
          (q1426292-multiply
           field-type x (q1426292-inverse field-type x))
          one))
        (equal
         (q1426292-multiply
          field-type x (q1426292-add field-type y z))
         (q1426292-add
          field-type
          (q1426292-multiply field-type x y)
          (q1426292-multiply field-type x z))))))))

(defun q1426292-field-p (field-type)
  (and
   (q1426292-member-p
    field-type (q1426292-zero field-type))
   (q1426292-member-p
    field-type (q1426292-one field-type))
   (not
    (equal
     (q1426292-zero field-type)
     (q1426292-one field-type)))
   (q1426292-field-laws-p field-type)))

(defun-sk q1426292-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (q1426292-member-p real-type x)
      (q1426292-member-p real-type y)
      (q1426292-member-p real-type z))
     (let ((zero (q1426292-zero real-type)))
       (and
        (not (q1426292-less real-type x x))
        (or
         (equal x y)
         (q1426292-less real-type x y)
         (q1426292-less real-type y x))
        (implies
         (and
          (q1426292-less real-type x y)
          (q1426292-less real-type y z))
         (q1426292-less real-type x z))
        (implies
         (q1426292-less real-type x y)
         (q1426292-less
          real-type
          (q1426292-add real-type x z)
          (q1426292-add real-type y z)))
        (implies
         (and
          (q1426292-less real-type zero x)
          (q1426292-less real-type zero y))
         (q1426292-less
          real-type
          zero
          (q1426292-multiply real-type x y))))))))

(defun-sk q1426292-set-nonempty-p (real-type set-tag)
  (exists (x)
    (and
     (q1426292-member-p real-type x)
     (q1426292-set-member-p set-tag x))))

(defun-sk q1426292-upper-bound-p
    (real-type set-tag bound)
  (forall (x)
    (implies
     (and
      (q1426292-member-p real-type x)
      (q1426292-set-member-p set-tag x))
     (q1426292-leq real-type x bound))))

(defun-sk q1426292-bounded-above-p
    (real-type set-tag)
  (exists (bound)
    (and
     (q1426292-member-p real-type bound)
     (q1426292-upper-bound-p
      real-type set-tag bound))))

(defun-sk q1426292-supremum-p
    (real-type set-tag supremum)
  (forall (bound)
    (and
     (q1426292-member-p real-type supremum)
     (q1426292-upper-bound-p
      real-type set-tag supremum)
     (implies
      (and
       (q1426292-member-p real-type bound)
       (q1426292-upper-bound-p
        real-type set-tag bound))
      (q1426292-leq real-type supremum bound)))))

(defun-sk q1426292-supremum-exists-p
    (real-type set-tag)
  (exists (supremum)
    (q1426292-supremum-p
     real-type set-tag supremum)))

(defun-sk q1426292-dedekind-complete-p (real-type)
  (forall (set-tag)
    (implies
     (and
      (q1426292-set-nonempty-p real-type set-tag)
      (q1426292-bounded-above-p real-type set-tag))
     (q1426292-supremum-exists-p
      real-type set-tag))))

(defun q1426292-real-field-p (real-type)
  (and
   (q1426292-field-p real-type)
   (q1426292-order-laws-p real-type)
   (q1426292-less
    real-type
    (q1426292-zero real-type)
    (q1426292-one real-type))
   (q1426292-dedekind-complete-p real-type)))

(defun-sk q1426292-field-norm-laws-p
    (real-type field-type)
  (forall (x y)
    (implies
     (and
      (q1426292-member-p field-type x)
      (q1426292-member-p field-type y))
     (let ((real-zero (q1426292-zero real-type))
           (real-one (q1426292-one real-type))
           (field-zero (q1426292-zero field-type))
           (norm-x (q1426292-norm real-type field-type x))
           (norm-y (q1426292-norm real-type field-type y)))
       (and
        (q1426292-member-p real-type norm-x)
        (q1426292-member-p real-type norm-y)
        (q1426292-leq real-type real-zero norm-x)
        (iff
         (equal norm-x real-zero)
         (equal x field-zero))
        (equal
         (q1426292-norm
          real-type field-type
          (q1426292-negate field-type x))
         norm-x)
        (q1426292-leq
         real-type
         (q1426292-norm
          real-type field-type
          (q1426292-add field-type x y))
         (q1426292-add real-type norm-x norm-y))
        (equal
         (q1426292-norm
          real-type field-type
          (q1426292-multiply field-type x y))
         (q1426292-multiply real-type norm-x norm-y))
        (equal
         (q1426292-norm
          real-type field-type
          (q1426292-zero field-type))
         real-zero)
        (equal
         (q1426292-norm
          real-type field-type
          (q1426292-one field-type))
         real-one))))))

(defun-sk q1426292-large-norm-scalar-exists-p
    (real-type field-type)
  (exists (x)
    (and
     (q1426292-member-p field-type x)
     (q1426292-less
      real-type
      (q1426292-one real-type)
      (q1426292-norm real-type field-type x)))))

(defun q1426292-nontrivially-normed-field-p
    (real-type field-type)
  (and
   (q1426292-field-p field-type)
   (q1426292-field-norm-laws-p
    real-type field-type)
   (q1426292-large-norm-scalar-exists-p
    real-type field-type)))

(defun-sk q1426292-ring-hom-isometric-laws-p
    (real-type source-field target-field hom-tag)
  (forall (x y)
    (implies
     (and
      (q1426292-member-p source-field x)
      (q1426292-member-p source-field y))
     (let ((hom-x
            (q1426292-ring-hom
             source-field target-field hom-tag x)))
       (and
        (q1426292-member-p target-field hom-x)
        (equal
         (q1426292-ring-hom
          source-field target-field hom-tag
          (q1426292-zero source-field))
         (q1426292-zero target-field))
        (equal
         (q1426292-ring-hom
          source-field target-field hom-tag
          (q1426292-one source-field))
         (q1426292-one target-field))
        (equal
         (q1426292-ring-hom
          source-field target-field hom-tag
          (q1426292-add source-field x y))
         (q1426292-add
          target-field
          hom-x
          (q1426292-ring-hom
           source-field target-field hom-tag y)))
        (equal
         (q1426292-ring-hom
          source-field target-field hom-tag
          (q1426292-multiply source-field x y))
         (q1426292-multiply
          target-field
          hom-x
          (q1426292-ring-hom
           source-field target-field hom-tag y)))
        (equal
         (q1426292-norm
          real-type target-field hom-x)
         (q1426292-norm real-type source-field x)))))))

(defun-sk q1426292-ring-hom-injective-p
    (source-field target-field hom-tag)
  (forall (x y)
    (implies
     (and
      (q1426292-member-p source-field x)
      (q1426292-member-p source-field y)
      (equal
       (q1426292-ring-hom
        source-field target-field hom-tag x)
       (q1426292-ring-hom
        source-field target-field hom-tag y)))
     (equal x y))))

(defun q1426292-ring-hom-isometric-p
    (real-type source-field target-field hom-tag)
  (and
   (q1426292-ring-hom-isometric-laws-p
    real-type source-field target-field hom-tag)
   (q1426292-ring-hom-injective-p
    source-field target-field hom-tag)))

(defun-sk q1426292-add-comm-group-laws-p
    (vector-type)
  (forall (x y z)
    (implies
     (and
      (q1426292-member-p vector-type x)
      (q1426292-member-p vector-type y)
      (q1426292-member-p vector-type z))
     (let ((zero (q1426292-zero vector-type)))
       (and
        (q1426292-member-p
         vector-type (q1426292-add vector-type x y))
        (q1426292-member-p
         vector-type (q1426292-negate vector-type x))
        (equal
         (q1426292-add
          vector-type (q1426292-add vector-type x y) z)
         (q1426292-add
          vector-type x (q1426292-add vector-type y z)))
        (equal
         (q1426292-add vector-type x y)
         (q1426292-add vector-type y x))
        (equal (q1426292-add vector-type x zero) x)
        (equal
         (q1426292-add
          vector-type x (q1426292-negate vector-type x))
         zero))))))

(defun-sk q1426292-seminorm-laws-p
    (real-type vector-type)
  (forall (x y)
    (implies
     (and
      (q1426292-member-p vector-type x)
      (q1426292-member-p vector-type y))
     (let ((real-zero (q1426292-zero real-type))
           (norm-x (q1426292-norm real-type vector-type x))
           (norm-y (q1426292-norm real-type vector-type y)))
       (and
        (q1426292-member-p real-type norm-x)
        (q1426292-member-p real-type norm-y)
        (q1426292-leq real-type real-zero norm-x)
        (equal
         (q1426292-norm
          real-type vector-type
          (q1426292-zero vector-type))
         real-zero)
        (equal
         (q1426292-norm
          real-type vector-type
          (q1426292-negate vector-type x))
         norm-x)
        (q1426292-leq
         real-type
         (q1426292-norm
          real-type vector-type
          (q1426292-add vector-type x y))
         (q1426292-add real-type norm-x norm-y)))))))

(defun q1426292-seminormed-add-comm-group-p
    (real-type vector-type)
  (and
   (q1426292-member-p
    vector-type (q1426292-zero vector-type))
   (q1426292-add-comm-group-laws-p vector-type)
   (q1426292-seminorm-laws-p
    real-type vector-type)))

(defun-sk q1426292-normed-space-laws-p
    (real-type scalar-type vector-type)
  (forall (a b x y)
    (implies
     (and
      (q1426292-member-p scalar-type a)
      (q1426292-member-p scalar-type b)
      (q1426292-member-p vector-type x)
      (q1426292-member-p vector-type y))
     (and
      (q1426292-member-p
       vector-type
       (q1426292-smul scalar-type vector-type a x))
      (equal
       (q1426292-smul
        scalar-type vector-type
        (q1426292-one scalar-type) x)
       x)
      (equal
       (q1426292-smul
        scalar-type vector-type
        (q1426292-multiply scalar-type a b) x)
       (q1426292-smul
        scalar-type vector-type a
        (q1426292-smul scalar-type vector-type b x)))
      (equal
       (q1426292-smul
        scalar-type vector-type
        (q1426292-add scalar-type a b) x)
       (q1426292-add
        vector-type
        (q1426292-smul scalar-type vector-type a x)
        (q1426292-smul scalar-type vector-type b x)))
      (equal
       (q1426292-smul
        scalar-type vector-type a
        (q1426292-add vector-type x y))
       (q1426292-add
        vector-type
        (q1426292-smul scalar-type vector-type a x)
        (q1426292-smul scalar-type vector-type a y)))
      (equal
       (q1426292-smul
        scalar-type vector-type
        (q1426292-zero scalar-type) x)
       (q1426292-zero vector-type))
      (equal
       (q1426292-smul
        scalar-type vector-type a
        (q1426292-zero vector-type))
       (q1426292-zero vector-type))
      (equal
       (q1426292-norm
        real-type vector-type
        (q1426292-smul scalar-type vector-type a x))
       (q1426292-multiply
        real-type
        (q1426292-norm real-type scalar-type a)
        (q1426292-norm real-type vector-type x)))))))

(defun q1426292-normed-space-p
    (real-type scalar-type vector-type)
  (q1426292-normed-space-laws-p
   real-type scalar-type vector-type))

(defun q1426292-distance
    (real-type vector-type x y)
  (q1426292-norm
   real-type
   vector-type
   (q1426292-subtract vector-type x y)))

(defun-sk q1426292-sequence-typed-p
    (vector-type sequence-tag)
  (forall (n)
    (implies
     (natp n)
     (q1426292-member-p
      vector-type
      (q1426292-sequence-value
       vector-type sequence-tag n)))))

(defun-sk q1426292-cauchy-tail-p
    (real-type vector-type sequence-tag epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (q1426292-less
      real-type
      (q1426292-distance
       real-type
       vector-type
       (q1426292-sequence-value
        vector-type sequence-tag m)
       (q1426292-sequence-value
        vector-type sequence-tag n))
      epsilon))))

(defun-sk q1426292-cauchy-cutoff-exists-p
    (real-type vector-type sequence-tag epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1426292-cauchy-tail-p
      real-type vector-type sequence-tag
      epsilon cutoff))))

(defun-sk q1426292-cauchy-p
    (real-type vector-type sequence-tag)
  (forall (epsilon)
    (implies
     (and
      (q1426292-member-p real-type epsilon)
      (q1426292-less
       real-type
       (q1426292-zero real-type)
       epsilon))
     (q1426292-cauchy-cutoff-exists-p
      real-type vector-type sequence-tag epsilon))))

(defun-sk q1426292-convergence-tail-p
    (real-type vector-type sequence-tag limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q1426292-less
      real-type
      (q1426292-distance
       real-type
       vector-type
       (q1426292-sequence-value
        vector-type sequence-tag n)
       limit)
      epsilon))))

(defun-sk q1426292-convergence-cutoff-exists-p
    (real-type vector-type sequence-tag limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q1426292-convergence-tail-p
      real-type vector-type sequence-tag
      limit epsilon cutoff))))

(defun-sk q1426292-converges-p
    (real-type vector-type sequence-tag limit)
  (forall (epsilon)
    (implies
     (and
      (q1426292-member-p real-type epsilon)
      (q1426292-less
       real-type
       (q1426292-zero real-type)
       epsilon))
     (q1426292-convergence-cutoff-exists-p
      real-type vector-type sequence-tag
      limit epsilon))))

(defun-sk q1426292-limit-exists-p
    (real-type vector-type sequence-tag)
  (exists (limit)
    (and
     (q1426292-member-p vector-type limit)
     (q1426292-converges-p
      real-type vector-type sequence-tag limit))))

(defun-sk q1426292-complete-space-p
    (real-type vector-type)
  (forall (sequence-tag)
    (implies
     (and
      (q1426292-sequence-typed-p
       vector-type sequence-tag)
      (q1426292-cauchy-p
       real-type vector-type sequence-tag))
     (q1426292-limit-exists-p
      real-type vector-type sequence-tag))))

(defun-sk q1426292-semilinear-family-laws-p
    (source-field target-field hom-tag
     index-type domain-type codomain-type family-tag)
  (forall (i a x y)
    (and
     (implies
      (and
       (q1426292-member-p index-type i)
       (q1426292-member-p domain-type x))
      (q1426292-member-p
       codomain-type
       (q1426292-family-value
        index-type domain-type codomain-type
        family-tag i x)))
     (implies
      (and
       (q1426292-member-p index-type i)
       (q1426292-member-p domain-type x)
       (q1426292-member-p domain-type y))
      (equal
       (q1426292-family-value
        index-type domain-type codomain-type
        family-tag i
        (q1426292-add domain-type x y))
       (q1426292-add
        codomain-type
        (q1426292-family-value
         index-type domain-type codomain-type
         family-tag i x)
        (q1426292-family-value
         index-type domain-type codomain-type
         family-tag i y))))
     (implies
      (and
       (q1426292-member-p index-type i)
       (q1426292-member-p source-field a)
       (q1426292-member-p domain-type x))
      (equal
       (q1426292-family-value
        index-type domain-type codomain-type
        family-tag i
        (q1426292-smul
         source-field domain-type a x))
       (q1426292-smul
        target-field codomain-type
        (q1426292-ring-hom
         source-field target-field hom-tag a)
        (q1426292-family-value
         index-type domain-type codomain-type
         family-tag i x)))))))

(defun-sk q1426292-map-action-bound-p
    (real-type index-type domain-type codomain-type
     family-tag i bound)
  (forall (x)
    (implies
     (q1426292-member-p domain-type x)
     (q1426292-leq
      real-type
      (q1426292-norm
       real-type
       codomain-type
       (q1426292-family-value
        index-type domain-type codomain-type
        family-tag i x))
      (q1426292-multiply
       real-type
       bound
       (q1426292-norm
        real-type domain-type x))))))

(defun-sk q1426292-map-bound-exists-p
    (real-type index-type domain-type codomain-type
     family-tag i)
  (exists (bound)
    (and
     (q1426292-member-p real-type bound)
     (q1426292-leq
      real-type (q1426292-zero real-type) bound)
     (q1426292-map-action-bound-p
      real-type index-type domain-type codomain-type
      family-tag i bound))))

(defun-sk q1426292-family-continuous-p
    (real-type index-type domain-type codomain-type
     family-tag)
  (forall (i)
    (implies
     (q1426292-member-p index-type i)
     (q1426292-map-bound-exists-p
      real-type index-type domain-type codomain-type
      family-tag i))))

(defun q1426292-continuous-semilinear-family-p
    (real-type source-field target-field hom-tag
     index-type domain-type codomain-type family-tag)
  (and
   (q1426292-semilinear-family-laws-p
    source-field target-field hom-tag
    index-type domain-type codomain-type family-tag)
   (q1426292-family-continuous-p
    real-type index-type domain-type codomain-type
    family-tag)))

(defun-sk q1426292-pointwise-bound-p
    (real-type index-type domain-type codomain-type
     family-tag x bound)
  (forall (i)
    (implies
     (q1426292-member-p index-type i)
     (q1426292-leq
      real-type
      (q1426292-norm
       real-type
       codomain-type
       (q1426292-family-value
        index-type domain-type codomain-type
        family-tag i x))
      bound))))

(defun-sk q1426292-pointwise-bound-exists-p
    (real-type index-type domain-type codomain-type
     family-tag x)
  (exists (bound)
    (and
     (q1426292-member-p real-type bound)
     (q1426292-pointwise-bound-p
      real-type index-type domain-type codomain-type
      family-tag x bound))))

(defun-sk q1426292-pointwise-bounded-p
    (real-type index-type domain-type codomain-type
     family-tag)
  (forall (x)
    (implies
     (q1426292-member-p domain-type x)
     (q1426292-pointwise-bound-exists-p
      real-type index-type domain-type codomain-type
      family-tag x))))

;; For continuous semilinear maps, the following action inequality is
;; equivalent to bounding each operator norm by the same nonnegative scalar.
(defun-sk q1426292-uniform-action-bound-p
    (real-type index-type domain-type codomain-type
     family-tag bound)
  (forall (i x)
    (implies
     (and
      (q1426292-member-p index-type i)
      (q1426292-member-p domain-type x))
     (q1426292-leq
      real-type
      (q1426292-norm
       real-type
       codomain-type
       (q1426292-family-value
        index-type domain-type codomain-type
        family-tag i x))
      (q1426292-multiply
       real-type
       bound
       (q1426292-norm
        real-type domain-type x))))))

(defun-sk q1426292-uniform-bound-exists-p
    (real-type index-type domain-type codomain-type
     family-tag)
  (exists (bound)
    (and
     (q1426292-member-p real-type bound)
     (q1426292-leq
      real-type (q1426292-zero real-type) bound)
     (q1426292-uniform-action-bound-p
      real-type index-type domain-type codomain-type
      family-tag bound))))

(defun-sk thousand-theorems-q1426292-banach-steinhaus-statement ()
  (forall
    (real-type source-field target-field
     domain-type codomain-type index-type
     hom-tag family-tag)
    (implies
     (and
      (q1426292-real-field-p real-type)
      (q1426292-nontrivially-normed-field-p
       real-type source-field)
      (q1426292-nontrivially-normed-field-p
       real-type target-field)
      (q1426292-ring-hom-isometric-p
       real-type source-field target-field hom-tag)
      (q1426292-seminormed-add-comm-group-p
       real-type domain-type)
      (q1426292-seminormed-add-comm-group-p
       real-type codomain-type)
      (q1426292-normed-space-p
       real-type source-field domain-type)
      (q1426292-normed-space-p
       real-type target-field codomain-type)
      (q1426292-complete-space-p
       real-type domain-type)
      (q1426292-continuous-semilinear-family-p
       real-type source-field target-field hom-tag
       index-type domain-type codomain-type family-tag)
      (q1426292-pointwise-bounded-p
       real-type index-type domain-type codomain-type
       family-tag))
     (q1426292-uniform-bound-exists-p
      real-type index-type domain-type codomain-type
      family-tag))))

(value-triple :itpeval-statement-checked)
:q
