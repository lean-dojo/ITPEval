;; Statement-only formalization of thousand-theorems corpus artifact Q944297,
;; "Open mapping theorem (functional analysis)": every surjective continuous
;; semilinear map between Banach spaces over isometrically isomorphic
;; nontrivially normed fields is an open map. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers and their operations are presented conservatively.
;; Norms are rounded rational upper cuts: NORM-LT-P(type,x,q) means ||x|| < q.
;; These cuts represent arbitrary finite nonnegative real norms, including
;; irrational values, rather than rational-valued approximations.
;;
;; Sequences, the two field homomorphisms, and the semilinear map are directly
;; quantified tame APPLY$ function objects. No opaque set, sequence, or map
;; tags occur. The conclusion uses the local ball-image characterization of an
;; open map. Positive rational radii form a basis for every norm topology, so
;; this characterization is bidirectionally equivalent to IsOpenMap.

(defstub q944297-member-p (carrier-type value) t)
(defstub q944297-zero (carrier-type) t)
(defstub q944297-one (carrier-type) t)
(defstub q944297-add (carrier-type left right) t)
(defstub q944297-multiply (carrier-type left right) t)
(defstub q944297-negate (carrier-type value) t)
(defstub q944297-inverse (carrier-type value) t)
(defstub q944297-smul
  (field-type vector-type scalar vector)
  t)
(defstub q944297-norm-lt-p
  (carrier-type value rational-bound)
  t)

(defun q944297-function-value (function argument)
  (apply$ function (list argument)))

(defun q944297-sequence-value (sequence index)
  (apply$ sequence (list index)))

(defun q944297-positive-rational-p (q)
  (and (rationalp q) (< 0 q)))

(defun q944297-subtract (carrier-type left right)
  (q944297-add
   carrier-type
   left
   (q944297-negate carrier-type right)))

(defun q944297-norm-difference-lt-p
    (carrier-type left right epsilon)
  (q944297-norm-lt-p
   carrier-type
   (q944297-subtract carrier-type left right)
   epsilon))

;; Rounded upper cuts for genuine finite nonnegative real norms.

(defun-sk q944297-norm-finite-p
    (carrier-type value)
  (exists (q)
    (and
     (q944297-positive-rational-p q)
     (q944297-norm-lt-p carrier-type value q))))

(defun-sk q944297-norm-positive-p
    (carrier-type value)
  (exists (q)
    (and
     (q944297-positive-rational-p q)
     (not
      (q944297-norm-lt-p carrier-type value q)))))

(defun-sk q944297-norm-rounded-p
    (carrier-type value q)
  (exists (r)
    (and
     (q944297-positive-rational-p r)
     (rationalp q)
     (< r q)
     (q944297-norm-lt-p carrier-type value r))))

(defun-sk q944297-norm-cut-laws-p
    (carrier-type)
  (forall (x q r)
    (implies
     (q944297-member-p carrier-type x)
     (and
      (implies
       (q944297-norm-lt-p carrier-type x q)
       (q944297-positive-rational-p q))
      (implies
       (and
        (q944297-norm-lt-p carrier-type x q)
        (rationalp r)
        (< q r))
       (q944297-norm-lt-p carrier-type x r))
      (implies
       (q944297-norm-lt-p carrier-type x q)
       (q944297-norm-rounded-p carrier-type x q))
      (q944297-norm-finite-p carrier-type x)
      (implies
       (equal x (q944297-zero carrier-type))
       (iff
        (q944297-norm-lt-p carrier-type x q)
        (q944297-positive-rational-p q)))
      (implies
       (not (equal x (q944297-zero carrier-type)))
       (q944297-norm-positive-p carrier-type x))))))

;; Normed additive commutative groups.

(defun-sk q944297-normed-add-comm-group-laws-p
    (carrier-type)
  (forall (x y z q r)
    (implies
     (and
      (q944297-member-p carrier-type x)
      (q944297-member-p carrier-type y)
      (q944297-member-p carrier-type z))
     (and
      (q944297-member-p
       carrier-type
       (q944297-add carrier-type x y))
      (q944297-member-p
       carrier-type
       (q944297-negate carrier-type x))
      (equal
       (q944297-add
        carrier-type
        (q944297-add carrier-type x y)
        z)
       (q944297-add
        carrier-type
        x
        (q944297-add carrier-type y z)))
      (equal
       (q944297-add carrier-type x y)
       (q944297-add carrier-type y x))
      (equal
       (q944297-add
        carrier-type x (q944297-zero carrier-type))
       x)
      (equal
       (q944297-add
        carrier-type x (q944297-negate carrier-type x))
       (q944297-zero carrier-type))
      (iff
       (q944297-norm-lt-p
        carrier-type
        (q944297-negate carrier-type x)
        q)
       (q944297-norm-lt-p carrier-type x q))
      (implies
       (and
        (q944297-positive-rational-p q)
        (q944297-positive-rational-p r)
        (q944297-norm-lt-p carrier-type x q)
        (q944297-norm-lt-p carrier-type y r))
       (q944297-norm-lt-p
        carrier-type
        (q944297-add carrier-type x y)
        (+ q r)))))))

(defun q944297-normed-add-comm-group-p
    (carrier-type)
  (and
   (q944297-member-p
    carrier-type (q944297-zero carrier-type))
   (q944297-norm-cut-laws-p carrier-type)
   (q944297-normed-add-comm-group-laws-p carrier-type)))

;; Nontrivially normed fields.

(defun-sk q944297-product-norm-lt-p
    (field-type x y q)
  (exists (r s)
    (and
     (q944297-positive-rational-p q)
     (q944297-positive-rational-p r)
     (q944297-positive-rational-p s)
     (q944297-norm-lt-p field-type x r)
     (q944297-norm-lt-p field-type y s)
     (< (* r s) q))))

(defun-sk q944297-field-laws-p
    (field-type)
  (forall (x y z)
    (implies
     (and
      (q944297-member-p field-type x)
      (q944297-member-p field-type y)
      (q944297-member-p field-type z))
     (and
      (q944297-member-p
       field-type (q944297-multiply field-type x y))
      (q944297-member-p
       field-type (q944297-inverse field-type x))
      (equal
       (q944297-multiply
        field-type
        (q944297-multiply field-type x y)
        z)
       (q944297-multiply
        field-type
        x
        (q944297-multiply field-type y z)))
      (equal
       (q944297-multiply field-type x y)
       (q944297-multiply field-type y x))
      (equal
       (q944297-multiply
        field-type x (q944297-one field-type))
       x)
      (equal
       (q944297-inverse
        field-type (q944297-zero field-type))
       (q944297-zero field-type))
      (implies
       (not (equal x (q944297-zero field-type)))
       (equal
        (q944297-multiply
         field-type
         x
         (q944297-inverse field-type x))
        (q944297-one field-type)))
      (equal
       (q944297-multiply
        field-type
        x
        (q944297-add field-type y z))
       (q944297-add
        field-type
        (q944297-multiply field-type x y)
        (q944297-multiply field-type x z)))))))

(defun-sk q944297-field-norm-laws-p
    (field-type)
  (forall (x y q)
    (implies
     (and
      (q944297-member-p field-type x)
      (q944297-member-p field-type y))
     (iff
      (q944297-norm-lt-p
       field-type
       (q944297-multiply field-type x y)
       q)
      (q944297-product-norm-lt-p
       field-type x y q)))))

(defun-sk q944297-large-norm-element-exists-p
    (field-type)
  (exists (x q)
    (and
     (q944297-member-p field-type x)
     (rationalp q)
     (< 1 q)
     (not (q944297-norm-lt-p field-type x q)))))

(defun q944297-nontrivially-normed-field-p
    (field-type)
  (and
   (q944297-normed-add-comm-group-p field-type)
   (q944297-member-p
    field-type (q944297-one field-type))
   (not
    (equal
     (q944297-zero field-type)
     (q944297-one field-type)))
   (q944297-field-laws-p field-type)
   (q944297-field-norm-laws-p field-type)
   (q944297-large-norm-element-exists-p field-type)))

;; Normed vector spaces.

(defun-sk q944297-scaled-norm-lt-p
    (field-type vector-type scalar vector q)
  (exists (r s)
    (and
     (q944297-positive-rational-p q)
     (q944297-positive-rational-p r)
     (q944297-positive-rational-p s)
     (q944297-norm-lt-p field-type scalar r)
     (q944297-norm-lt-p vector-type vector s)
     (< (* r s) q))))

(defun-sk q944297-normed-space-laws-p
    (field-type vector-type)
  (forall (a b x y q)
    (implies
     (and
      (q944297-member-p field-type a)
      (q944297-member-p field-type b)
      (q944297-member-p vector-type x)
      (q944297-member-p vector-type y))
     (and
      (q944297-member-p
       vector-type
       (q944297-smul field-type vector-type a x))
      (equal
       (q944297-smul
        field-type vector-type (q944297-one field-type) x)
       x)
      (equal
       (q944297-smul
        field-type
        vector-type
        (q944297-multiply field-type a b)
        x)
       (q944297-smul
        field-type
        vector-type
        a
        (q944297-smul field-type vector-type b x)))
      (equal
       (q944297-smul
        field-type
        vector-type
        (q944297-add field-type a b)
        x)
       (q944297-add
        vector-type
        (q944297-smul field-type vector-type a x)
        (q944297-smul field-type vector-type b x)))
      (equal
       (q944297-smul
        field-type
        vector-type
        a
        (q944297-add vector-type x y))
       (q944297-add
        vector-type
        (q944297-smul field-type vector-type a x)
        (q944297-smul field-type vector-type a y)))
      (iff
       (q944297-norm-lt-p
        vector-type
        (q944297-smul field-type vector-type a x)
        q)
       (q944297-scaled-norm-lt-p
        field-type vector-type a x q))))))

(defun q944297-normed-space-p
    (field-type vector-type)
  (and
   (q944297-normed-add-comm-group-p vector-type)
   (q944297-normed-space-laws-p field-type vector-type)))

;; Completeness via directly quantified tame APPLY$ sequences.

(defun-sk q944297-sequence-range-p
    (carrier-type sequence)
  (forall (n)
    (implies
     (natp n)
     (q944297-member-p
      carrier-type
      (q944297-sequence-value sequence n)))))

(defun q944297-sequence-p
    (carrier-type sequence)
  (and
   (tamep-functionp sequence)
   (q944297-sequence-range-p carrier-type sequence)))

(defun-sk q944297-cauchy-tail-p
    (carrier-type sequence epsilon n0)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp n0)
      (<= n0 m)
      (<= n0 n))
     (q944297-norm-difference-lt-p
      carrier-type
      (q944297-sequence-value sequence m)
      (q944297-sequence-value sequence n)
      epsilon))))

(defun-sk q944297-cauchy-epsilon-p
    (carrier-type sequence epsilon)
  (exists (n0)
    (and
     (natp n0)
     (q944297-cauchy-tail-p
      carrier-type sequence epsilon n0))))

(defun-sk q944297-cauchy-all-epsilon-p
    (carrier-type sequence)
  (forall (epsilon)
    (implies
     (q944297-positive-rational-p epsilon)
     (q944297-cauchy-epsilon-p
      carrier-type sequence epsilon))))

(defun q944297-cauchy-p
    (carrier-type sequence)
  (and
   (q944297-sequence-p carrier-type sequence)
   (q944297-cauchy-all-epsilon-p carrier-type sequence)))

(defun-sk q944297-convergence-tail-p
    (carrier-type sequence limit epsilon n0)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp n0)
      (<= n0 n))
     (q944297-norm-difference-lt-p
      carrier-type
      (q944297-sequence-value sequence n)
      limit
      epsilon))))

(defun-sk q944297-convergence-epsilon-p
    (carrier-type sequence limit epsilon)
  (exists (n0)
    (and
     (natp n0)
     (q944297-convergence-tail-p
      carrier-type sequence limit epsilon n0))))

(defun-sk q944297-convergence-all-epsilon-p
    (carrier-type sequence limit)
  (forall (epsilon)
    (implies
     (q944297-positive-rational-p epsilon)
     (q944297-convergence-epsilon-p
      carrier-type sequence limit epsilon))))

(defun q944297-converges-p
    (carrier-type sequence limit)
  (and
   (q944297-member-p carrier-type limit)
   (q944297-sequence-p carrier-type sequence)
   (q944297-convergence-all-epsilon-p
    carrier-type sequence limit)))

(defun-sk q944297-limit-exists-p
    (carrier-type sequence)
  (exists (limit)
    (q944297-converges-p
     carrier-type sequence limit)))

(defun-sk q944297-complete-space-p
    (carrier-type)
  (forall (sequence)
    (implies
     (q944297-cauchy-p carrier-type sequence)
     (q944297-limit-exists-p carrier-type sequence))))

(defun q944297-banach-space-p
    (field-type vector-type)
  (and
   (q944297-normed-space-p field-type vector-type)
   (q944297-complete-space-p vector-type)))

;; Isometric ring homomorphisms as directly quantified tame APPLY$ functions.

(defun-sk q944297-ring-homomorphism-laws-p
    (source-field target-field homomorphism)
  (forall (x y q)
    (implies
     (and
      (q944297-member-p source-field x)
      (q944297-member-p source-field y))
     (and
      (q944297-member-p
       target-field
       (q944297-function-value homomorphism x))
      (equal
       (q944297-function-value
        homomorphism (q944297-zero source-field))
       (q944297-zero target-field))
      (equal
       (q944297-function-value
        homomorphism (q944297-one source-field))
       (q944297-one target-field))
      (equal
       (q944297-function-value
        homomorphism
        (q944297-add source-field x y))
       (q944297-add
        target-field
        (q944297-function-value homomorphism x)
        (q944297-function-value homomorphism y)))
      (equal
       (q944297-function-value
        homomorphism
        (q944297-multiply source-field x y))
       (q944297-multiply
        target-field
        (q944297-function-value homomorphism x)
        (q944297-function-value homomorphism y)))
      (iff
       (q944297-norm-lt-p
        target-field
        (q944297-function-value homomorphism x)
        q)
       (q944297-norm-lt-p source-field x q))))))

(defun q944297-isometric-ring-homomorphism-p
    (source-field target-field homomorphism)
  (and
   (tamep-functionp homomorphism)
   (q944297-ring-homomorphism-laws-p
    source-field target-field homomorphism)))

(defun-sk q944297-ring-hom-inverse-pair-p
    (source-field target-field forward-hom inverse-hom)
  (forall (x y)
    (implies
     (and
      (q944297-member-p source-field x)
      (q944297-member-p target-field y))
     (and
      (equal
       (q944297-function-value
        inverse-hom
        (q944297-function-value forward-hom x))
       x)
      (equal
       (q944297-function-value
        forward-hom
        (q944297-function-value inverse-hom y))
       y)))))

(defun q944297-isometric-ring-isomorphism-p
    (source-field target-field forward-hom inverse-hom)
  (and
   (q944297-isometric-ring-homomorphism-p
    source-field target-field forward-hom)
   (q944297-isometric-ring-homomorphism-p
    target-field source-field inverse-hom)
   (q944297-ring-hom-inverse-pair-p
    source-field target-field forward-hom inverse-hom)))

;; Continuous semilinear maps as directly quantified tame APPLY$ functions.

(defun-sk q944297-semilinear-map-laws-p
    (source-field target-field
     domain-type codomain-type
     forward-hom mapping)
  (forall (a x y)
    (implies
     (and
      (q944297-member-p source-field a)
      (q944297-member-p domain-type x)
      (q944297-member-p domain-type y))
     (and
      (q944297-member-p
       codomain-type
       (q944297-function-value mapping x))
      (equal
       (q944297-function-value
        mapping (q944297-add domain-type x y))
       (q944297-add
        codomain-type
        (q944297-function-value mapping x)
        (q944297-function-value mapping y)))
      (equal
       (q944297-function-value
        mapping
        (q944297-smul source-field domain-type a x))
       (q944297-smul
        target-field
        codomain-type
        (q944297-function-value forward-hom a)
        (q944297-function-value mapping x)))))))

(defun-sk q944297-continuity-delta-p
    (domain-type codomain-type mapping
     center epsilon delta)
  (forall (point)
    (implies
     (and
      (q944297-member-p domain-type point)
      (q944297-norm-difference-lt-p
       domain-type point center delta))
     (q944297-norm-difference-lt-p
      codomain-type
      (q944297-function-value mapping point)
      (q944297-function-value mapping center)
      epsilon))))

(defun-sk q944297-continuity-delta-exists-p
    (domain-type codomain-type mapping center epsilon)
  (exists (delta)
    (and
     (q944297-positive-rational-p delta)
     (q944297-continuity-delta-p
      domain-type codomain-type mapping
      center epsilon delta))))

(defun-sk q944297-continuous-map-p
    (domain-type codomain-type mapping)
  (forall (center epsilon)
    (implies
     (and
      (q944297-member-p domain-type center)
      (q944297-positive-rational-p epsilon))
     (q944297-continuity-delta-exists-p
      domain-type codomain-type mapping
      center epsilon))))

(defun q944297-continuous-semilinear-map-p
    (source-field target-field
     domain-type codomain-type
     forward-hom mapping)
  (and
   (tamep-functionp mapping)
   (q944297-semilinear-map-laws-p
    source-field target-field
    domain-type codomain-type
    forward-hom mapping)
   (q944297-continuous-map-p
    domain-type codomain-type mapping)))

;; Surjectivity and the local ball-image form of openness.

(defun-sk q944297-preimage-exists-p
    (domain-type codomain-type mapping value)
  (exists (preimage)
    (and
     (q944297-member-p domain-type preimage)
     (equal
      (q944297-function-value mapping preimage)
      value))))

(defun-sk q944297-surjective-p
    (domain-type codomain-type mapping)
  (forall (value)
    (implies
     (q944297-member-p codomain-type value)
     (q944297-preimage-exists-p
      domain-type codomain-type mapping value))))

(defun-sk q944297-local-ball-preimage-exists-p
    (domain-type mapping center domain-radius value)
  (exists (preimage)
    (and
     (q944297-member-p domain-type preimage)
     (q944297-norm-difference-lt-p
      domain-type preimage center domain-radius)
     (equal
      (q944297-function-value mapping preimage)
      value))))

(defun-sk q944297-local-ball-image-covered-p
    (domain-type codomain-type mapping
     center domain-radius codomain-radius)
  (forall (value)
    (implies
     (and
      (q944297-member-p codomain-type value)
      (q944297-norm-difference-lt-p
       codomain-type
       value
       (q944297-function-value mapping center)
       codomain-radius))
     (q944297-local-ball-preimage-exists-p
      domain-type mapping center domain-radius value))))

(defun-sk q944297-local-image-radius-exists-p
    (domain-type codomain-type mapping
     center domain-radius)
  (exists (codomain-radius)
    (and
     (q944297-positive-rational-p codomain-radius)
     (q944297-local-ball-image-covered-p
      domain-type codomain-type mapping
      center domain-radius codomain-radius))))

(defun-sk q944297-open-map-p
    (domain-type codomain-type mapping)
  (forall (center domain-radius)
    (implies
     (and
      (q944297-member-p domain-type center)
      (q944297-positive-rational-p domain-radius))
     (q944297-local-image-radius-exists-p
      domain-type codomain-type mapping
      center domain-radius))))

(defun-sk
    thousand-theorems-q944297-open-mapping-theorem-functional-analysis-statement
    ()
  (forall
    (source-field target-field
     domain-type codomain-type
     forward-hom inverse-hom mapping)
    (implies
     (and
      (q944297-nontrivially-normed-field-p source-field)
      (q944297-nontrivially-normed-field-p target-field)
      (q944297-isometric-ring-isomorphism-p
       source-field target-field forward-hom inverse-hom)
      (q944297-banach-space-p source-field domain-type)
      (q944297-banach-space-p target-field codomain-type)
      (q944297-continuous-semilinear-map-p
       source-field target-field
       domain-type codomain-type
       forward-hom mapping)
      (q944297-surjective-p
       domain-type codomain-type mapping))
     (q944297-open-map-p
      domain-type codomain-type mapping))))

(value-triple :itpeval-statement-checked)
:q
