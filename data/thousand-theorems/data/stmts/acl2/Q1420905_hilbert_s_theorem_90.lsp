;; Statement-only formalization of thousand-theorems corpus artifact Q1420905,
;; "Hilbert's theorem 90": in a finite cyclic Galois field extension, every
;; element of norm one is y divided by its image under a chosen generator,
;; for some nonzero y. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Field structures and an arbitrary embedding of the base field into the
;; extension field. Structure tags select operations without enumerating or
;; otherwise restricting either carrier.

(defstub q1420905-field-element-p (field value) t)
(defstub q1420905-field-zero (field) t)
(defstub q1420905-field-one (field) t)
(defstub q1420905-field-add (field left right) t)
(defstub q1420905-field-multiply (field left right) t)
(defstub q1420905-field-negate (field value) t)
(defstub q1420905-field-inverse (field value) t)
(defstub q1420905-algebra-map (extension base top value) t)

(defun-sk q1420905-field-laws-p (field)
  (forall (a b c)
    (and
     (implies
      (q1420905-field-element-p field a)
      (and
       (q1420905-field-element-p
        field (q1420905-field-negate field a))
       (q1420905-field-element-p
        field (q1420905-field-inverse field a))
       (equal
        (q1420905-field-add
         field a (q1420905-field-zero field))
        a)
       (equal
        (q1420905-field-add
         field (q1420905-field-zero field) a)
        a)
       (equal
        (q1420905-field-add
         field a (q1420905-field-negate field a))
        (q1420905-field-zero field))
       (equal
        (q1420905-field-multiply
         field a (q1420905-field-one field))
        a)
       (equal
        (q1420905-field-multiply
         field (q1420905-field-one field) a)
        a)
       (implies
        (not (equal a (q1420905-field-zero field)))
        (and
         (equal
          (q1420905-field-multiply
           field a (q1420905-field-inverse field a))
          (q1420905-field-one field))
         (equal
          (q1420905-field-multiply
           field (q1420905-field-inverse field a) a)
          (q1420905-field-one field))))))
     (implies
      (and
       (q1420905-field-element-p field a)
       (q1420905-field-element-p field b))
      (and
       (q1420905-field-element-p
        field (q1420905-field-add field a b))
       (q1420905-field-element-p
        field (q1420905-field-multiply field a b))
       (equal
        (q1420905-field-add field a b)
        (q1420905-field-add field b a))
       (equal
        (q1420905-field-multiply field a b)
        (q1420905-field-multiply field b a))))
     (implies
      (and
       (q1420905-field-element-p field a)
       (q1420905-field-element-p field b)
       (q1420905-field-element-p field c))
      (and
       (equal
        (q1420905-field-add
         field (q1420905-field-add field a b) c)
        (q1420905-field-add
         field a (q1420905-field-add field b c)))
       (equal
        (q1420905-field-multiply
         field (q1420905-field-multiply field a b) c)
        (q1420905-field-multiply
         field a (q1420905-field-multiply field b c)))
       (equal
        (q1420905-field-multiply
         field a (q1420905-field-add field b c))
        (q1420905-field-add
         field
         (q1420905-field-multiply field a b)
         (q1420905-field-multiply field a c))))))))

(defun q1420905-field-p (field)
  (and
   (q1420905-field-element-p
    field (q1420905-field-zero field))
   (q1420905-field-element-p
    field (q1420905-field-one field))
   (not
    (equal
     (q1420905-field-zero field)
     (q1420905-field-one field)))
   (q1420905-field-laws-p field)))

(defun-sk q1420905-algebra-map-laws-p (extension base top)
  (forall (a b)
    (and
     (implies
      (q1420905-field-element-p base a)
      (q1420905-field-element-p
       top
       (q1420905-algebra-map extension base top a)))
     (equal
      (q1420905-algebra-map
       extension base top (q1420905-field-zero base))
      (q1420905-field-zero top))
     (equal
      (q1420905-algebra-map
       extension base top (q1420905-field-one base))
      (q1420905-field-one top))
     (implies
      (and
       (q1420905-field-element-p base a)
       (q1420905-field-element-p base b))
      (and
       (equal
        (q1420905-algebra-map
         extension base top
         (q1420905-field-add base a b))
        (q1420905-field-add
         top
         (q1420905-algebra-map extension base top a)
         (q1420905-algebra-map extension base top b)))
       (equal
        (q1420905-algebra-map
         extension base top
         (q1420905-field-multiply base a b))
        (q1420905-field-multiply
         top
         (q1420905-algebra-map extension base top a)
         (q1420905-algebra-map extension base top b)))
       (implies
        (equal
         (q1420905-algebra-map extension base top a)
         (q1420905-algebra-map extension base top b))
        (equal a b)))))))

(defun q1420905-field-extension-p (extension base top)
  (and
   (q1420905-field-p base)
   (q1420905-field-p top)
   (q1420905-algebra-map-laws-p extension base top)))

;; A finite basis is represented by a list of extension-field elements.
;; Coefficient lists range over all base-field coefficients, so spanning and
;; linear independence retain their ordinary unbounded meanings.

(defun q1420905-field-list-p (field values)
  (if (consp values)
      (and
       (q1420905-field-element-p field (car values))
       (q1420905-field-list-p field (cdr values)))
    (equal values nil)))

(defun q1420905-all-zero-p (base coefficients)
  (if (consp coefficients)
      (and
       (equal
        (car coefficients)
        (q1420905-field-zero base))
       (q1420905-all-zero-p base (cdr coefficients)))
    (equal coefficients nil)))

(defun q1420905-linear-combination
    (extension base top coefficients basis)
  (if (and (consp coefficients) (consp basis))
      (q1420905-field-add
       top
       (q1420905-field-multiply
        top
        (q1420905-algebra-map
         extension base top (car coefficients))
        (car basis))
       (q1420905-linear-combination
        extension base top (cdr coefficients) (cdr basis)))
    (q1420905-field-zero top)))

(defun-sk q1420905-linearly-independent-p
    (extension base top basis)
  (forall (coefficients)
    (implies
     (and
      (q1420905-field-list-p base coefficients)
      (equal (len coefficients) (len basis))
      (equal
       (q1420905-linear-combination
        extension base top coefficients basis)
       (q1420905-field-zero top)))
     (q1420905-all-zero-p base coefficients))))

(defun-sk q1420905-has-basis-coordinates-p
    (extension base top basis value)
  (exists (coefficients)
    (and
     (q1420905-field-list-p base coefficients)
     (equal (len coefficients) (len basis))
     (equal
      (q1420905-linear-combination
       extension base top coefficients basis)
      value))))

(defun-sk q1420905-spans-p (extension base top basis)
  (forall (value)
    (implies
     (q1420905-field-element-p top value)
     (q1420905-has-basis-coordinates-p
      extension base top basis value))))

(defun q1420905-basis-p (extension base top basis)
  (and
   (q1420905-field-list-p top basis)
   (q1420905-linearly-independent-p
    extension base top basis)
   (q1420905-spans-p extension base top basis)))

;; K-algebra automorphisms are represented extensionally by their action on
;; the whole extension field. The laws below make every admitted tag an
;; injective base-fixing field endomorphism; finite dimensionality then makes
;; it a bijective K-algebra automorphism.

(defstub q1420905-automorphism-apply
  (extension base top automorphism value)
  t)

(defun-sk q1420905-automorphism-laws-p
    (extension base top automorphism)
  (forall (a b k)
    (and
     (implies
      (q1420905-field-element-p top a)
      (q1420905-field-element-p
       top
       (q1420905-automorphism-apply
        extension base top automorphism a)))
     (equal
      (q1420905-automorphism-apply
       extension base top automorphism
       (q1420905-field-zero top))
      (q1420905-field-zero top))
     (equal
      (q1420905-automorphism-apply
       extension base top automorphism
       (q1420905-field-one top))
      (q1420905-field-one top))
     (implies
      (q1420905-field-element-p base k)
      (equal
       (q1420905-automorphism-apply
        extension base top automorphism
        (q1420905-algebra-map extension base top k))
       (q1420905-algebra-map extension base top k)))
     (implies
      (and
       (q1420905-field-element-p top a)
       (q1420905-field-element-p top b))
      (and
       (equal
        (q1420905-automorphism-apply
         extension base top automorphism
         (q1420905-field-add top a b))
        (q1420905-field-add
         top
         (q1420905-automorphism-apply
          extension base top automorphism a)
         (q1420905-automorphism-apply
          extension base top automorphism b)))
       (equal
        (q1420905-automorphism-apply
         extension base top automorphism
         (q1420905-field-multiply top a b))
        (q1420905-field-multiply
         top
         (q1420905-automorphism-apply
          extension base top automorphism a)
         (q1420905-automorphism-apply
          extension base top automorphism b)))
       (implies
        (equal
         (q1420905-automorphism-apply
          extension base top automorphism a)
         (q1420905-automorphism-apply
          extension base top automorphism b))
        (equal a b)))))))

(defun q1420905-automorphism-p
    (extension base top automorphism)
  (q1420905-automorphism-laws-p
   extension base top automorphism))

(defun-sk q1420905-automorphisms-extensionally-equal-p
    (extension base top left right)
  (forall (value)
    (implies
     (q1420905-field-element-p top value)
     (equal
      (q1420905-automorphism-apply
       extension base top left value)
      (q1420905-automorphism-apply
       extension base top right value)))))

(defun q1420905-automorphism-distinct-from-list-p
    (extension base top automorphism automorphisms)
  (if (consp automorphisms)
      (and
       (not
        (q1420905-automorphisms-extensionally-equal-p
         extension base top automorphism (car automorphisms)))
       (q1420905-automorphism-distinct-from-list-p
        extension base top automorphism (cdr automorphisms)))
    t))

(defun q1420905-pairwise-distinct-automorphisms-p
    (extension base top automorphisms)
  (if (consp automorphisms)
      (and
       (q1420905-automorphism-distinct-from-list-p
        extension base top (car automorphisms) (cdr automorphisms))
       (q1420905-pairwise-distinct-automorphisms-p
        extension base top (cdr automorphisms)))
    (equal automorphisms nil)))

(defun q1420905-valid-automorphism-list-p
    (extension base top automorphisms)
  (if (consp automorphisms)
      (and
       (q1420905-automorphism-p
        extension base top (car automorphisms))
       (q1420905-valid-automorphism-list-p
        extension base top (cdr automorphisms)))
    (equal automorphisms nil)))

(defun q1420905-automorphism-extensionally-member-p
    (extension base top automorphism automorphisms)
  (if (consp automorphisms)
      (or
       (q1420905-automorphisms-extensionally-equal-p
        extension base top automorphism (car automorphisms))
       (q1420905-automorphism-extensionally-member-p
        extension base top automorphism (cdr automorphisms)))
    nil))

(defun-sk q1420905-enumerates-all-automorphisms-p
    (extension base top automorphisms)
  (forall (automorphism)
    (implies
     (q1420905-automorphism-p
      extension base top automorphism)
     (q1420905-automorphism-extensionally-member-p
      extension base top automorphism automorphisms))))

(defun q1420905-exact-automorphism-list-p
    (extension base top automorphisms)
  (and
   (true-listp automorphisms)
   (q1420905-valid-automorphism-list-p
    extension base top automorphisms)
   (q1420905-pairwise-distinct-automorphisms-p
    extension base top automorphisms)
   (q1420905-enumerates-all-automorphisms-p
    extension base top automorphisms)))

;; For a finite field extension, having exactly [L:K] distinct K-algebra
;; automorphisms is equivalent to being Galois. This gives a basis-independent
;; first-order representation of FiniteDimensional K L and IsGalois K L.

(defun q1420905-galois-data-p
    (extension base top basis automorphisms)
  (and
   (q1420905-basis-p extension base top basis)
   (q1420905-exact-automorphism-list-p
    extension base top automorphisms)
   (equal (len automorphisms) (len basis))))

(defun-sk q1420905-finite-galois-extension-p
    (extension base top)
  (exists (basis automorphisms)
    (and
     (q1420905-field-extension-p extension base top)
     (q1420905-galois-data-p
      extension base top basis automorphisms))))

;; The generator condition is the source hypothesis that every automorphism
;; lies in the subgroup generated by g. Natural powers suffice because the
;; automorphism group is finite.

(defun q1420905-automorphism-power-apply
    (extension base top generator exponent value)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      value
    (q1420905-automorphism-apply
     extension base top generator
     (q1420905-automorphism-power-apply
      extension base top generator (- exponent 1) value))))

(defun-sk q1420905-automorphism-equals-power-p
    (extension base top automorphism generator exponent)
  (forall (value)
    (implies
     (q1420905-field-element-p top value)
     (equal
      (q1420905-automorphism-apply
       extension base top automorphism value)
      (q1420905-automorphism-power-apply
       extension base top generator exponent value)))))

(defun-sk q1420905-is-power-of-generator-p
    (extension base top automorphism generator)
  (exists (exponent)
    (and
     (natp exponent)
     (q1420905-automorphism-equals-power-p
      extension base top automorphism generator exponent))))

(defun-sk q1420905-generates-galois-group-p
    (extension base top generator)
  (forall (automorphism)
    (implies
     (q1420905-automorphism-p
      extension base top automorphism)
     (q1420905-is-power-of-generator-p
      extension base top automorphism generator))))

;; In a finite Galois extension, the algebra norm equals the product of all
;; Galois conjugates. Thus the internal exact automorphism enumeration below
;; is equivalent to Algebra.norm K x = 1 and introduces no external witness.

(defun q1420905-conjugate-product
    (extension base top automorphisms value)
  (if (consp automorphisms)
      (q1420905-field-multiply
       top
       (q1420905-automorphism-apply
        extension base top (car automorphisms) value)
       (q1420905-conjugate-product
        extension base top (cdr automorphisms) value))
    (q1420905-field-one top)))

(defun-sk q1420905-norm-one-p
    (extension base top value)
  (exists (automorphisms)
    (and
     (q1420905-exact-automorphism-list-p
      extension base top automorphisms)
     (equal
      (q1420905-conjugate-product
       extension base top automorphisms value)
      (q1420905-field-one top)))))

(defun-sk q1420905-hilbert-witness-exists-p
    (extension base top generator value)
  (exists (y)
    (and
     (q1420905-field-element-p top y)
     (not (equal y (q1420905-field-zero top)))
     (equal
      (q1420905-field-multiply
       top
       y
       (q1420905-field-inverse
        top
        (q1420905-automorphism-apply
         extension base top generator y)))
      value))))

(defun-sk
    thousand-theorems-q1420905-hilberts-theorem-90-statement
    ()
  (forall (extension base top generator value)
    (implies
     (and
      (q1420905-finite-galois-extension-p
       extension base top)
      (q1420905-automorphism-p
       extension base top generator)
      (q1420905-generates-galois-group-p
       extension base top generator)
      (q1420905-field-element-p top value)
      (q1420905-norm-one-p
       extension base top value))
     (q1420905-hilbert-witness-exists-p
      extension base top generator value))))

(value-triple :itpeval-statement-checked)
:q
