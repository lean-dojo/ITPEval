;; Statement-only formalization of thousand-theorems corpus artifact Q1816952,
;; "Schur's lemma": in an algebraically closed-field linear preadditive
;; category with kernels, the finite-dimensional endomorphism space of a
;; simple object has dimension one. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic symbols represent arbitrary fields, categories,
;; objects, morphisms, and operations. Tags select structures but do not
;; enumerate or otherwise restrict their carriers. All laws and all
;; existential data are stated below with unbounded DEFUN-SK quantifiers.

(defstub q1816952-field-element-p (field value) t)
(defstub q1816952-field-zero (field) t)
(defstub q1816952-field-one (field) t)
(defstub q1816952-field-add (field left right) t)
(defstub q1816952-field-multiply (field left right) t)
(defstub q1816952-field-negate (field value) t)
(defstub q1816952-field-inverse (field value) t)

(defstub q1816952-object-p (category object) t)
(defstub q1816952-hom-p (category source target morphism) t)
(defstub q1816952-identity (category object) t)
(defstub q1816952-compose
  (category source middle target first second)
  t)
(defstub q1816952-zero-hom (category source target) t)
(defstub q1816952-add-hom
  (category source target left right)
  t)
(defstub q1816952-negate-hom
  (category source target morphism)
  t)
(defstub q1816952-smul-hom
  (field category source target scalar morphism)
  t)

;; Fields and algebraic closedness.

(defun-sk q1816952-field-laws-p (field)
  (forall (x y z)
    (and
     (implies
      (and
       (q1816952-field-element-p field x)
       (q1816952-field-element-p field y))
      (and
       (q1816952-field-element-p
        field (q1816952-field-add field x y))
       (q1816952-field-element-p
        field (q1816952-field-multiply field x y))
       (equal
        (q1816952-field-add field x y)
        (q1816952-field-add field y x))
       (equal
        (q1816952-field-multiply field x y)
        (q1816952-field-multiply field y x))))
     (implies
      (q1816952-field-element-p field x)
      (and
       (q1816952-field-element-p
        field (q1816952-field-negate field x))
       (q1816952-field-element-p
        field (q1816952-field-inverse field x))
       (equal
        (q1816952-field-add
         field x (q1816952-field-zero field))
        x)
       (equal
        (q1816952-field-add
         field x (q1816952-field-negate field x))
        (q1816952-field-zero field))
       (equal
        (q1816952-field-multiply
         field x (q1816952-field-one field))
        x)
       (implies
        (equal x (q1816952-field-zero field))
        (equal
         (q1816952-field-inverse field x)
         (q1816952-field-zero field)))
       (implies
        (not (equal x (q1816952-field-zero field)))
        (equal
         (q1816952-field-multiply
          field x (q1816952-field-inverse field x))
         (q1816952-field-one field)))))
     (implies
      (and
       (q1816952-field-element-p field x)
       (q1816952-field-element-p field y)
       (q1816952-field-element-p field z))
      (and
       (equal
        (q1816952-field-add
         field (q1816952-field-add field x y) z)
        (q1816952-field-add
         field x (q1816952-field-add field y z)))
       (equal
        (q1816952-field-multiply
         field (q1816952-field-multiply field x y) z)
        (q1816952-field-multiply
         field x (q1816952-field-multiply field y z)))
       (equal
        (q1816952-field-multiply
         field x (q1816952-field-add field y z))
        (q1816952-field-add
         field
         (q1816952-field-multiply field x y)
         (q1816952-field-multiply field x z))))))))

(defun q1816952-field-p (field)
  (and
   (q1816952-field-element-p
    field (q1816952-field-zero field))
   (q1816952-field-element-p
    field (q1816952-field-one field))
   (not
    (equal
     (q1816952-field-zero field)
     (q1816952-field-one field)))
   (q1816952-field-laws-p field)))

;; Coefficient lists are the unrestricted finite-support representation of
;; polynomials, in increasing order of degree.

(defun q1816952-field-list-p (field values)
  (if (consp values)
      (and
       (q1816952-field-element-p field (car values))
       (q1816952-field-list-p field (cdr values)))
    (equal values nil)))

(defun q1816952-polynomial-eval (field coefficients point)
  (if (consp coefficients)
      (q1816952-field-add
       field
       (car coefficients)
       (q1816952-field-multiply
        field
        point
        (q1816952-polynomial-eval
         field (cdr coefficients) point)))
    (q1816952-field-zero field)))

(defun q1816952-nonconstant-polynomial-p (field coefficients)
  (and
   (true-listp coefficients)
   (consp coefficients)
   (consp (cdr coefficients))
   (q1816952-field-list-p field coefficients)
   (not
    (equal
     (car (last coefficients))
     (q1816952-field-zero field)))))

(defun-sk q1816952-polynomial-root-exists-p
    (field coefficients)
  (exists (root)
    (and
     (q1816952-field-element-p field root)
     (equal
      (q1816952-polynomial-eval field coefficients root)
      (q1816952-field-zero field)))))

(defun-sk q1816952-algebraically-closed-p (field)
  (forall (coefficients)
    (implies
     (q1816952-nonconstant-polynomial-p field coefficients)
     (q1816952-polynomial-root-exists-p
      field coefficients))))

(defun q1816952-algebraically-closed-field-p (field)
  (and
   (q1816952-field-p field)
   (q1816952-algebraically-closed-p field)))

;; Category laws. COMPOSE(first, second) means first followed by second.

(defun-sk q1816952-category-laws-p (category)
  (forall (a b c d f g h)
    (and
     (implies
      (q1816952-hom-p category a b f)
      (and
       (q1816952-object-p category a)
       (q1816952-object-p category b)))
     (implies
      (q1816952-object-p category a)
      (q1816952-hom-p
       category a a (q1816952-identity category a)))
     (implies
      (and
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category b c g))
      (and
       (q1816952-hom-p
        category a c
        (q1816952-compose category a b c f g))
       (equal
        (q1816952-compose
         category a a b (q1816952-identity category a) f)
        f)
       (equal
        (q1816952-compose
         category a b b f (q1816952-identity category b))
        f)))
     (implies
      (and
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category b c g)
       (q1816952-hom-p category c d h))
      (equal
       (q1816952-compose
        category a c d
        (q1816952-compose category a b c f g)
        h)
       (q1816952-compose
        category a b d
        f
        (q1816952-compose category b c d g h)))))))

;; Every hom set is an additive commutative group, and composition is
;; additive in both variables.

(defun-sk q1816952-preadditive-laws-p (category)
  (forall (a b c f g h)
    (and
     (implies
      (and
       (q1816952-object-p category a)
       (q1816952-object-p category b))
      (q1816952-hom-p
       category a b (q1816952-zero-hom category a b)))
     (implies
      (q1816952-hom-p category a b f)
      (and
       (q1816952-hom-p
        category a b (q1816952-negate-hom category a b f))
       (equal
        (q1816952-add-hom
         category a b f (q1816952-zero-hom category a b))
        f)
       (equal
        (q1816952-add-hom
         category a b f
         (q1816952-negate-hom category a b f))
        (q1816952-zero-hom category a b))))
     (implies
      (and
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category a b g))
      (and
       (q1816952-hom-p
        category a b (q1816952-add-hom category a b f g))
       (equal
        (q1816952-add-hom category a b f g)
        (q1816952-add-hom category a b g f))))
     (implies
      (and
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category a b g)
       (q1816952-hom-p category a b h))
      (equal
       (q1816952-add-hom
        category a b
        (q1816952-add-hom category a b f g)
        h)
       (q1816952-add-hom
        category a b
        f
        (q1816952-add-hom category a b g h))))
     (implies
      (and
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category a b g)
       (q1816952-hom-p category b c h))
      (equal
       (q1816952-compose
        category a b c
        (q1816952-add-hom category a b f g)
        h)
       (q1816952-add-hom
        category a c
        (q1816952-compose category a b c f h)
        (q1816952-compose category a b c g h))))
     (implies
      (and
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category b c g)
       (q1816952-hom-p category b c h))
      (equal
       (q1816952-compose
        category a b c
        f
        (q1816952-add-hom category b c g h))
       (q1816952-add-hom
        category a c
        (q1816952-compose category a b c f g)
        (q1816952-compose category a b c f h)))))))

;; The hom sets are vector spaces over FIELD and scalar multiplication is
;; compatible with composition.

(defun-sk q1816952-linear-laws-p (field category)
  (forall (a b c r s f g)
    (and
     (implies
      (and
       (q1816952-field-element-p field r)
       (q1816952-hom-p category a b f))
      (and
       (q1816952-hom-p
        category a b
        (q1816952-smul-hom field category a b r f))
       (equal
        (q1816952-smul-hom
         field category a b (q1816952-field-one field) f)
        f)
       (equal
        (q1816952-smul-hom
         field category a b r
         (q1816952-zero-hom category a b))
        (q1816952-zero-hom category a b))
       (equal
        (q1816952-smul-hom
         field category a b
         (q1816952-field-zero field)
         f)
        (q1816952-zero-hom category a b))
       (equal
        (q1816952-smul-hom
         field category a b
         (q1816952-field-negate field r)
         f)
        (q1816952-negate-hom
         category a b
         (q1816952-smul-hom
          field category a b r f)))))
     (implies
      (and
       (q1816952-field-element-p field r)
       (q1816952-field-element-p field s)
       (q1816952-hom-p category a b f))
      (and
       (equal
        (q1816952-smul-hom
         field category a b
         (q1816952-field-add field r s)
         f)
        (q1816952-add-hom
         category a b
         (q1816952-smul-hom field category a b r f)
         (q1816952-smul-hom field category a b s f)))
       (equal
        (q1816952-smul-hom
         field category a b
         (q1816952-field-multiply field r s)
         f)
        (q1816952-smul-hom
         field category a b r
         (q1816952-smul-hom field category a b s f)))))
     (implies
      (and
       (q1816952-field-element-p field r)
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category a b g))
      (equal
       (q1816952-smul-hom
        field category a b r
        (q1816952-add-hom category a b f g))
       (q1816952-add-hom
        category a b
        (q1816952-smul-hom field category a b r f)
        (q1816952-smul-hom field category a b r g))))
     (implies
      (and
       (q1816952-field-element-p field r)
       (q1816952-hom-p category a b f)
       (q1816952-hom-p category b c g))
      (and
       (equal
        (q1816952-compose
         category a b c
         (q1816952-smul-hom field category a b r f)
         g)
        (q1816952-smul-hom
         field category a c r
         (q1816952-compose category a b c f g)))
       (equal
        (q1816952-compose
         category a b c
         f
         (q1816952-smul-hom field category b c r g))
        (q1816952-smul-hom
         field category a c r
         (q1816952-compose category a b c f g))))))))

(defun q1816952-linear-preadditive-category-p
    (field category)
  (and
   (q1816952-category-laws-p category)
   (q1816952-preadditive-laws-p category)
   (q1816952-linear-laws-p field category)))

;; Categorical isomorphisms, monomorphisms, and simplicity.

(defun-sk q1816952-isomorphism-p
    (category source target morphism)
  (exists (inverse)
    (and
     (q1816952-hom-p category target source inverse)
     (equal
      (q1816952-compose
       category source target source morphism inverse)
      (q1816952-identity category source))
     (equal
      (q1816952-compose
       category target source target inverse morphism)
      (q1816952-identity category target)))))

(defun-sk q1816952-monomorphism-p
    (category source target morphism)
  (forall (test-object left right)
    (implies
     (and
      (q1816952-object-p category test-object)
      (q1816952-hom-p category test-object source left)
      (q1816952-hom-p category test-object source right)
      (equal
       (q1816952-compose
        category test-object source target left morphism)
       (q1816952-compose
        category test-object source target right morphism)))
     (equal left right))))

(defun-sk q1816952-simple-object-laws-p
    (category object)
  (forall (source morphism)
    (implies
     (and
      (q1816952-hom-p category source object morphism)
     (q1816952-monomorphism-p
       category source object morphism))
     (or
      (equal
       (q1816952-identity category source)
       (q1816952-zero-hom category source source))
      (q1816952-isomorphism-p
       category source object morphism)))))

(defun q1816952-simple-object-p (category object)
  (and
   (q1816952-object-p category object)
   (not
    (equal
     (q1816952-identity category object)
     (q1816952-zero-hom category object object)))
   (q1816952-simple-object-laws-p category object)))

;; Kernels are internal existential witnesses satisfying their unrestricted
;; universal property, including uniqueness of every factor.

(defun-sk q1816952-kernel-factor-unique-p
    (category source kernel-object kernel-arrow
     test-object test-arrow factor)
  (forall (candidate)
    (implies
     (and
      (q1816952-hom-p
       category test-object kernel-object candidate)
      (equal
       (q1816952-compose
        category test-object kernel-object source
        candidate kernel-arrow)
       test-arrow))
     (equal candidate factor))))

(defun-sk q1816952-kernel-factor-exists-p
    (category source kernel-object kernel-arrow
     test-object test-arrow)
  (exists (factor)
    (and
     (q1816952-hom-p
      category test-object kernel-object factor)
     (equal
      (q1816952-compose
       category test-object kernel-object source
       factor kernel-arrow)
      test-arrow)
     (q1816952-kernel-factor-unique-p
      category source kernel-object kernel-arrow
      test-object test-arrow factor))))

(defun-sk q1816952-kernel-universal-p
    (category source target morphism
     kernel-object kernel-arrow)
  (forall (test-object test-arrow)
    (implies
     (and
      (q1816952-hom-p
       category test-object source test-arrow)
      (equal
       (q1816952-compose
        category test-object source target
        test-arrow morphism)
       (q1816952-zero-hom
        category test-object target)))
     (q1816952-kernel-factor-exists-p
      category source kernel-object kernel-arrow
      test-object test-arrow))))

(defun-sk q1816952-kernel-exists-p
    (category source target morphism)
  (exists (kernel-object kernel-arrow)
    (and
     (q1816952-object-p category kernel-object)
     (q1816952-hom-p
      category kernel-object source kernel-arrow)
     (equal
      (q1816952-compose
       category kernel-object source target
       kernel-arrow morphism)
      (q1816952-zero-hom
       category kernel-object target))
     (q1816952-kernel-universal-p
      category source target morphism
      kernel-object kernel-arrow))))

(defun-sk q1816952-has-kernels-p (category)
  (forall (source target morphism)
    (implies
     (q1816952-hom-p category source target morphism)
     (q1816952-kernel-exists-p
      category source target morphism))))

;; Finite dimensionality is the internal existence of a finite basis of the
;; unrestricted endomorphism carrier. Coefficients are quantified inside the
;; spanning predicate rather than supplied as an external coordinate map.

(defun q1816952-endomorphism-list-p
    (category object morphisms)
  (if (consp morphisms)
      (and
       (q1816952-hom-p
        category object object (car morphisms))
       (q1816952-endomorphism-list-p
        category object (cdr morphisms)))
    (equal morphisms nil)))

(defun q1816952-all-zero-coefficients-p
    (field coefficients)
  (if (consp coefficients)
      (and
       (equal
        (car coefficients)
        (q1816952-field-zero field))
       (q1816952-all-zero-coefficients-p
        field (cdr coefficients)))
    (equal coefficients nil)))

(defun q1816952-linear-combination
    (field category object basis coefficients)
  (if (and (consp basis) (consp coefficients))
      (q1816952-add-hom
       category object object
       (q1816952-smul-hom
        field category object object
        (car coefficients) (car basis))
       (q1816952-linear-combination
        field category object
        (cdr basis) (cdr coefficients)))
    (q1816952-zero-hom category object object)))

(defun-sk q1816952-basis-coefficients-exist-p
    (field category object basis endomorphism)
  (exists (coefficients)
    (and
     (true-listp coefficients)
     (equal (len coefficients) (len basis))
     (q1816952-field-list-p field coefficients)
     (equal
      (q1816952-linear-combination
       field category object basis coefficients)
      endomorphism))))

(defun-sk q1816952-basis-spans-p
    (field category object basis)
  (forall (endomorphism)
    (implies
     (q1816952-hom-p
      category object object endomorphism)
     (q1816952-basis-coefficients-exist-p
      field category object basis endomorphism))))

(defun-sk q1816952-basis-independent-p
    (field category object basis)
  (forall (coefficients)
    (implies
     (and
      (true-listp coefficients)
      (equal (len coefficients) (len basis))
      (q1816952-field-list-p field coefficients)
      (equal
       (q1816952-linear-combination
        field category object basis coefficients)
       (q1816952-zero-hom category object object)))
     (q1816952-all-zero-coefficients-p
      field coefficients))))

(defun q1816952-basis-p
    (field category object basis)
  (and
   (true-listp basis)
   (q1816952-endomorphism-list-p category object basis)
   (q1816952-basis-spans-p field category object basis)
   (q1816952-basis-independent-p
    field category object basis)))

(defun-sk q1816952-finite-dimensional-endomorphisms-p
    (field category object)
  (exists (basis)
    (q1816952-basis-p field category object basis)))

;; A vector space has dimension one exactly when a fixed nonzero vector is a
;; basis. Here that vector is the identity endomorphism. The unique scalar
;; witness is kept internal to the conclusion.

(defun-sk q1816952-scalar-representation-unique-p
    (field category object endomorphism scalar)
  (forall (other-scalar)
    (implies
     (and
      (q1816952-field-element-p field other-scalar)
      (equal
       (q1816952-smul-hom
        field category object object
        other-scalar
        (q1816952-identity category object))
       endomorphism))
     (equal other-scalar scalar))))

(defun-sk q1816952-scalar-representation-exists-p
    (field category object endomorphism)
  (exists (scalar)
    (and
     (q1816952-field-element-p field scalar)
     (equal
      (q1816952-smul-hom
       field category object object
       scalar
       (q1816952-identity category object))
      endomorphism)
     (q1816952-scalar-representation-unique-p
      field category object endomorphism scalar))))

(defun-sk q1816952-every-endomorphism-is-scalar-p
    (field category object)
  (forall (endomorphism)
    (implies
     (q1816952-hom-p
      category object object endomorphism)
     (q1816952-scalar-representation-exists-p
      field category object endomorphism))))

(defun q1816952-endomorphism-dimension-one-p
    (field category object)
  (and
   (q1816952-hom-p
    category object object
    (q1816952-identity category object))
   (not
    (equal
     (q1816952-identity category object)
     (q1816952-zero-hom category object object)))
   (q1816952-every-endomorphism-is-scalar-p
    field category object)))

(defun-sk thousand-theorems-q1816952-schur-s-lemma-statement ()
  (forall (field category object)
    (implies
     (and
      (q1816952-algebraically-closed-field-p field)
      (q1816952-linear-preadditive-category-p
       field category)
      (q1816952-has-kernels-p category)
      (q1816952-simple-object-p category object)
      (q1816952-finite-dimensional-endomorphisms-p
       field category object))
     (q1816952-endomorphism-dimension-one-p
      field category object))))

(value-triple :itpeval-statement-checked)
:q
