;; Statement-only formalization of thousand-theorems corpus artifact Q1148215,
;; "Mitchell's embedding theorem": every abelian category admits a full and
;; faithful functor into modules over a ring that preserves finite limits and
;; finite colimits. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Categories, rings, modules, and functors are explicit bundles of tame
;; ACL2 function objects.  Thus all structure quantified in the Lean theorem,
;; including the existential ring and functor, remains inside the statement.
;; Linear maps include every tame unary function satisfying the linear laws;
;; identity and composition are exact syntax constructors.  Equality of
;; linear maps below is pointwise equality, the ACL2 presentation of the
;; function-extensional equality used by ModuleCat.

(defun q1148215-app1 (function x)
  (apply$ function (list x)))

(defun q1148215-app2 (function x y)
  (apply$ function (list x y)))

(defun q1148215-app3 (function x y z)
  (apply$ function (list x y z)))

(defun q1148215-app4 (function w x y z)
  (apply$ function (list w x y z)))

(defun q1148215-app5 (function v w x y z)
  (apply$ function (list v w x y z)))

;; A category bundle contains, in order, predicates for objects and typed
;; morphisms, identity and composition operations, and the zero, addition,
;; and negation operations on hom groups.

(defun q1148215-category-structure-p (category)
  (and
   (true-listp category)
   (equal (len category) 7)
   (tamep-functionp (nth 0 category))
   (tamep-functionp (nth 1 category))
   (tamep-functionp (nth 2 category))
   (tamep-functionp (nth 3 category))
   (tamep-functionp (nth 4 category))
   (tamep-functionp (nth 5 category))
   (tamep-functionp (nth 6 category))))

(defun q1148215-object-p (category object)
  (q1148215-app1 (nth 0 category) object))

(defun q1148215-hom-p (category source target morphism)
  (q1148215-app3 (nth 1 category) source target morphism))

(defun q1148215-identity (category object)
  (q1148215-app1 (nth 2 category) object))

(defun q1148215-compose
    (category source middle target first second)
  (q1148215-app5
   (nth 3 category) source middle target first second))

(defun q1148215-zero-hom (category source target)
  (q1148215-app2 (nth 4 category) source target))

(defun q1148215-add-hom
    (category source target left right)
  (q1148215-app4
   (nth 5 category) source target left right))

(defun q1148215-negate-hom
    (category source target morphism)
  (q1148215-app3
   (nth 6 category) source target morphism))

;; A ring bundle contains a carrier predicate, zero, one, addition,
;; multiplication, and negation.

(defun q1148215-ring-structure-p (ring)
  (and
   (true-listp ring)
   (equal (len ring) 6)
   (tamep-functionp (nth 0 ring))
   (tamep-functionp (nth 3 ring))
   (tamep-functionp (nth 4 ring))
   (tamep-functionp (nth 5 ring))))

(defun q1148215-ring-element-p (ring value)
  (q1148215-app1 (nth 0 ring) value))

(defun q1148215-ring-zero (ring)
  (nth 1 ring))

(defun q1148215-ring-one (ring)
  (nth 2 ring))

(defun q1148215-ring-add (ring left right)
  (q1148215-app2 (nth 3 ring) left right))

(defun q1148215-ring-multiply (ring left right)
  (q1148215-app2 (nth 4 ring) left right))

(defun q1148215-ring-negate (ring value)
  (q1148215-app1 (nth 5 ring) value))

;; A module bundle contains a carrier predicate, zero, addition, negation,
;; and scalar multiplication.

(defun q1148215-module-structure-p (module)
  (and
   (true-listp module)
   (equal (len module) 5)
   (tamep-functionp (nth 0 module))
   (tamep-functionp (nth 2 module))
   (tamep-functionp (nth 3 module))
   (tamep-functionp (nth 4 module))))

(defun q1148215-module-element-p (ring module value)
  (declare (ignore ring))
  (q1148215-app1 (nth 0 module) value))

(defun q1148215-module-zero (ring module)
  (declare (ignore ring))
  (nth 1 module))

(defun q1148215-module-add (ring module left right)
  (declare (ignore ring))
  (q1148215-app2 (nth 2 module) left right))

(defun q1148215-module-negate (ring module value)
  (declare (ignore ring))
  (q1148215-app1 (nth 3 module) value))

(defun q1148215-module-smul (ring module scalar value)
  (declare (ignore ring))
  (q1148215-app2 (nth 4 module) scalar value))

;; A linear map is either a tame unary function, the identity constructor,
;; or a composition constructor.

(defun q1148215-linear-map-syntax-p (linear-map)
  (declare (xargs :measure (acl2-count linear-map)))
  (cond
   ((tamep-functionp linear-map) t)
   ((equal linear-map '(:identity)) t)
   ((and
     (consp linear-map)
     (equal (car linear-map) :compose)
     (consp (cdr linear-map))
     (consp (cddr linear-map))
     (null (cdddr linear-map)))
    (and
     (q1148215-linear-map-syntax-p (cadr linear-map))
     (q1148215-linear-map-syntax-p (caddr linear-map))))
   (t nil)))

(defun q1148215-linear-apply-core (linear-map value)
  (declare (xargs :measure (acl2-count linear-map)))
  (cond
   ((tamep-functionp linear-map)
    (q1148215-app1 linear-map value))
   ((equal linear-map '(:identity))
    value)
   ((and
     (consp linear-map)
     (equal (car linear-map) :compose)
     (consp (cdr linear-map))
     (consp (cddr linear-map))
     (null (cdddr linear-map)))
    (q1148215-linear-apply-core
     (caddr linear-map)
     (q1148215-linear-apply-core
      (cadr linear-map) value)))
   (t nil)))

(defun q1148215-linear-apply
    (ring source target linear-map value)
  (declare (ignore ring source target))
  (q1148215-linear-apply-core linear-map value))

(defun q1148215-linear-identity (ring module)
  (declare (ignore ring module))
  '(:identity))

(defun q1148215-linear-compose
    (ring source middle target first second)
  (declare (ignore ring source middle target))
  (list :compose first second))

;; A functor bundle contains an object map and a typed morphism map.

(defun q1148215-functor-structure-p (functor)
  (and
   (true-listp functor)
   (equal (len functor) 2)
   (tamep-functionp (nth 0 functor))
   (tamep-functionp (nth 1 functor))))

(defun q1148215-functor-object (functor object)
  (q1148215-app1 (nth 0 functor) object))

(defun q1148215-functor-morphism
    (functor source target morphism)
  (q1148215-app3 (nth 1 functor) source target morphism))

;; Categories and preadditive categories.

(defun-sk q1148215-category-laws-p (category)
  (forall (a b c d f g h)
    (and
     (implies
      (q1148215-hom-p category a b f)
      (and
       (q1148215-object-p category a)
       (q1148215-object-p category b)))
     (implies
      (q1148215-object-p category a)
      (q1148215-hom-p
       category a a (q1148215-identity category a)))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category b c g))
      (and
       (q1148215-hom-p
        category a c
        (q1148215-compose category a b c f g))
       (equal
        (q1148215-compose
         category a a b (q1148215-identity category a) f)
        f)
       (equal
        (q1148215-compose
         category a b b f (q1148215-identity category b))
        f)))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category b c g)
       (q1148215-hom-p category c d h))
      (equal
       (q1148215-compose
        category a c d
        (q1148215-compose category a b c f g)
        h)
       (q1148215-compose
        category a b d
        f
        (q1148215-compose category b c d g h)))))))

(defun-sk q1148215-preadditive-laws-p (category)
  (forall (a b c f g h)
    (and
     (implies
      (and
       (q1148215-object-p category a)
       (q1148215-object-p category b))
      (q1148215-hom-p
       category a b (q1148215-zero-hom category a b)))
     (implies
      (q1148215-hom-p category a b f)
      (and
       (q1148215-hom-p
        category a b (q1148215-negate-hom category a b f))
       (equal
        (q1148215-add-hom
         category a b f (q1148215-zero-hom category a b))
        f)
       (equal
        (q1148215-add-hom
         category a b (q1148215-zero-hom category a b) f)
        f)
       (equal
        (q1148215-add-hom
         category a b f
         (q1148215-negate-hom category a b f))
        (q1148215-zero-hom category a b))))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category a b g))
      (and
       (q1148215-hom-p
        category a b (q1148215-add-hom category a b f g))
       (equal
        (q1148215-add-hom category a b f g)
        (q1148215-add-hom category a b g f))))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category a b g)
       (q1148215-hom-p category a b h))
      (equal
       (q1148215-add-hom
        category a b
        (q1148215-add-hom category a b f g)
        h)
       (q1148215-add-hom
        category a b
        f
        (q1148215-add-hom category a b g h))))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category a b g)
       (q1148215-hom-p category b c h))
      (equal
       (q1148215-compose
        category a b c
        (q1148215-add-hom category a b f g)
        h)
       (q1148215-add-hom
        category a c
        (q1148215-compose category a b c f h)
        (q1148215-compose category a b c g h))))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category b c g)
       (q1148215-hom-p category b c h))
      (equal
       (q1148215-compose
        category a b c
        f
        (q1148215-add-hom category b c g h))
       (q1148215-add-hom
        category a c
        (q1148215-compose category a b c f g)
        (q1148215-compose category a b c f h)))))))

;; Finite categorical universal properties.

(defun-sk q1148215-terminal-arrow-unique-p
    (category object terminal-object arrow)
  (forall (candidate)
    (implies
     (q1148215-hom-p
      category object terminal-object candidate)
     (equal candidate arrow))))

(defun-sk q1148215-terminal-arrow-exists-p
    (category object terminal-object)
  (exists (arrow)
    (and
     (q1148215-hom-p category object terminal-object arrow)
     (q1148215-terminal-arrow-unique-p
      category object terminal-object arrow))))

(defun-sk q1148215-terminal-universal-p
    (category terminal-object)
  (forall (object)
    (implies
     (q1148215-object-p category object)
     (q1148215-terminal-arrow-exists-p
      category object terminal-object))))

(defun q1148215-terminal-object-p (category terminal-object)
  (and
   (q1148215-object-p category terminal-object)
   (q1148215-terminal-universal-p category terminal-object)))

(defun-sk q1148215-initial-arrow-unique-p
    (category initial-object object arrow)
  (forall (candidate)
    (implies
     (q1148215-hom-p
      category initial-object object candidate)
     (equal candidate arrow))))

(defun-sk q1148215-initial-arrow-exists-p
    (category initial-object object)
  (exists (arrow)
    (and
     (q1148215-hom-p category initial-object object arrow)
     (q1148215-initial-arrow-unique-p
      category initial-object object arrow))))

(defun-sk q1148215-initial-universal-p
    (category initial-object)
  (forall (object)
    (implies
     (q1148215-object-p category object)
     (q1148215-initial-arrow-exists-p
      category initial-object object))))

(defun q1148215-initial-object-p (category initial-object)
  (and
   (q1148215-object-p category initial-object)
   (q1148215-initial-universal-p category initial-object)))

(defun q1148215-zero-object-p (category zero-object)
  (and
   (q1148215-terminal-object-p category zero-object)
   (q1148215-initial-object-p category zero-object)))

(defun-sk q1148215-zero-object-exists-p (category)
  (exists (zero-object)
    (q1148215-zero-object-p category zero-object)))

(defun-sk q1148215-product-factor-unique-p
    (category left right product-object projection-left projection-right
     test-object left-map right-map factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-hom-p
       category test-object product-object candidate)
      (equal
       (q1148215-compose
        category test-object product-object left
        candidate projection-left)
       left-map)
      (equal
       (q1148215-compose
        category test-object product-object right
        candidate projection-right)
       right-map))
     (equal candidate factor))))

(defun-sk q1148215-product-factor-exists-p
    (category left right product-object projection-left projection-right
     test-object left-map right-map)
  (exists (factor)
    (and
     (q1148215-hom-p
      category test-object product-object factor)
     (equal
      (q1148215-compose
       category test-object product-object left
       factor projection-left)
      left-map)
     (equal
      (q1148215-compose
       category test-object product-object right
       factor projection-right)
      right-map)
     (q1148215-product-factor-unique-p
      category left right product-object
      projection-left projection-right
      test-object left-map right-map factor))))

(defun-sk q1148215-product-universal-p
    (category left right product-object projection-left projection-right)
  (forall (test-object left-map right-map)
    (implies
     (and
      (q1148215-hom-p category test-object left left-map)
      (q1148215-hom-p category test-object right right-map))
     (q1148215-product-factor-exists-p
      category left right product-object
      projection-left projection-right
      test-object left-map right-map))))

(defun q1148215-product-p
    (category left right product-object projection-left projection-right)
  (and
   (q1148215-object-p category left)
   (q1148215-object-p category right)
   (q1148215-object-p category product-object)
   (q1148215-hom-p
    category product-object left projection-left)
   (q1148215-hom-p
    category product-object right projection-right)
   (q1148215-product-universal-p
    category left right product-object
    projection-left projection-right)))

(defun-sk q1148215-product-exists-p (category left right)
  (exists (product-object projection-left projection-right)
    (q1148215-product-p
     category left right product-object
     projection-left projection-right)))

(defun-sk q1148215-has-binary-products-p (category)
  (forall (left right)
    (implies
     (and
      (q1148215-object-p category left)
      (q1148215-object-p category right))
     (q1148215-product-exists-p category left right))))

(defun-sk q1148215-coproduct-factor-unique-p
    (category left right coproduct-object injection-left injection-right
     test-object left-map right-map factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-hom-p
       category coproduct-object test-object candidate)
      (equal
       (q1148215-compose
        category left coproduct-object test-object
        injection-left candidate)
       left-map)
      (equal
       (q1148215-compose
        category right coproduct-object test-object
        injection-right candidate)
       right-map))
     (equal candidate factor))))

(defun-sk q1148215-coproduct-factor-exists-p
    (category left right coproduct-object injection-left injection-right
     test-object left-map right-map)
  (exists (factor)
    (and
     (q1148215-hom-p
      category coproduct-object test-object factor)
     (equal
      (q1148215-compose
       category left coproduct-object test-object
       injection-left factor)
      left-map)
     (equal
      (q1148215-compose
       category right coproduct-object test-object
       injection-right factor)
      right-map)
     (q1148215-coproduct-factor-unique-p
      category left right coproduct-object
      injection-left injection-right
      test-object left-map right-map factor))))

(defun-sk q1148215-coproduct-universal-p
    (category left right coproduct-object injection-left injection-right)
  (forall (test-object left-map right-map)
    (implies
     (and
      (q1148215-hom-p category left test-object left-map)
      (q1148215-hom-p category right test-object right-map))
     (q1148215-coproduct-factor-exists-p
      category left right coproduct-object
      injection-left injection-right
      test-object left-map right-map))))

(defun q1148215-coproduct-p
    (category left right coproduct-object injection-left injection-right)
  (and
   (q1148215-object-p category left)
   (q1148215-object-p category right)
   (q1148215-object-p category coproduct-object)
   (q1148215-hom-p
    category left coproduct-object injection-left)
   (q1148215-hom-p
    category right coproduct-object injection-right)
   (q1148215-coproduct-universal-p
    category left right coproduct-object
    injection-left injection-right)))

(defun-sk q1148215-coproduct-exists-p (category left right)
  (exists (coproduct-object injection-left injection-right)
    (q1148215-coproduct-p
     category left right coproduct-object
     injection-left injection-right)))

(defun-sk q1148215-has-binary-coproducts-p (category)
  (forall (left right)
    (implies
     (and
      (q1148215-object-p category left)
      (q1148215-object-p category right))
     (q1148215-coproduct-exists-p category left right))))

(defun-sk q1148215-equalizer-factor-unique-p
    (category source equalizer-object equalizer-arrow
     test-object test-arrow factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-hom-p
       category test-object equalizer-object candidate)
      (equal
       (q1148215-compose
        category test-object equalizer-object source
        candidate equalizer-arrow)
       test-arrow))
     (equal candidate factor))))

(defun-sk q1148215-equalizer-factor-exists-p
    (category source equalizer-object equalizer-arrow
     test-object test-arrow)
  (exists (factor)
    (and
     (q1148215-hom-p
      category test-object equalizer-object factor)
     (equal
      (q1148215-compose
       category test-object equalizer-object source
       factor equalizer-arrow)
      test-arrow)
     (q1148215-equalizer-factor-unique-p
      category source equalizer-object equalizer-arrow
      test-object test-arrow factor))))

(defun-sk q1148215-equalizer-universal-p
    (category source target first second
     equalizer-object equalizer-arrow)
  (forall (test-object test-arrow)
    (implies
     (and
      (q1148215-hom-p
       category test-object source test-arrow)
      (equal
       (q1148215-compose
        category test-object source target test-arrow first)
       (q1148215-compose
        category test-object source target test-arrow second)))
     (q1148215-equalizer-factor-exists-p
      category source equalizer-object equalizer-arrow
      test-object test-arrow))))

(defun q1148215-equalizer-p
    (category source target first second
     equalizer-object equalizer-arrow)
  (and
   (q1148215-hom-p category source target first)
   (q1148215-hom-p category source target second)
   (q1148215-object-p category equalizer-object)
   (q1148215-hom-p
    category equalizer-object source equalizer-arrow)
   (equal
    (q1148215-compose
     category equalizer-object source target
     equalizer-arrow first)
    (q1148215-compose
     category equalizer-object source target
     equalizer-arrow second))
   (q1148215-equalizer-universal-p
    category source target first second
    equalizer-object equalizer-arrow)))

(defun-sk q1148215-equalizer-exists-p
    (category source target first second)
  (exists (equalizer-object equalizer-arrow)
    (q1148215-equalizer-p
     category source target first second
     equalizer-object equalizer-arrow)))

(defun-sk q1148215-coequalizer-factor-unique-p
    (category target coequalizer-object coequalizer-arrow
     test-object test-arrow factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-hom-p
       category coequalizer-object test-object candidate)
      (equal
       (q1148215-compose
        category target coequalizer-object test-object
        coequalizer-arrow candidate)
       test-arrow))
     (equal candidate factor))))

(defun-sk q1148215-coequalizer-factor-exists-p
    (category target coequalizer-object coequalizer-arrow
     test-object test-arrow)
  (exists (factor)
    (and
     (q1148215-hom-p
      category coequalizer-object test-object factor)
     (equal
      (q1148215-compose
       category target coequalizer-object test-object
       coequalizer-arrow factor)
      test-arrow)
     (q1148215-coequalizer-factor-unique-p
      category target coequalizer-object coequalizer-arrow
      test-object test-arrow factor))))

(defun-sk q1148215-coequalizer-universal-p
    (category source target first second
     coequalizer-object coequalizer-arrow)
  (forall (test-object test-arrow)
    (implies
     (and
      (q1148215-hom-p
       category target test-object test-arrow)
      (equal
       (q1148215-compose
        category source target test-object first test-arrow)
       (q1148215-compose
        category source target test-object second test-arrow)))
     (q1148215-coequalizer-factor-exists-p
      category target coequalizer-object coequalizer-arrow
      test-object test-arrow))))

(defun q1148215-coequalizer-p
    (category source target first second
     coequalizer-object coequalizer-arrow)
  (and
   (q1148215-hom-p category source target first)
   (q1148215-hom-p category source target second)
   (q1148215-object-p category coequalizer-object)
   (q1148215-hom-p
    category target coequalizer-object coequalizer-arrow)
   (equal
    (q1148215-compose
     category source target coequalizer-object
     first coequalizer-arrow)
    (q1148215-compose
     category source target coequalizer-object
     second coequalizer-arrow))
   (q1148215-coequalizer-universal-p
    category source target first second
    coequalizer-object coequalizer-arrow)))

(defun-sk q1148215-coequalizer-exists-p
    (category source target first second)
  (exists (coequalizer-object coequalizer-arrow)
    (q1148215-coequalizer-p
     category source target first second
     coequalizer-object coequalizer-arrow)))

;; Kernels, cokernels, normal monomorphisms, and normal epimorphisms.

(defun q1148215-kernel-p
    (category source target morphism kernel-object kernel-arrow)
  (q1148215-equalizer-p
   category source target
   morphism (q1148215-zero-hom category source target)
   kernel-object kernel-arrow))

(defun-sk q1148215-kernel-exists-p
    (category source target morphism)
  (exists (kernel-object kernel-arrow)
    (q1148215-kernel-p
     category source target morphism
     kernel-object kernel-arrow)))

(defun-sk q1148215-has-kernels-p (category)
  (forall (source target morphism)
    (implies
     (q1148215-hom-p category source target morphism)
     (q1148215-kernel-exists-p
      category source target morphism))))

(defun q1148215-cokernel-p
    (category source target morphism cokernel-object cokernel-arrow)
  (q1148215-coequalizer-p
   category source target
   morphism (q1148215-zero-hom category source target)
   cokernel-object cokernel-arrow))

(defun-sk q1148215-cokernel-exists-p
    (category source target morphism)
  (exists (cokernel-object cokernel-arrow)
    (q1148215-cokernel-p
     category source target morphism
     cokernel-object cokernel-arrow)))

(defun-sk q1148215-has-cokernels-p (category)
  (forall (source target morphism)
    (implies
     (q1148215-hom-p category source target morphism)
     (q1148215-cokernel-exists-p
      category source target morphism))))

(defun-sk q1148215-monomorphism-p
    (category source target morphism)
  (forall (test-object left right)
    (implies
     (and
      (q1148215-hom-p category test-object source left)
      (q1148215-hom-p category test-object source right)
      (equal
       (q1148215-compose
        category test-object source target left morphism)
       (q1148215-compose
        category test-object source target right morphism)))
     (equal left right))))

(defun-sk q1148215-epimorphism-p
    (category source target morphism)
  (forall (test-object left right)
    (implies
     (and
      (q1148215-hom-p category target test-object left)
      (q1148215-hom-p category target test-object right)
      (equal
       (q1148215-compose
        category source target test-object morphism left)
       (q1148215-compose
        category source target test-object morphism right)))
     (equal left right))))

(defun-sk q1148215-normal-mono-witness-exists-p
    (category source target morphism)
  (exists (cokernel-target cokernel-map)
    (and
     (q1148215-hom-p
      category target cokernel-target cokernel-map)
     (q1148215-kernel-p
      category target cokernel-target cokernel-map
      source morphism))))

(defun-sk q1148215-all-monomorphisms-normal-p (category)
  (forall (source target morphism)
    (implies
     (and
      (q1148215-hom-p category source target morphism)
      (q1148215-monomorphism-p
       category source target morphism))
     (q1148215-normal-mono-witness-exists-p
      category source target morphism))))

(defun-sk q1148215-normal-epi-witness-exists-p
    (category source target morphism)
  (exists (kernel-source kernel-map)
    (and
     (q1148215-hom-p category kernel-source source kernel-map)
     (q1148215-cokernel-p
      category kernel-source source kernel-map
      target morphism))))

(defun-sk q1148215-all-epimorphisms-normal-p (category)
  (forall (source target morphism)
    (implies
     (and
      (q1148215-hom-p category source target morphism)
      (q1148215-epimorphism-p
       category source target morphism))
     (q1148215-normal-epi-witness-exists-p
      category source target morphism))))

;; This is the usual equivalent axiomatization of an abelian category:
;; preadditive, finite biproducts (presented as zero, binary products and
;; binary coproducts), kernels and cokernels, with every mono and epi normal.

(defun q1148215-abelian-category-p (category)
  (and
   (q1148215-category-structure-p category)
   (q1148215-category-laws-p category)
   (q1148215-preadditive-laws-p category)
   (q1148215-zero-object-exists-p category)
   (q1148215-has-binary-products-p category)
   (q1148215-has-binary-coproducts-p category)
   (q1148215-has-kernels-p category)
   (q1148215-has-cokernels-p category)
   (q1148215-all-monomorphisms-normal-p category)
   (q1148215-all-epimorphisms-normal-p category)))

;; Rings, modules, and linear maps.  Multiplication is not assumed
;; commutative, matching ModuleCat over an arbitrary ring.

(defun-sk q1148215-ring-laws-p (ring)
  (forall (x y z)
    (and
     (implies
      (q1148215-ring-element-p ring x)
      (and
       (q1148215-ring-element-p
        ring (q1148215-ring-negate ring x))
       (equal
        (q1148215-ring-add
         ring x (q1148215-ring-zero ring))
        x)
       (equal
        (q1148215-ring-add
         ring (q1148215-ring-zero ring) x)
        x)
       (equal
        (q1148215-ring-add
         ring x (q1148215-ring-negate ring x))
        (q1148215-ring-zero ring))
       (equal
        (q1148215-ring-multiply
         ring x (q1148215-ring-one ring))
        x)
       (equal
        (q1148215-ring-multiply
         ring (q1148215-ring-one ring) x)
        x)))
     (implies
      (and
       (q1148215-ring-element-p ring x)
       (q1148215-ring-element-p ring y))
      (and
       (q1148215-ring-element-p
        ring (q1148215-ring-add ring x y))
       (q1148215-ring-element-p
        ring (q1148215-ring-multiply ring x y))
       (equal
        (q1148215-ring-add ring x y)
        (q1148215-ring-add ring y x))))
     (implies
      (and
       (q1148215-ring-element-p ring x)
       (q1148215-ring-element-p ring y)
       (q1148215-ring-element-p ring z))
      (and
       (equal
        (q1148215-ring-add
         ring (q1148215-ring-add ring x y) z)
        (q1148215-ring-add
         ring x (q1148215-ring-add ring y z)))
       (equal
        (q1148215-ring-multiply
         ring (q1148215-ring-multiply ring x y) z)
        (q1148215-ring-multiply
         ring x (q1148215-ring-multiply ring y z)))
       (equal
        (q1148215-ring-multiply
         ring x (q1148215-ring-add ring y z))
        (q1148215-ring-add
         ring
         (q1148215-ring-multiply ring x y)
         (q1148215-ring-multiply ring x z)))
       (equal
        (q1148215-ring-multiply
         ring (q1148215-ring-add ring x y) z)
        (q1148215-ring-add
         ring
         (q1148215-ring-multiply ring x z)
         (q1148215-ring-multiply ring y z))))))))

(defun q1148215-ring-p (ring)
  (and
   (q1148215-ring-structure-p ring)
   (q1148215-ring-element-p
    ring (q1148215-ring-zero ring))
   (q1148215-ring-element-p
    ring (q1148215-ring-one ring))
   (q1148215-ring-laws-p ring)))

(defun-sk q1148215-module-laws-p (ring module)
  (forall (r s x y z)
    (and
     (implies
      (q1148215-module-element-p ring module x)
      (and
       (q1148215-module-element-p
        ring module
        (q1148215-module-negate ring module x))
       (equal
        (q1148215-module-add
         ring module x (q1148215-module-zero ring module))
        x)
       (equal
        (q1148215-module-add
         ring module (q1148215-module-zero ring module) x)
        x)
       (equal
        (q1148215-module-add
         ring module x
         (q1148215-module-negate ring module x))
        (q1148215-module-zero ring module))))
     (implies
      (and
       (q1148215-module-element-p ring module x)
       (q1148215-module-element-p ring module y))
      (and
       (q1148215-module-element-p
        ring module
        (q1148215-module-add ring module x y))
       (equal
        (q1148215-module-add ring module x y)
        (q1148215-module-add ring module y x))))
     (implies
      (and
       (q1148215-module-element-p ring module x)
       (q1148215-module-element-p ring module y)
       (q1148215-module-element-p ring module z))
      (equal
       (q1148215-module-add
        ring module
        (q1148215-module-add ring module x y)
        z)
       (q1148215-module-add
        ring module x
        (q1148215-module-add ring module y z))))
     (implies
      (and
       (q1148215-ring-element-p ring r)
       (q1148215-module-element-p ring module x))
      (and
       (q1148215-module-element-p
        ring module
        (q1148215-module-smul ring module r x))
       (equal
        (q1148215-module-smul
         ring module (q1148215-ring-one ring) x)
        x)
       (equal
        (q1148215-module-smul
         ring module (q1148215-ring-zero ring) x)
        (q1148215-module-zero ring module))))
     (implies
      (and
       (q1148215-ring-element-p ring r)
       (q1148215-ring-element-p ring s)
       (q1148215-module-element-p ring module x))
      (and
       (equal
        (q1148215-module-smul
         ring module (q1148215-ring-add ring r s) x)
        (q1148215-module-add
         ring module
         (q1148215-module-smul ring module r x)
         (q1148215-module-smul ring module s x)))
       (equal
        (q1148215-module-smul
         ring module (q1148215-ring-multiply ring r s) x)
        (q1148215-module-smul
         ring module r
         (q1148215-module-smul ring module s x)))))
     (implies
      (and
       (q1148215-ring-element-p ring r)
       (q1148215-module-element-p ring module x)
       (q1148215-module-element-p ring module y))
      (equal
       (q1148215-module-smul
        ring module r
        (q1148215-module-add ring module x y))
       (q1148215-module-add
        ring module
        (q1148215-module-smul ring module r x)
        (q1148215-module-smul ring module r y)))))))

(defun q1148215-module-p (ring module)
  (and
   (q1148215-ring-p ring)
   (q1148215-module-structure-p module)
   (q1148215-module-element-p
    ring module (q1148215-module-zero ring module))
   (q1148215-module-laws-p ring module)))

(defun-sk q1148215-linear-map-laws-p
    (ring source target linear-map)
  (forall (scalar left right)
    (and
     (implies
      (q1148215-module-element-p ring source left)
      (q1148215-module-element-p
       ring target
       (q1148215-linear-apply
        ring source target linear-map left)))
     (implies
      (and
       (q1148215-module-element-p ring source left)
       (q1148215-module-element-p ring source right))
      (equal
       (q1148215-linear-apply
        ring source target linear-map
        (q1148215-module-add ring source left right))
       (q1148215-module-add
        ring target
        (q1148215-linear-apply
         ring source target linear-map left)
        (q1148215-linear-apply
         ring source target linear-map right))))
     (implies
      (and
       (q1148215-ring-element-p ring scalar)
       (q1148215-module-element-p ring source left))
      (equal
       (q1148215-linear-apply
        ring source target linear-map
        (q1148215-module-smul ring source scalar left))
       (q1148215-module-smul
        ring target scalar
        (q1148215-linear-apply
         ring source target linear-map left)))))))

(defun q1148215-linear-map-p
    (ring source target linear-map)
  (and
   (q1148215-module-p ring source)
   (q1148215-module-p ring target)
   (q1148215-linear-map-syntax-p linear-map)
   (q1148215-linear-map-laws-p
    ring source target linear-map)))

(defun-sk q1148215-linear-maps-pointwise-equal-p
    (ring source target left right)
  (forall (value)
    (implies
     (q1148215-module-element-p ring source value)
     (equal
      (q1148215-linear-apply
       ring source target left value)
      (q1148215-linear-apply
       ring source target right value)))))

(defun-sk q1148215-linear-identity-laws-p (ring)
  (forall (module value)
    (and
     (implies
      (q1148215-module-p ring module)
      (q1148215-linear-map-p
       ring module module
       (q1148215-linear-identity ring module)))
     (implies
      (q1148215-module-element-p ring module value)
      (equal
       (q1148215-linear-apply
        ring module module
        (q1148215-linear-identity ring module)
        value)
       value)))))

(defun-sk q1148215-linear-compose-laws-p (ring)
  (forall (source middle target first second value)
    (and
     (implies
      (and
       (q1148215-linear-map-p ring source middle first)
       (q1148215-linear-map-p ring middle target second))
      (q1148215-linear-map-p
       ring source target
       (q1148215-linear-compose
        ring source middle target first second)))
     (implies
      (and
       (q1148215-linear-map-p ring source middle first)
       (q1148215-linear-map-p ring middle target second)
       (q1148215-module-element-p ring source value))
      (equal
       (q1148215-linear-apply
        ring source target
        (q1148215-linear-compose
         ring source middle target first second)
        value)
       (q1148215-linear-apply
        ring middle target second
        (q1148215-linear-apply
         ring source middle first value)))))))

(defun q1148215-module-category-p (ring)
  (and
   (q1148215-ring-p ring)
   (q1148215-linear-identity-laws-p ring)
   (q1148215-linear-compose-laws-p ring)))

;; Universal properties in the module category.

(defun-sk q1148215-module-terminal-arrow-unique-p
    (ring module terminal-module arrow)
  (forall (candidate)
    (implies
     (q1148215-linear-map-p
      ring module terminal-module candidate)
     (q1148215-linear-maps-pointwise-equal-p
      ring module terminal-module candidate arrow))))

(defun-sk q1148215-module-terminal-arrow-exists-p
    (ring module terminal-module)
  (exists (arrow)
    (and
     (q1148215-linear-map-p ring module terminal-module arrow)
     (q1148215-module-terminal-arrow-unique-p
      ring module terminal-module arrow))))

(defun-sk q1148215-module-terminal-universal-p
    (ring terminal-module)
  (forall (module)
    (implies
     (q1148215-module-p ring module)
     (q1148215-module-terminal-arrow-exists-p
      ring module terminal-module))))

(defun q1148215-module-terminal-p (ring terminal-module)
  (and
   (q1148215-module-p ring terminal-module)
   (q1148215-module-terminal-universal-p
    ring terminal-module)))

(defun-sk q1148215-module-initial-arrow-unique-p
    (ring initial-module module arrow)
  (forall (candidate)
    (implies
     (q1148215-linear-map-p
      ring initial-module module candidate)
     (q1148215-linear-maps-pointwise-equal-p
      ring initial-module module candidate arrow))))

(defun-sk q1148215-module-initial-arrow-exists-p
    (ring initial-module module)
  (exists (arrow)
    (and
     (q1148215-linear-map-p ring initial-module module arrow)
     (q1148215-module-initial-arrow-unique-p
      ring initial-module module arrow))))

(defun-sk q1148215-module-initial-universal-p
    (ring initial-module)
  (forall (module)
    (implies
     (q1148215-module-p ring module)
     (q1148215-module-initial-arrow-exists-p
      ring initial-module module))))

(defun q1148215-module-initial-p (ring initial-module)
  (and
   (q1148215-module-p ring initial-module)
   (q1148215-module-initial-universal-p
    ring initial-module)))

(defun-sk q1148215-module-product-factor-unique-p
    (ring left right product-module projection-left projection-right
     test-module left-map right-map factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-linear-map-p
       ring test-module product-module candidate)
      (q1148215-linear-maps-pointwise-equal-p
       ring test-module left
       (q1148215-linear-compose
        ring test-module product-module left
        candidate projection-left)
       left-map)
      (q1148215-linear-maps-pointwise-equal-p
       ring test-module right
       (q1148215-linear-compose
        ring test-module product-module right
        candidate projection-right)
       right-map))
     (q1148215-linear-maps-pointwise-equal-p
      ring test-module product-module candidate factor))))

(defun-sk q1148215-module-product-factor-exists-p
    (ring left right product-module projection-left projection-right
     test-module left-map right-map)
  (exists (factor)
    (and
     (q1148215-linear-map-p
      ring test-module product-module factor)
     (q1148215-linear-maps-pointwise-equal-p
      ring test-module left
      (q1148215-linear-compose
       ring test-module product-module left
       factor projection-left)
      left-map)
     (q1148215-linear-maps-pointwise-equal-p
      ring test-module right
      (q1148215-linear-compose
       ring test-module product-module right
       factor projection-right)
      right-map)
     (q1148215-module-product-factor-unique-p
      ring left right product-module
      projection-left projection-right
      test-module left-map right-map factor))))

(defun-sk q1148215-module-product-universal-p
    (ring left right product-module projection-left projection-right)
  (forall (test-module left-map right-map)
    (implies
     (and
      (q1148215-linear-map-p ring test-module left left-map)
      (q1148215-linear-map-p ring test-module right right-map))
     (q1148215-module-product-factor-exists-p
      ring left right product-module
      projection-left projection-right
      test-module left-map right-map))))

(defun q1148215-module-product-p
    (ring left right product-module projection-left projection-right)
  (and
   (q1148215-module-p ring left)
   (q1148215-module-p ring right)
   (q1148215-module-p ring product-module)
   (q1148215-linear-map-p
    ring product-module left projection-left)
   (q1148215-linear-map-p
    ring product-module right projection-right)
   (q1148215-module-product-universal-p
    ring left right product-module
    projection-left projection-right)))

(defun-sk q1148215-module-coproduct-factor-unique-p
    (ring left right coproduct-module injection-left injection-right
     test-module left-map right-map factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-linear-map-p
       ring coproduct-module test-module candidate)
      (q1148215-linear-maps-pointwise-equal-p
       ring left test-module
       (q1148215-linear-compose
        ring left coproduct-module test-module
        injection-left candidate)
       left-map)
      (q1148215-linear-maps-pointwise-equal-p
       ring right test-module
       (q1148215-linear-compose
        ring right coproduct-module test-module
        injection-right candidate)
       right-map))
     (q1148215-linear-maps-pointwise-equal-p
      ring coproduct-module test-module candidate factor))))

(defun-sk q1148215-module-coproduct-factor-exists-p
    (ring left right coproduct-module injection-left injection-right
     test-module left-map right-map)
  (exists (factor)
    (and
     (q1148215-linear-map-p
      ring coproduct-module test-module factor)
     (q1148215-linear-maps-pointwise-equal-p
      ring left test-module
      (q1148215-linear-compose
       ring left coproduct-module test-module
       injection-left factor)
      left-map)
     (q1148215-linear-maps-pointwise-equal-p
      ring right test-module
      (q1148215-linear-compose
       ring right coproduct-module test-module
       injection-right factor)
      right-map)
     (q1148215-module-coproduct-factor-unique-p
      ring left right coproduct-module
      injection-left injection-right
      test-module left-map right-map factor))))

(defun-sk q1148215-module-coproduct-universal-p
    (ring left right coproduct-module injection-left injection-right)
  (forall (test-module left-map right-map)
    (implies
     (and
      (q1148215-linear-map-p ring left test-module left-map)
      (q1148215-linear-map-p ring right test-module right-map))
     (q1148215-module-coproduct-factor-exists-p
      ring left right coproduct-module
      injection-left injection-right
      test-module left-map right-map))))

(defun q1148215-module-coproduct-p
    (ring left right coproduct-module injection-left injection-right)
  (and
   (q1148215-module-p ring left)
   (q1148215-module-p ring right)
   (q1148215-module-p ring coproduct-module)
   (q1148215-linear-map-p
    ring left coproduct-module injection-left)
   (q1148215-linear-map-p
    ring right coproduct-module injection-right)
   (q1148215-module-coproduct-universal-p
    ring left right coproduct-module
    injection-left injection-right)))

(defun-sk q1148215-module-equalizer-factor-unique-p
    (ring source equalizer-module equalizer-arrow
     test-module test-arrow factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-linear-map-p
       ring test-module equalizer-module candidate)
      (q1148215-linear-maps-pointwise-equal-p
       ring test-module source
       (q1148215-linear-compose
        ring test-module equalizer-module source
        candidate equalizer-arrow)
       test-arrow))
     (q1148215-linear-maps-pointwise-equal-p
      ring test-module equalizer-module candidate factor))))

(defun-sk q1148215-module-equalizer-factor-exists-p
    (ring source equalizer-module equalizer-arrow
     test-module test-arrow)
  (exists (factor)
    (and
     (q1148215-linear-map-p
      ring test-module equalizer-module factor)
     (q1148215-linear-maps-pointwise-equal-p
      ring test-module source
      (q1148215-linear-compose
       ring test-module equalizer-module source
       factor equalizer-arrow)
      test-arrow)
     (q1148215-module-equalizer-factor-unique-p
      ring source equalizer-module equalizer-arrow
      test-module test-arrow factor))))

(defun-sk q1148215-module-equalizer-universal-p
    (ring source target first second
     equalizer-module equalizer-arrow)
  (forall (test-module test-arrow)
    (implies
     (and
      (q1148215-linear-map-p
       ring test-module source test-arrow)
      (q1148215-linear-maps-pointwise-equal-p
       ring test-module target
       (q1148215-linear-compose
        ring test-module source target test-arrow first)
       (q1148215-linear-compose
        ring test-module source target test-arrow second)))
     (q1148215-module-equalizer-factor-exists-p
      ring source equalizer-module equalizer-arrow
      test-module test-arrow))))

(defun q1148215-module-equalizer-p
    (ring source target first second
     equalizer-module equalizer-arrow)
  (and
   (q1148215-linear-map-p ring source target first)
   (q1148215-linear-map-p ring source target second)
   (q1148215-module-p ring equalizer-module)
   (q1148215-linear-map-p
    ring equalizer-module source equalizer-arrow)
   (q1148215-linear-maps-pointwise-equal-p
    ring equalizer-module target
    (q1148215-linear-compose
     ring equalizer-module source target
     equalizer-arrow first)
    (q1148215-linear-compose
     ring equalizer-module source target
     equalizer-arrow second))
   (q1148215-module-equalizer-universal-p
    ring source target first second
    equalizer-module equalizer-arrow)))

(defun-sk q1148215-module-coequalizer-factor-unique-p
    (ring target coequalizer-module coequalizer-arrow
     test-module test-arrow factor)
  (forall (candidate)
    (implies
     (and
      (q1148215-linear-map-p
       ring coequalizer-module test-module candidate)
      (q1148215-linear-maps-pointwise-equal-p
       ring target test-module
       (q1148215-linear-compose
        ring target coequalizer-module test-module
        coequalizer-arrow candidate)
       test-arrow))
     (q1148215-linear-maps-pointwise-equal-p
      ring coequalizer-module test-module candidate factor))))

(defun-sk q1148215-module-coequalizer-factor-exists-p
    (ring target coequalizer-module coequalizer-arrow
     test-module test-arrow)
  (exists (factor)
    (and
     (q1148215-linear-map-p
      ring coequalizer-module test-module factor)
     (q1148215-linear-maps-pointwise-equal-p
      ring target test-module
      (q1148215-linear-compose
       ring target coequalizer-module test-module
       coequalizer-arrow factor)
      test-arrow)
     (q1148215-module-coequalizer-factor-unique-p
      ring target coequalizer-module coequalizer-arrow
      test-module test-arrow factor))))

(defun-sk q1148215-module-coequalizer-universal-p
    (ring source target first second
     coequalizer-module coequalizer-arrow)
  (forall (test-module test-arrow)
    (implies
     (and
      (q1148215-linear-map-p
       ring target test-module test-arrow)
      (q1148215-linear-maps-pointwise-equal-p
       ring source test-module
       (q1148215-linear-compose
        ring source target test-module first test-arrow)
       (q1148215-linear-compose
        ring source target test-module second test-arrow)))
     (q1148215-module-coequalizer-factor-exists-p
      ring target coequalizer-module coequalizer-arrow
      test-module test-arrow))))

(defun q1148215-module-coequalizer-p
    (ring source target first second
     coequalizer-module coequalizer-arrow)
  (and
   (q1148215-linear-map-p ring source target first)
   (q1148215-linear-map-p ring source target second)
   (q1148215-module-p ring coequalizer-module)
   (q1148215-linear-map-p
    ring target coequalizer-module coequalizer-arrow)
   (q1148215-linear-maps-pointwise-equal-p
    ring source coequalizer-module
    (q1148215-linear-compose
     ring source target coequalizer-module
     first coequalizer-arrow)
    (q1148215-linear-compose
     ring source target coequalizer-module
     second coequalizer-arrow))
   (q1148215-module-coequalizer-universal-p
    ring source target first second
    coequalizer-module coequalizer-arrow)))

;; Functors into ModuleCat, fullness, and faithfulness.

(defun-sk q1148215-functor-laws-p
    (category ring functor)
  (forall (a b c f g)
    (and
     (implies
      (q1148215-object-p category a)
      (and
       (q1148215-module-p
        ring (q1148215-functor-object functor a))
       (q1148215-linear-maps-pointwise-equal-p
        ring
        (q1148215-functor-object functor a)
        (q1148215-functor-object functor a)
        (q1148215-functor-morphism
         functor a a (q1148215-identity category a))
        (q1148215-linear-identity
         ring (q1148215-functor-object functor a)))))
     (implies
      (q1148215-hom-p category a b f)
      (q1148215-linear-map-p
       ring
       (q1148215-functor-object functor a)
       (q1148215-functor-object functor b)
       (q1148215-functor-morphism functor a b f)))
     (implies
      (and
       (q1148215-hom-p category a b f)
       (q1148215-hom-p category b c g))
      (q1148215-linear-maps-pointwise-equal-p
       ring
       (q1148215-functor-object functor a)
       (q1148215-functor-object functor c)
       (q1148215-functor-morphism
        functor a c
        (q1148215-compose category a b c f g))
       (q1148215-linear-compose
        ring
        (q1148215-functor-object functor a)
        (q1148215-functor-object functor b)
        (q1148215-functor-object functor c)
        (q1148215-functor-morphism functor a b f)
        (q1148215-functor-morphism functor b c g)))))))

(defun q1148215-functor-p (category ring functor)
  (and
   (q1148215-category-structure-p category)
   (q1148215-functor-structure-p functor)
   (q1148215-category-laws-p category)
   (q1148215-module-category-p ring)
   (q1148215-functor-laws-p category ring functor)))

(defun-sk q1148215-full-witness-exists-p
    (category ring functor source target linear-map)
  (exists (morphism)
    (and
     (q1148215-hom-p category source target morphism)
     (q1148215-linear-maps-pointwise-equal-p
      ring
      (q1148215-functor-object functor source)
      (q1148215-functor-object functor target)
      (q1148215-functor-morphism
       functor source target morphism)
      linear-map))))

(defun-sk q1148215-full-p (category ring functor)
  (forall (source target linear-map)
    (implies
     (and
      (q1148215-object-p category source)
      (q1148215-object-p category target)
      (q1148215-linear-map-p
       ring
       (q1148215-functor-object functor source)
       (q1148215-functor-object functor target)
       linear-map))
     (q1148215-full-witness-exists-p
      category ring functor source target linear-map))))

(defun-sk q1148215-faithful-p (category ring functor)
  (forall (source target left right)
    (implies
     (and
      (q1148215-hom-p category source target left)
      (q1148215-hom-p category source target right)
      (q1148215-linear-maps-pointwise-equal-p
       ring
       (q1148215-functor-object functor source)
       (q1148215-functor-object functor target)
       (q1148215-functor-morphism
        functor source target left)
       (q1148215-functor-morphism
        functor source target right)))
     (equal left right))))

;; For a functor between categories with finite limits, preserving terminal
;; objects, binary products, and equalizers is equivalent to preserving every
;; finite limit.  The dual initial/coproduct/coequalizer basis expresses
;; preservation of every finite colimit.

(defun-sk q1148215-preserves-terminal-objects-p
    (category ring functor)
  (forall (terminal-object)
    (implies
     (q1148215-terminal-object-p category terminal-object)
     (q1148215-module-terminal-p
      ring
      (q1148215-functor-object functor terminal-object)))))

(defun-sk q1148215-preserves-binary-products-p
    (category ring functor)
  (forall (left right product-object projection-left projection-right)
    (implies
     (q1148215-product-p
      category left right product-object
      projection-left projection-right)
     (q1148215-module-product-p
      ring
      (q1148215-functor-object functor left)
      (q1148215-functor-object functor right)
      (q1148215-functor-object functor product-object)
      (q1148215-functor-morphism
       functor product-object left projection-left)
      (q1148215-functor-morphism
       functor product-object right projection-right)))))

(defun-sk q1148215-preserves-equalizers-p
    (category ring functor)
  (forall (source target first second equalizer-object equalizer-arrow)
    (implies
     (q1148215-equalizer-p
      category source target first second
      equalizer-object equalizer-arrow)
     (q1148215-module-equalizer-p
      ring
      (q1148215-functor-object functor source)
      (q1148215-functor-object functor target)
      (q1148215-functor-morphism
       functor source target first)
      (q1148215-functor-morphism
       functor source target second)
      (q1148215-functor-object functor equalizer-object)
      (q1148215-functor-morphism
       functor equalizer-object source equalizer-arrow)))))

(defun q1148215-preserves-finite-limits-p
    (category ring functor)
  (and
   (q1148215-preserves-terminal-objects-p
    category ring functor)
   (q1148215-preserves-binary-products-p
    category ring functor)
   (q1148215-preserves-equalizers-p
    category ring functor)))

(defun-sk q1148215-preserves-initial-objects-p
    (category ring functor)
  (forall (initial-object)
    (implies
     (q1148215-initial-object-p category initial-object)
     (q1148215-module-initial-p
      ring
      (q1148215-functor-object functor initial-object)))))

(defun-sk q1148215-preserves-binary-coproducts-p
    (category ring functor)
  (forall (left right coproduct-object injection-left injection-right)
    (implies
     (q1148215-coproduct-p
      category left right coproduct-object
      injection-left injection-right)
     (q1148215-module-coproduct-p
      ring
      (q1148215-functor-object functor left)
      (q1148215-functor-object functor right)
      (q1148215-functor-object functor coproduct-object)
      (q1148215-functor-morphism
       functor left coproduct-object injection-left)
      (q1148215-functor-morphism
       functor right coproduct-object injection-right)))))

(defun-sk q1148215-preserves-coequalizers-p
    (category ring functor)
  (forall (source target first second coequalizer-object coequalizer-arrow)
    (implies
     (q1148215-coequalizer-p
      category source target first second
      coequalizer-object coequalizer-arrow)
     (q1148215-module-coequalizer-p
      ring
      (q1148215-functor-object functor source)
      (q1148215-functor-object functor target)
      (q1148215-functor-morphism
       functor source target first)
      (q1148215-functor-morphism
       functor source target second)
      (q1148215-functor-object functor coequalizer-object)
      (q1148215-functor-morphism
       functor target coequalizer-object coequalizer-arrow)))))

(defun q1148215-preserves-finite-colimits-p
    (category ring functor)
  (and
   (q1148215-preserves-initial-objects-p
    category ring functor)
   (q1148215-preserves-binary-coproducts-p
    category ring functor)
   (q1148215-preserves-coequalizers-p
    category ring functor)))

;; The ring and functor remain internal existential witnesses, as in the Lean
;; statement.  Their bundles carry the full carrier operations and both
;; functor maps explicitly.

(defun q1148215-embedding-witness-p
    (category ring functor)
  (and
   (q1148215-ring-p ring)
   (q1148215-module-category-p ring)
   (q1148215-functor-p category ring functor)
   (q1148215-full-p category ring functor)
   (q1148215-faithful-p category ring functor)
   (q1148215-preserves-finite-limits-p
    category ring functor)
   (q1148215-preserves-finite-colimits-p
    category ring functor)))

(defun-sk q1148215-embedding-witness-exists-p (category)
  (exists (ring functor)
    (q1148215-embedding-witness-p
     category ring functor)))

(defun-sk
    thousand-theorems-q1148215-mitchells-embedding-theorem-statement
    ()
  (forall (category)
    (implies
     (q1148215-abelian-category-p category)
     (q1148215-embedding-witness-exists-p category))))

(value-triple :itpeval-statement-checked)
:q
