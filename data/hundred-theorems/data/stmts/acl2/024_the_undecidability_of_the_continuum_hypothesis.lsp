;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__024, "The Undecidability of the Continuum
;; Hypothesis": every countable transitive set model of ZF has a proper
;; countable transitive ZF extension with exactly the same ambient ordinals;
;; if the original model satisfies choice, the extension satisfies ZFC.
;; Ambient membership is constrained by the ZF axioms, countability uses
;; membership-defined bijection graphs over the least inductive set, and the
;; extension model is internally existential. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Conservative interfaces for ambient set membership and for internal and
;; ambient satisfaction of first-order formulas in the language of sets.
(defstub ht024-ambient-set-p (object) t)
(defstub ht024-member-p (set element) t)
(defstub ht024-sat (model environment formula) t)
(defstub ht024-ambient-sat (environment formula) t)

(defun ht024-sat-p (model environment formula)
  (if (ht024-sat model environment formula) t nil))

(defun ht024-ambient-sat-p (environment formula)
  (if (ht024-ambient-sat environment formula) t nil))

;; Formulas use natural-numbered variables and the constructors
;; (:equal i j), (:member i j), (:not p), (:and p q), and (:forall i p).
(defun ht024-formula-p (formula)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((atom formula) nil)
   ((equal (car formula) :equal)
    (and (true-listp formula)
         (equal (len formula) 3)
         (natp (cadr formula))
         (natp (caddr formula))))
   ((equal (car formula) :member)
    (and (true-listp formula)
         (equal (len formula) 3)
         (natp (cadr formula))
         (natp (caddr formula))))
   ((equal (car formula) :not)
    (and (true-listp formula)
         (equal (len formula) 2)
         (ht024-formula-p (cadr formula))))
   ((equal (car formula) :and)
    (and (true-listp formula)
         (equal (len formula) 3)
         (ht024-formula-p (cadr formula))
         (ht024-formula-p (caddr formula))))
   ((equal (car formula) :forall)
    (and (true-listp formula)
         (equal (len formula) 3)
         (natp (cadr formula))
         (ht024-formula-p (caddr formula))))
   (t nil)))

(defun ht024-env-lookup (variable environment)
  (cdr (assoc-equal variable environment)))

(defun ht024-env-update (variable value environment)
  (acons variable value environment))

(defun ht024-bound-variable-p (variable bound)
  (if (consp bound)
      (or (equal variable (car bound))
          (ht024-bound-variable-p variable (cdr bound)))
    nil))

;; Every free parameter of a schema formula is assigned an element of MODEL.
(defun ht024-parameters-in-model-p
    (model formula environment bound)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((atom formula) nil)
   ((or (equal (car formula) :equal)
        (equal (car formula) :member))
    (and
     (or (ht024-bound-variable-p (cadr formula) bound)
         (ht024-member-p
          model
          (ht024-env-lookup (cadr formula) environment)))
     (or (ht024-bound-variable-p (caddr formula) bound)
         (ht024-member-p
          model
          (ht024-env-lookup (caddr formula) environment)))))
   ((equal (car formula) :not)
    (ht024-parameters-in-model-p
     model (cadr formula) environment bound))
   ((equal (car formula) :and)
    (and
     (ht024-parameters-in-model-p
      model (cadr formula) environment bound)
     (ht024-parameters-in-model-p
      model (caddr formula) environment bound)))
   ((equal (car formula) :forall)
    (ht024-parameters-in-model-p
     model
     (caddr formula)
     environment
     (cons (cadr formula) bound)))
   (t nil)))

;; Basic unbounded set predicates.
(defun-sk ht024-set-nonempty-p (set)
  (exists (element)
    (ht024-member-p set element)))

(defun-sk ht024-subset-p (left right)
  (forall (element)
    (implies
     (ht024-member-p left element)
     (ht024-member-p right element))))

(defun-sk ht024-set-equal-p (left right)
  (forall (element)
    (iff
     (ht024-member-p left element)
     (ht024-member-p right element))))

(defun-sk ht024-transitive-p (set)
  (forall (element member)
    (implies
     (and
      (ht024-member-p set element)
      (ht024-member-p element member))
     (ht024-member-p set member))))

;; Ambient ordinals are exactly the transitive sets whose membership relation
;; is a strict total well-order.
(defun-sk ht024-membership-strict-order-p (set)
  (forall (x y z)
    (and
     (implies
      (ht024-member-p set x)
      (not (ht024-member-p x x)))
     (implies
      (and
       (ht024-member-p set x)
       (ht024-member-p set y)
       (ht024-member-p set z)
       (ht024-member-p y x)
       (ht024-member-p z y))
      (ht024-member-p z x))
     (implies
      (and
       (ht024-member-p set x)
       (ht024-member-p set y)
       (not (equal x y)))
      (or
       (ht024-member-p y x)
       (ht024-member-p x y))))))

(defun-sk ht024-membership-least-p (subset least)
  (forall (other)
    (and
     (ht024-member-p subset least)
     (implies
      (ht024-member-p subset other)
      (or
       (equal least other)
       (ht024-member-p other least))))))

(defun-sk ht024-membership-least-exists-p (subset)
  (exists (least)
    (ht024-membership-least-p subset least)))

(defun-sk ht024-membership-well-founded-p (set)
  (forall (subset)
    (implies
     (and
      (ht024-subset-p subset set)
      (ht024-set-nonempty-p subset))
     (ht024-membership-least-exists-p subset))))

(defun ht024-ordinal-p (set)
  (and
   (ht024-ambient-set-p set)
   (ht024-transitive-p set)
   (ht024-membership-strict-order-p set)
   (ht024-membership-well-founded-p set)))

;; Tarskian recursion laws make HT024-SAT a genuine satisfaction relation.
(defun-sk ht024-all-members-satisfy-p
    (model environment variable body)
  (forall (value)
    (implies
     (ht024-member-p model value)
     (ht024-sat-p
      model
      (ht024-env-update variable value environment)
      body))))

(defun-sk ht024-satisfaction-equality-law-p ()
  (forall (model environment i j)
    (implies
     (and (natp i) (natp j))
     (equal
      (ht024-sat-p model environment (list :equal i j))
      (equal
       (ht024-env-lookup i environment)
       (ht024-env-lookup j environment))))))

(defun-sk ht024-satisfaction-membership-law-p ()
  (forall (model environment i j)
    (implies
     (and (natp i) (natp j))
     (equal
      (ht024-sat-p model environment (list :member i j))
      (if
       (ht024-member-p
        (ht024-env-lookup j environment)
        (ht024-env-lookup i environment))
       t nil)))))

(defun-sk ht024-satisfaction-negation-law-p ()
  (forall (model environment body)
    (implies
     (ht024-formula-p body)
     (equal
      (ht024-sat-p model environment (list :not body))
      (if (ht024-sat-p model environment body) nil t)))))

(defun-sk ht024-satisfaction-conjunction-law-p ()
  (forall (model environment left right)
    (implies
     (and
      (ht024-formula-p left)
      (ht024-formula-p right))
     (equal
      (ht024-sat-p model environment (list :and left right))
      (if
       (and
        (ht024-sat-p model environment left)
        (ht024-sat-p model environment right))
       t nil)))))

(defun-sk ht024-satisfaction-universal-law-p ()
  (forall (model environment variable body)
    (implies
     (and
      (natp variable)
      (ht024-formula-p body))
     (equal
      (ht024-sat-p
       model environment (list :forall variable body))
      (if
       (ht024-all-members-satisfy-p
        model environment variable body)
       t nil)))))

(defun ht024-satisfaction-laws-p ()
  (and
   (ht024-satisfaction-equality-law-p)
   (ht024-satisfaction-membership-law-p)
   (ht024-satisfaction-negation-law-p)
   (ht024-satisfaction-conjunction-law-p)
   (ht024-satisfaction-universal-law-p)))

;; The ambient satisfaction relation has the same Tarskian recursion, with
;; quantifiers ranging over every ambient set represented in the ACL2 domain.
(defun-sk ht024-ambient-all-satisfy-p
    (environment variable body)
  (forall (value)
    (implies
     (ht024-ambient-set-p value)
     (ht024-ambient-sat-p
      (ht024-env-update variable value environment)
      body))))

(defun-sk ht024-ambient-satisfaction-equality-law-p ()
  (forall (environment i j)
    (implies
     (and (natp i) (natp j))
     (equal
      (ht024-ambient-sat-p environment (list :equal i j))
      (equal
       (ht024-env-lookup i environment)
       (ht024-env-lookup j environment))))))

(defun-sk ht024-ambient-satisfaction-membership-law-p ()
  (forall (environment i j)
    (implies
     (and (natp i) (natp j))
     (equal
      (ht024-ambient-sat-p environment (list :member i j))
      (if
       (ht024-member-p
        (ht024-env-lookup j environment)
        (ht024-env-lookup i environment))
       t nil)))))

(defun-sk ht024-ambient-satisfaction-negation-law-p ()
  (forall (environment body)
    (implies
     (ht024-formula-p body)
     (equal
      (ht024-ambient-sat-p environment (list :not body))
      (if (ht024-ambient-sat-p environment body) nil t)))))

(defun-sk ht024-ambient-satisfaction-conjunction-law-p ()
  (forall (environment left right)
    (implies
     (and
      (ht024-formula-p left)
      (ht024-formula-p right))
     (equal
      (ht024-ambient-sat-p environment (list :and left right))
      (if
       (and
        (ht024-ambient-sat-p environment left)
        (ht024-ambient-sat-p environment right))
       t nil)))))

(defun-sk ht024-ambient-satisfaction-universal-law-p ()
  (forall (environment variable body)
    (implies
     (and
      (natp variable)
      (ht024-formula-p body))
     (equal
      (ht024-ambient-sat-p
       environment (list :forall variable body))
      (if
       (ht024-ambient-all-satisfy-p environment variable body)
       t nil)))))

(defun ht024-ambient-satisfaction-laws-p ()
  (and
   (ht024-ambient-satisfaction-equality-law-p)
   (ht024-ambient-satisfaction-membership-law-p)
   (ht024-ambient-satisfaction-negation-law-p)
   (ht024-ambient-satisfaction-conjunction-law-p)
   (ht024-ambient-satisfaction-universal-law-p)))

;; Extensionality.
(defun-sk ht024-same-internal-members-p (model left right)
  (forall (element)
    (implies
     (ht024-member-p model element)
     (iff
      (ht024-member-p left element)
      (ht024-member-p right element)))))

(defun-sk ht024-zf-extensionality-p (model)
  (forall (left right)
    (implies
     (and
      (ht024-member-p model left)
      (ht024-member-p model right)
      (ht024-same-internal-members-p model left right))
     (equal left right))))

;; Empty set.
(defun-sk ht024-empty-set-p (model empty)
  (forall (element)
    (and
     (ht024-member-p model empty)
     (implies
      (ht024-member-p model element)
      (not (ht024-member-p empty element))))))

(defun-sk ht024-zf-empty-set-p (model)
  (exists (empty)
    (ht024-empty-set-p model empty)))

;; Pairing.
(defun-sk ht024-pair-set-p (model pair left right)
  (forall (element)
    (and
     (ht024-member-p model pair)
     (implies
      (ht024-member-p model element)
      (iff
       (ht024-member-p pair element)
       (or (equal element left)
           (equal element right)))))))

(defun-sk ht024-pair-set-exists-p (model left right)
  (exists (pair)
    (ht024-pair-set-p model pair left right)))

(defun-sk ht024-zf-pairing-p (model)
  (forall (left right)
    (implies
     (and
      (ht024-member-p model left)
      (ht024-member-p model right))
     (ht024-pair-set-exists-p model left right))))

;; Union.
(defun-sk ht024-in-member-of-p (element set)
  (exists (member)
    (and
     (ht024-member-p set member)
     (ht024-member-p member element))))

(defun-sk ht024-union-set-p (model union set)
  (forall (element)
    (and
     (ht024-member-p model union)
     (implies
      (ht024-member-p model element)
      (iff
       (ht024-member-p union element)
       (ht024-in-member-of-p element set))))))

(defun-sk ht024-union-set-exists-p (model set)
  (exists (union)
    (ht024-union-set-p model union set)))

(defun-sk ht024-zf-union-p (model)
  (forall (set)
    (implies
     (ht024-member-p model set)
     (ht024-union-set-exists-p model set))))

;; Power set, with subset interpreted inside the model.
(defun-sk ht024-internal-subset-p (model left right)
  (forall (element)
    (implies
     (and
      (ht024-member-p model element)
      (ht024-member-p left element))
     (ht024-member-p right element))))

(defun-sk ht024-power-set-p (model power set)
  (forall (candidate)
    (and
     (ht024-member-p model power)
     (implies
      (ht024-member-p model candidate)
      (iff
       (ht024-member-p power candidate)
       (ht024-internal-subset-p model candidate set))))))

(defun-sk ht024-power-set-exists-p (model set)
  (exists (power)
    (ht024-power-set-p model power set)))

(defun-sk ht024-zf-power-set-p (model)
  (forall (set)
    (implies
     (ht024-member-p model set)
     (ht024-power-set-exists-p model set))))

;; Infinity.
(defun-sk ht024-successor-set-p (model successor set)
  (forall (element)
    (and
     (ht024-member-p model successor)
     (implies
      (ht024-member-p model element)
      (iff
       (ht024-member-p successor element)
       (or
        (ht024-member-p set element)
        (equal element set)))))))

(defun-sk ht024-successor-in-set-exists-p (model inductive set)
  (exists (successor)
    (and
     (ht024-member-p inductive successor)
     (ht024-successor-set-p model successor set))))

(defun-sk ht024-inductive-set-p (model inductive)
  (forall (set)
    (and
     (ht024-member-p model inductive)
     (implies
      (ht024-member-p inductive set)
      (ht024-successor-in-set-exists-p model inductive set)))))

(defun-sk ht024-empty-member-exists-p (model set)
  (exists (empty)
    (and
     (ht024-member-p set empty)
     (ht024-empty-set-p model empty))))

(defun-sk ht024-zf-infinity-p (model)
  (exists (inductive)
    (and
     (ht024-member-p model inductive)
     (ht024-empty-member-exists-p model inductive)
     (ht024-inductive-set-p model inductive))))

;; Foundation.
(defun-sk ht024-foundation-minimal-p (set minimal)
  (forall (element)
    (and
     (ht024-member-p set minimal)
     (implies
      (ht024-member-p set element)
      (not (ht024-member-p minimal element))))))

(defun-sk ht024-foundation-minimal-exists-p (set)
  (exists (minimal)
    (ht024-foundation-minimal-p set minimal)))

(defun-sk ht024-zf-foundation-p (model)
  (forall (set)
    (implies
     (and
      (ht024-member-p model set)
      (ht024-set-nonempty-p set))
     (ht024-foundation-minimal-exists-p set))))

;; Separation schema. Variable 0 is the element selected from SET.
(defun-sk ht024-separated-set-p
    (model result set formula environment)
  (forall (element)
    (and
     (ht024-member-p model result)
     (implies
      (ht024-member-p model element)
      (iff
       (ht024-member-p result element)
       (and
        (ht024-member-p set element)
        (ht024-sat-p
         model
         (ht024-env-update 0 element environment)
         formula)))))))

(defun-sk ht024-separated-set-exists-p
    (model set formula environment)
  (exists (result)
    (ht024-separated-set-p
     model result set formula environment)))

(defun-sk ht024-zf-separation-p (model)
  (forall (set formula environment)
    (implies
     (and
      (ht024-member-p model set)
      (ht024-formula-p formula)
      (ht024-parameters-in-model-p
       model formula environment (list 0)))
     (ht024-separated-set-exists-p
      model set formula environment))))

;; Replacement schema. Variables 0 and 1 are respectively the argument and
;; the uniquely specified value.
(defun ht024-replacement-instance-sat-p
    (model environment formula argument value)
  (ht024-sat-p
   model
   (ht024-env-update
    1 value
    (ht024-env-update 0 argument environment))
   formula))

(defun-sk ht024-replacement-value-exists-p
    (model environment formula argument)
  (exists (value)
    (and
     (ht024-member-p model value)
     (ht024-replacement-instance-sat-p
      model environment formula argument value))))

(defun-sk ht024-replacement-value-unique-p
    (model environment formula argument)
  (forall (left right)
    (implies
     (and
      (ht024-member-p model left)
      (ht024-member-p model right)
      (ht024-replacement-instance-sat-p
       model environment formula argument left)
      (ht024-replacement-instance-sat-p
       model environment formula argument right))
     (equal left right))))

(defun-sk ht024-formula-functional-on-p
    (model set formula environment)
  (forall (argument)
    (implies
     (ht024-member-p set argument)
     (and
      (ht024-replacement-value-exists-p
       model environment formula argument)
      (ht024-replacement-value-unique-p
       model environment formula argument)))))

(defun-sk ht024-replacement-image-member-p
    (model set formula environment value)
  (exists (argument)
    (and
     (ht024-member-p set argument)
     (ht024-replacement-instance-sat-p
      model environment formula argument value))))

(defun-sk ht024-replacement-set-p
    (model result set formula environment)
  (forall (value)
    (and
     (ht024-member-p model result)
     (implies
      (ht024-member-p model value)
      (iff
       (ht024-member-p result value)
       (ht024-replacement-image-member-p
        model set formula environment value))))))

(defun-sk ht024-replacement-set-exists-p
    (model set formula environment)
  (exists (result)
    (ht024-replacement-set-p
     model result set formula environment)))

(defun-sk ht024-zf-replacement-p (model)
  (forall (set formula environment)
    (implies
     (and
      (ht024-member-p model set)
      (ht024-formula-p formula)
      (ht024-parameters-in-model-p
       model formula environment (list 0 1))
      (ht024-formula-functional-on-p
       model set formula environment))
     (ht024-replacement-set-exists-p
      model set formula environment))))

(defun ht024-satisfies-zf-p (model)
  (and
   (ht024-zf-extensionality-p model)
   (ht024-zf-empty-set-p model)
   (ht024-zf-pairing-p model)
   (ht024-zf-union-p model)
   (ht024-zf-power-set-p model)
   (ht024-zf-infinity-p model)
   (ht024-zf-foundation-p model)
   (ht024-zf-separation-p model)
   (ht024-zf-replacement-p model)))

;; AC is represented by its well-ordering form, equivalent over ZF.
;; Kuratowski ordered pairs and relations are decoded from membership.
(defun-sk ht024-singleton-p (singleton element)
  (forall (member)
    (iff
     (ht024-member-p singleton member)
     (equal member element))))

(defun-sk ht024-unordered-pair-p (pair left right)
  (forall (member)
    (iff
     (ht024-member-p pair member)
     (or
      (equal member left)
      (equal member right)))))

(defun-sk ht024-ordered-pair-p (pair left right)
  (exists (singleton unordered)
    (and
     (ht024-singleton-p singleton left)
     (ht024-unordered-pair-p unordered left right)
     (ht024-unordered-pair-p pair singleton unordered))))

(defun-sk ht024-relation-holds-p (relation left right)
  (exists (pair)
    (and
     (ht024-member-p relation pair)
     (ht024-ordered-pair-p pair left right))))

(defun-sk ht024-relation-entry-on-p (set entry)
  (exists (left right)
    (and
     (ht024-member-p set left)
     (ht024-member-p set right)
     (ht024-ordered-pair-p entry left right))))

(defun-sk ht024-relation-on-p (relation set)
  (forall (entry)
    (implies
     (ht024-member-p relation entry)
     (ht024-relation-entry-on-p set entry))))

(defun-sk ht024-strict-total-order-p (relation set)
  (forall (x y z)
    (and
     (implies
      (ht024-member-p set x)
      (not (ht024-relation-holds-p relation x x)))
     (implies
      (and
       (ht024-member-p set x)
       (ht024-member-p set y)
       (ht024-member-p set z)
       (ht024-relation-holds-p relation x y)
       (ht024-relation-holds-p relation y z))
      (ht024-relation-holds-p relation x z))
     (implies
      (and
       (ht024-member-p set x)
       (ht024-member-p set y)
       (not (equal x y)))
      (or
       (ht024-relation-holds-p relation x y)
       (ht024-relation-holds-p relation y x))))))

(defun-sk ht024-relation-least-p (relation subset least)
  (forall (other)
    (and
     (ht024-member-p subset least)
     (implies
      (ht024-member-p subset other)
      (or
       (equal least other)
       (ht024-relation-holds-p relation least other))))))

(defun-sk ht024-relation-least-exists-p (relation subset)
  (exists (least)
    (ht024-relation-least-p relation subset least)))

(defun-sk ht024-internal-well-founded-p (model relation set)
  (forall (subset)
    (implies
     (and
      (ht024-member-p model subset)
      (ht024-internal-subset-p model subset set)
      (ht024-set-nonempty-p subset))
     (ht024-relation-least-exists-p relation subset))))

(defun ht024-well-orders-p (model relation set)
  (and
   (ht024-member-p model relation)
   (ht024-relation-on-p relation set)
   (ht024-strict-total-order-p relation set)
   (ht024-internal-well-founded-p model relation set)))

(defun-sk ht024-well-order-exists-p (model set)
  (exists (relation)
    (ht024-well-orders-p model relation set)))

(defun-sk ht024-satisfies-ac-p (model)
  (forall (set)
    (implies
     (ht024-member-p model set)
     (ht024-well-order-exists-p model set))))

(defun ht024-satisfies-zfc-p (model)
  (and
   (ht024-satisfies-zf-p model)
   (ht024-satisfies-ac-p model)))

;; Ambient Isabelle/ZF semantics. ACL2 values satisfying HT024-AMBIENT-SET-P
;; form the set universe; the membership relation is typed and satisfies ZF.
(defun-sk ht024-ambient-membership-typed-p ()
  (forall (set element)
    (implies
     (ht024-member-p set element)
     (and
      (ht024-ambient-set-p set)
      (ht024-ambient-set-p element)))))

(defun-sk ht024-ambient-extensionality-p ()
  (forall (left right)
    (implies
     (and
      (ht024-ambient-set-p left)
      (ht024-ambient-set-p right)
      (ht024-set-equal-p left right))
     (equal left right))))

(defun-sk ht024-ambient-empty-p (empty)
  (forall (element)
    (and
     (ht024-ambient-set-p empty)
     (not (ht024-member-p empty element)))))

(defun-sk ht024-ambient-empty-exists-p ()
  (exists (empty)
    (ht024-ambient-empty-p empty)))

(defun-sk ht024-ambient-pair-p (pair left right)
  (forall (element)
    (and
     (ht024-ambient-set-p pair)
     (iff
      (ht024-member-p pair element)
      (or
       (equal element left)
       (equal element right))))))

(defun-sk ht024-ambient-pair-exists-p (left right)
  (exists (pair)
    (ht024-ambient-pair-p pair left right)))

(defun-sk ht024-ambient-pairing-p ()
  (forall (left right)
    (implies
     (and
      (ht024-ambient-set-p left)
      (ht024-ambient-set-p right))
     (ht024-ambient-pair-exists-p left right))))

(defun-sk ht024-ambient-union-p (union set)
  (forall (element)
    (and
     (ht024-ambient-set-p union)
     (iff
      (ht024-member-p union element)
      (ht024-in-member-of-p element set)))))

(defun-sk ht024-ambient-union-exists-p (set)
  (exists (union)
    (ht024-ambient-union-p union set)))

(defun-sk ht024-ambient-union-axiom-p ()
  (forall (set)
    (implies
     (ht024-ambient-set-p set)
     (ht024-ambient-union-exists-p set))))

(defun-sk ht024-ambient-power-p (power set)
  (forall (candidate)
    (and
     (ht024-ambient-set-p power)
     (implies
      (ht024-ambient-set-p candidate)
      (iff
       (ht024-member-p power candidate)
       (ht024-subset-p candidate set))))))

(defun-sk ht024-ambient-power-exists-p (set)
  (exists (power)
    (ht024-ambient-power-p power set)))

(defun-sk ht024-ambient-power-axiom-p ()
  (forall (set)
    (implies
     (ht024-ambient-set-p set)
     (ht024-ambient-power-exists-p set))))

(defun-sk ht024-ambient-successor-p (successor set)
  (forall (element)
    (and
     (ht024-ambient-set-p successor)
     (iff
      (ht024-member-p successor element)
      (or
       (ht024-member-p set element)
       (equal element set))))))

(defun-sk ht024-ambient-successor-in-p (inductive set)
  (exists (successor)
    (and
     (ht024-member-p inductive successor)
     (ht024-ambient-successor-p successor set))))

(defun-sk ht024-ambient-empty-member-p (inductive)
  (exists (empty)
    (and
     (ht024-ambient-empty-p empty)
     (ht024-member-p inductive empty))))

(defun-sk ht024-ambient-inductive-p (inductive)
  (forall (set)
    (and
     (ht024-ambient-set-p inductive)
     (ht024-ambient-empty-member-p inductive)
     (implies
      (ht024-member-p inductive set)
      (ht024-ambient-successor-in-p inductive set)))))

(defun-sk ht024-ambient-infinity-p ()
  (exists (inductive)
    (ht024-ambient-inductive-p inductive)))

(defun-sk ht024-ambient-foundation-p ()
  (forall (set)
    (implies
     (and
      (ht024-ambient-set-p set)
      (ht024-set-nonempty-p set))
     (ht024-foundation-minimal-exists-p set))))

;; Ambient Separation, with variable 0 bound to the selected element.
(defun-sk ht024-ambient-separated-set-p
    (result set formula environment)
  (forall (element)
    (and
     (ht024-ambient-set-p result)
     (iff
      (ht024-member-p result element)
      (and
       (ht024-member-p set element)
       (ht024-ambient-sat-p
        (ht024-env-update 0 element environment)
        formula))))))

(defun-sk ht024-ambient-separated-set-exists-p
    (set formula environment)
  (exists (result)
    (ht024-ambient-separated-set-p
     result set formula environment)))

(defun-sk ht024-ambient-separation-p ()
  (forall (set formula environment)
    (implies
     (and
      (ht024-ambient-set-p set)
      (ht024-formula-p formula))
     (ht024-ambient-separated-set-exists-p
      set formula environment))))

;; Ambient Replacement. Variables 0 and 1 denote argument and value.
(defun ht024-ambient-replacement-instance-p
    (environment formula argument value)
  (ht024-ambient-sat-p
   (ht024-env-update
    1 value
    (ht024-env-update 0 argument environment))
   formula))

(defun-sk ht024-ambient-replacement-value-exists-p
    (environment formula argument)
  (exists (value)
    (and
     (ht024-ambient-set-p value)
     (ht024-ambient-replacement-instance-p
      environment formula argument value))))

(defun-sk ht024-ambient-replacement-value-unique-p
    (environment formula argument)
  (forall (left right)
    (implies
     (and
      (ht024-ambient-set-p left)
      (ht024-ambient-set-p right)
      (ht024-ambient-replacement-instance-p
       environment formula argument left)
      (ht024-ambient-replacement-instance-p
       environment formula argument right))
     (equal left right))))

(defun-sk ht024-ambient-formula-functional-on-p
    (set formula environment)
  (forall (argument)
    (implies
     (ht024-member-p set argument)
     (and
      (ht024-ambient-replacement-value-exists-p
       environment formula argument)
      (ht024-ambient-replacement-value-unique-p
       environment formula argument)))))

(defun-sk ht024-ambient-replacement-image-member-p
    (set formula environment value)
  (exists (argument)
    (and
     (ht024-member-p set argument)
     (ht024-ambient-replacement-instance-p
      environment formula argument value))))

(defun-sk ht024-ambient-replacement-set-p
    (result set formula environment)
  (forall (value)
    (and
     (ht024-ambient-set-p result)
     (implies
      (ht024-ambient-set-p value)
      (iff
       (ht024-member-p result value)
       (ht024-ambient-replacement-image-member-p
        set formula environment value))))))

(defun-sk ht024-ambient-replacement-set-exists-p
    (set formula environment)
  (exists (result)
    (ht024-ambient-replacement-set-p
     result set formula environment)))

(defun-sk ht024-ambient-replacement-p ()
  (forall (set formula environment)
    (implies
     (and
      (ht024-ambient-set-p set)
      (ht024-formula-p formula)
      (ht024-ambient-formula-functional-on-p
       set formula environment))
     (ht024-ambient-replacement-set-exists-p
      set formula environment))))

(defun ht024-ambient-zf-p ()
  (and
   (ht024-ambient-membership-typed-p)
   (ht024-ambient-satisfaction-laws-p)
   (ht024-ambient-extensionality-p)
   (ht024-ambient-empty-exists-p)
   (ht024-ambient-pairing-p)
   (ht024-ambient-union-axiom-p)
   (ht024-ambient-power-axiom-p)
   (ht024-ambient-infinity-p)
   (ht024-ambient-foundation-p)
   (ht024-ambient-separation-p)
   (ht024-ambient-replacement-p)))

;; The natural numbers object is the least ambient inductive set.
(defun-sk ht024-least-inductive-p (omega)
  (forall (inductive)
    (implies
     (ht024-ambient-inductive-p inductive)
     (ht024-subset-p omega inductive))))

(defun ht024-omega-p (omega)
  (and
   (ht024-ambient-inductive-p omega)
   (ht024-least-inductive-p omega)))

;; A bijection is an ambient membership-defined graph of Kuratowski pairs.
(defun-sk ht024-graph-entry-on-p (entry domain codomain)
  (exists (argument value)
    (and
     (ht024-member-p domain argument)
     (ht024-member-p codomain value)
     (ht024-ordered-pair-p entry argument value))))

(defun-sk ht024-graph-on-p (graph domain codomain)
  (forall (entry)
    (and
     (ht024-ambient-set-p graph)
     (implies
      (ht024-member-p graph entry)
      (ht024-graph-entry-on-p entry domain codomain)))))

(defun-sk ht024-graph-value-exists-p
    (graph codomain argument)
  (exists (value)
    (and
     (ht024-member-p codomain value)
     (ht024-relation-holds-p graph argument value))))

(defun-sk ht024-graph-total-p (graph domain codomain)
  (forall (argument)
    (implies
     (ht024-member-p domain argument)
     (ht024-graph-value-exists-p graph codomain argument))))

(defun-sk ht024-graph-single-valued-p (graph domain codomain)
  (forall (argument left right)
    (implies
     (and
      (ht024-member-p domain argument)
      (ht024-member-p codomain left)
      (ht024-member-p codomain right)
      (ht024-relation-holds-p graph argument left)
      (ht024-relation-holds-p graph argument right))
     (equal left right))))

(defun-sk ht024-graph-injective-p (graph domain codomain)
  (forall (left right value)
    (implies
     (and
      (ht024-member-p domain left)
      (ht024-member-p domain right)
      (ht024-member-p codomain value)
      (ht024-relation-holds-p graph left value)
      (ht024-relation-holds-p graph right value))
     (equal left right))))

(defun-sk ht024-graph-preimage-exists-p
    (graph domain value)
  (exists (argument)
    (and
     (ht024-member-p domain argument)
     (ht024-relation-holds-p graph argument value))))

(defun-sk ht024-graph-surjective-p (graph domain codomain)
  (forall (value)
    (implies
     (ht024-member-p codomain value)
     (ht024-graph-preimage-exists-p graph domain value))))

(defun ht024-bijection-graph-p (graph domain codomain)
  (and
   (ht024-ambient-set-p domain)
   (ht024-ambient-set-p codomain)
   (ht024-graph-on-p graph domain codomain)
   (ht024-graph-total-p graph domain codomain)
   (ht024-graph-single-valued-p graph domain codomain)
   (ht024-graph-injective-p graph domain codomain)
   (ht024-graph-surjective-p graph domain codomain)))

(defun-sk ht024-equinumerous-with-nat-p (model)
  (exists (omega graph)
    (and
     (ht024-omega-p omega)
     (ht024-bijection-graph-p graph omega model))))

(defun-sk ht024-same-ordinals-p (left right)
  (forall (ordinal)
    (implies
     (ht024-ordinal-p ordinal)
     (iff
      (ht024-member-p left ordinal)
      (ht024-member-p right ordinal)))))

;; This DEFUN-SK restores the source's internal existential quantifier over N.
(defun-sk ht024-extension-exists-p (model)
  (exists (extension)
    (and
     (ht024-subset-p model extension)
     (not (ht024-set-equal-p model extension))
     (ht024-equinumerous-with-nat-p extension)
     (ht024-transitive-p extension)
     (ht024-satisfies-zf-p extension)
     (ht024-same-ordinals-p model extension)
     (implies
      (ht024-satisfies-ac-p model)
      (ht024-satisfies-zfc-p extension)))))

(defun hundred-theorems-024-extensions-of-ctms-statement (model)
  (implies
   (and
    (ht024-ambient-zf-p)
    (ht024-satisfaction-laws-p)
    (ht024-ambient-set-p model)
    (ht024-equinumerous-with-nat-p model)
    (ht024-transitive-p model)
    (ht024-satisfies-zf-p model))
   (ht024-extension-exists-p model)))

(value-triple :itpeval-statement-checked)
:q
