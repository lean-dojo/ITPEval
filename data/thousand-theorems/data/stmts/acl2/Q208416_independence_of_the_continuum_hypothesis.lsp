;; Statement-only formalization of thousand-theorems corpus artifact Q208416
;; (thousand-theorems__acl2__Q208416), "Independence of the continuum
;; hypothesis": in the fixed first-order language of the Flypitch
;; formalization, neither its continuum-hypothesis sentence nor its negation
;; is derivable from its ZFC theory. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The fixed language has equality, one binary membership relation, constants
;; for the empty set and omega, binary ordered pairing, and unary powerset and
;; union functions. Variables are unbounded de Bruijn indices.

(defun q208416-var (index)
  (list 'q208416-var (nfix index)))

(defun q208416-empty ()
  (list 'q208416-empty))

(defun q208416-omega ()
  (list 'q208416-omega))

(defun q208416-pair (left right)
  (list 'q208416-pair left right))

(defun q208416-powerset (term)
  (list 'q208416-powerset term))

(defun q208416-union (term)
  (list 'q208416-union term))

(defun q208416-false ()
  (list 'q208416-false))

(defun q208416-equal (left right)
  (list 'q208416-equal left right))

(defun q208416-member (element set)
  (list 'q208416-member element set))

(defun q208416-implies (antecedent consequent)
  (list 'q208416-implies antecedent consequent))

(defun q208416-forall (body)
  (list 'q208416-forall body))

;; These are exactly the classical derived connectives used by the source.

(defun q208416-not (formula)
  (q208416-implies formula (q208416-false)))

(defun q208416-and (left right)
  (q208416-not
   (q208416-implies left (q208416-not right))))

(defun q208416-or (left right)
  (q208416-implies (q208416-not left) right))

(defun q208416-iff (left right)
  (q208416-and
   (q208416-implies left right)
   (q208416-implies right left)))

(defun q208416-exists (body)
  (q208416-not
   (q208416-forall (q208416-not body))))

(defun q208416-term-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((and
     (true-listp term)
     (equal (len term) 2)
     (equal (car term) 'q208416-var))
    (natp (cadr term)))
   ((and
     (true-listp term)
     (equal (len term) 1)
     (or
      (equal (car term) 'q208416-empty)
      (equal (car term) 'q208416-omega)))
    t)
   ((and
     (true-listp term)
     (equal (len term) 3)
     (equal (car term) 'q208416-pair))
    (and
     (q208416-term-p (cadr term))
     (q208416-term-p (caddr term))))
   ((and
     (true-listp term)
     (equal (len term) 2)
     (or
      (equal (car term) 'q208416-powerset)
      (equal (car term) 'q208416-union)))
    (q208416-term-p (cadr term)))
   (t nil)))

(defun q208416-formula-p (formula)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((and
     (true-listp formula)
     (equal (len formula) 1)
     (equal (car formula) 'q208416-false))
    t)
   ((and
     (true-listp formula)
     (equal (len formula) 3)
     (or
      (equal (car formula) 'q208416-equal)
      (equal (car formula) 'q208416-member)))
    (and
     (q208416-term-p (cadr formula))
     (q208416-term-p (caddr formula))))
   ((and
     (true-listp formula)
     (equal (len formula) 3)
     (equal (car formula) 'q208416-implies))
    (and
     (q208416-formula-p (cadr formula))
     (q208416-formula-p (caddr formula))))
   ((and
     (true-listp formula)
     (equal (len formula) 2)
     (equal (car formula) 'q208416-forall))
    (q208416-formula-p (cadr formula)))
   (t nil)))

;; Bounded formulas are the source's BOUNDED_FORMULA objects: every de
;; Bruijn index is below the number of available variables.

(defun q208416-bounded-term-p (depth term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((and
     (true-listp term)
     (equal (len term) 2)
     (equal (car term) 'q208416-var))
    (and
     (natp (cadr term))
     (< (cadr term) (nfix depth))))
   ((and
     (true-listp term)
     (equal (len term) 1)
     (or
      (equal (car term) 'q208416-empty)
      (equal (car term) 'q208416-omega)))
    t)
   ((and
     (true-listp term)
     (equal (len term) 3)
     (equal (car term) 'q208416-pair))
    (and
     (q208416-bounded-term-p depth (cadr term))
     (q208416-bounded-term-p depth (caddr term))))
   ((and
     (true-listp term)
     (equal (len term) 2)
     (or
      (equal (car term) 'q208416-powerset)
      (equal (car term) 'q208416-union)))
    (q208416-bounded-term-p depth (cadr term)))
   (t nil)))

(defun q208416-bounded-formula-p (depth formula)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((and
     (true-listp formula)
     (equal (len formula) 1)
     (equal (car formula) 'q208416-false))
    t)
   ((and
     (true-listp formula)
     (equal (len formula) 3)
     (or
      (equal (car formula) 'q208416-equal)
      (equal (car formula) 'q208416-member)))
    (and
     (q208416-bounded-term-p depth (cadr formula))
     (q208416-bounded-term-p depth (caddr formula))))
   ((and
     (true-listp formula)
     (equal (len formula) 3)
     (equal (car formula) 'q208416-implies))
    (and
     (q208416-bounded-formula-p depth (cadr formula))
     (q208416-bounded-formula-p depth (caddr formula))))
   ((and
     (true-listp formula)
     (equal (len formula) 2)
     (equal (car formula) 'q208416-forall))
    (q208416-bounded-formula-p
     (+ 1 (nfix depth))
     (cadr formula)))
   (t nil)))

;; Capture-avoiding lift and substitution are the operations appearing in the
;; source proof rules and in the collection and CH formulas.

(defun q208416-lift-term (term amount cutoff)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((and
     (consp term)
     (equal (car term) 'q208416-var))
    (if (<= (nfix cutoff) (nfix (cadr term)))
        (q208416-var (+ (nfix (cadr term)) (nfix amount)))
      (q208416-var (cadr term))))
   ((and
     (consp term)
     (equal (car term) 'q208416-pair))
    (q208416-pair
     (q208416-lift-term (cadr term) amount cutoff)
     (q208416-lift-term (caddr term) amount cutoff)))
   ((and
     (consp term)
     (equal (car term) 'q208416-powerset))
    (q208416-powerset
     (q208416-lift-term (cadr term) amount cutoff)))
   ((and
     (consp term)
     (equal (car term) 'q208416-union))
    (q208416-union
     (q208416-lift-term (cadr term) amount cutoff)))
   (t term)))

(defun q208416-lift-formula (formula amount cutoff)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((and
     (consp formula)
     (equal (car formula) 'q208416-equal))
    (q208416-equal
     (q208416-lift-term (cadr formula) amount cutoff)
     (q208416-lift-term (caddr formula) amount cutoff)))
   ((and
     (consp formula)
     (equal (car formula) 'q208416-member))
    (q208416-member
     (q208416-lift-term (cadr formula) amount cutoff)
     (q208416-lift-term (caddr formula) amount cutoff)))
   ((and
     (consp formula)
     (equal (car formula) 'q208416-implies))
    (q208416-implies
     (q208416-lift-formula (cadr formula) amount cutoff)
     (q208416-lift-formula (caddr formula) amount cutoff)))
   ((and
     (consp formula)
     (equal (car formula) 'q208416-forall))
    (q208416-forall
     (q208416-lift-formula
      (cadr formula) amount (+ 1 (nfix cutoff)))))
   (t formula)))

(defun q208416-substitute-term (term replacement index)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((and
     (consp term)
     (equal (car term) 'q208416-var))
    (let ((variable (nfix (cadr term)))
          (index (nfix index)))
      (cond
       ((< variable index)
        (q208416-var variable))
       ((< index variable)
        (q208416-var (- variable 1)))
       (t
        (q208416-lift-term replacement index 0)))))
   ((and
     (consp term)
     (equal (car term) 'q208416-pair))
    (q208416-pair
     (q208416-substitute-term (cadr term) replacement index)
     (q208416-substitute-term (caddr term) replacement index)))
   ((and
     (consp term)
     (equal (car term) 'q208416-powerset))
    (q208416-powerset
     (q208416-substitute-term (cadr term) replacement index)))
   ((and
     (consp term)
     (equal (car term) 'q208416-union))
    (q208416-union
     (q208416-substitute-term (cadr term) replacement index)))
   (t term)))

(defun q208416-substitute-formula (formula replacement index)
  (declare (xargs :measure (acl2-count formula)))
  (cond
   ((and
     (consp formula)
     (equal (car formula) 'q208416-equal))
    (q208416-equal
     (q208416-substitute-term
      (cadr formula) replacement index)
     (q208416-substitute-term
      (caddr formula) replacement index)))
   ((and
     (consp formula)
     (equal (car formula) 'q208416-member))
    (q208416-member
     (q208416-substitute-term
      (cadr formula) replacement index)
     (q208416-substitute-term
      (caddr formula) replacement index)))
   ((and
     (consp formula)
     (equal (car formula) 'q208416-implies))
    (q208416-implies
     (q208416-substitute-formula
      (cadr formula) replacement index)
     (q208416-substitute-formula
      (caddr formula) replacement index)))
   ((and
     (consp formula)
     (equal (car formula) 'q208416-forall))
    (q208416-forall
     (q208416-substitute-formula
      (cadr formula) replacement (+ 1 (nfix index)))))
   (t formula)))

(defun q208416-repeat-forall (count formula)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      formula
    (q208416-forall
     (q208416-repeat-forall (- (nfix count) 1) formula))))

;; Set-theoretic formula abbreviations from the fixed source language.

(defun q208416-subset-formula (left right)
  (q208416-forall
   (q208416-implies
    (q208416-member
     (q208416-var 0)
     (q208416-lift-term left 1 0))
    (q208416-member
     (q208416-var 0)
     (q208416-lift-term right 1 0)))))

(defun q208416-transitive-formula ()
  (q208416-forall
   (q208416-implies
    (q208416-member (q208416-var 0) (q208416-var 1))
    (q208416-subset-formula
     (q208416-var 0)
     (q208416-var 1)))))

(defun q208416-epsilon-trichotomy-formula ()
  (q208416-forall
   (q208416-implies
    (q208416-member (q208416-var 0) (q208416-var 1))
    (q208416-forall
     (q208416-implies
      (q208416-member (q208416-var 0) (q208416-var 2))
      (q208416-or
       (q208416-or
        (q208416-equal (q208416-var 1) (q208416-var 0))
        (q208416-member (q208416-var 1) (q208416-var 0)))
       (q208416-member (q208416-var 0) (q208416-var 1))))))))

(defun q208416-epsilon-well-founded-formula ()
  (q208416-forall
   (q208416-implies
    (q208416-subset-formula
     (q208416-var 0)
     (q208416-var 1))
    (q208416-implies
     (q208416-not
      (q208416-equal (q208416-var 0) (q208416-empty)))
     (q208416-exists
      (q208416-and
       (q208416-member (q208416-var 0) (q208416-var 1))
       (q208416-forall
        (q208416-implies
         (q208416-member (q208416-var 0) (q208416-var 2))
         (q208416-not
          (q208416-member
           (q208416-var 0)
           (q208416-var 1)))))))))))

(defun q208416-ordinal-formula ()
  (q208416-and
   (q208416-and
    (q208416-epsilon-trichotomy-formula)
    (q208416-epsilon-well-founded-formula))
   (q208416-transitive-formula)))

;; The eight fixed ZFC axioms used by the source.

(defun q208416-emptyset-axiom ()
  (q208416-forall
   (q208416-not
    (q208416-member (q208416-var 0) (q208416-empty)))))

(defun q208416-ordered-pairs-axiom ()
  (q208416-repeat-forall
   4
   (q208416-iff
    (q208416-equal
     (q208416-pair (q208416-var 3) (q208416-var 2))
     (q208416-pair (q208416-var 1) (q208416-var 0)))
    (q208416-and
     (q208416-equal (q208416-var 3) (q208416-var 1))
     (q208416-equal (q208416-var 2) (q208416-var 0))))))

(defun q208416-extensionality-axiom ()
  (q208416-repeat-forall
   2
   (q208416-implies
    (q208416-forall
     (q208416-iff
      (q208416-member (q208416-var 0) (q208416-var 2))
      (q208416-member (q208416-var 0) (q208416-var 1))))
    (q208416-equal (q208416-var 1) (q208416-var 0)))))

(defun q208416-union-axiom ()
  (q208416-repeat-forall
   2
   (q208416-iff
    (q208416-member
     (q208416-var 0)
     (q208416-union (q208416-var 1)))
    (q208416-exists
     (q208416-and
      (q208416-member (q208416-var 0) (q208416-var 2))
      (q208416-member (q208416-var 1) (q208416-var 0)))))))

(defun q208416-powerset-axiom ()
  (q208416-repeat-forall
   2
   (q208416-iff
    (q208416-member
     (q208416-var 0)
     (q208416-powerset (q208416-var 1)))
    (q208416-forall
     (q208416-implies
      (q208416-member (q208416-var 0) (q208416-var 1))
      (q208416-member (q208416-var 0) (q208416-var 2)))))))

(defun q208416-limit-property (ordinal)
  (q208416-and
   (q208416-member (q208416-empty) ordinal)
   (q208416-forall
    (q208416-implies
     (q208416-member
      (q208416-var 0)
      (q208416-lift-term ordinal 1 0))
     (q208416-exists
      (q208416-and
       (q208416-member
        (q208416-var 0)
        (q208416-lift-term ordinal 2 0))
       (q208416-member
        (q208416-var 1)
        (q208416-var 0))))))))

(defun q208416-infinity-axiom ()
  (q208416-and
   (q208416-limit-property (q208416-omega))
   (q208416-and
    (q208416-exists
     (q208416-and
      (q208416-ordinal-formula)
      (q208416-equal (q208416-omega) (q208416-var 0))))
    (q208416-forall
     (q208416-implies
      (q208416-ordinal-formula)
      (q208416-implies
       (q208416-limit-property (q208416-var 0))
       (q208416-subset-formula
        (q208416-omega)
        (q208416-var 0))))))))

(defun q208416-regularity-axiom ()
  (q208416-forall
   (q208416-implies
    (q208416-not
     (q208416-equal (q208416-var 0) (q208416-empty)))
    (q208416-exists
     (q208416-and
      (q208416-member (q208416-var 0) (q208416-var 1))
      (q208416-forall
       (q208416-implies
        (q208416-member (q208416-var 0) (q208416-var 2))
        (q208416-not
         (q208416-member
          (q208416-var 0)
          (q208416-var 1))))))))))

(defun q208416-chain-formula ()
  (q208416-repeat-forall
   2
   (q208416-implies
    (q208416-and
     (q208416-member (q208416-var 1) (q208416-var 2))
     (q208416-member (q208416-var 0) (q208416-var 2)))
    (q208416-or
     (q208416-subset-formula
      (q208416-var 1)
      (q208416-var 0))
     (q208416-subset-formula
      (q208416-var 0)
      (q208416-var 1))))))

(defun q208416-zorn-axiom ()
  (q208416-forall
   (q208416-implies
    (q208416-not
     (q208416-equal (q208416-var 0) (q208416-empty)))
    (q208416-implies
     (q208416-forall
      (q208416-implies
       (q208416-and
        (q208416-subset-formula
         (q208416-var 0)
         (q208416-var 1))
        (q208416-chain-formula))
       (q208416-member
        (q208416-union (q208416-var 0))
        (q208416-var 1))))
     (q208416-exists
      (q208416-and
       (q208416-member (q208416-var 0) (q208416-var 1))
       (q208416-forall
        (q208416-implies
         (q208416-member (q208416-var 0) (q208416-var 2))
         (q208416-implies
          (q208416-subset-formula
           (q208416-var 1)
           (q208416-var 0))
          (q208416-equal
           (q208416-var 1)
           (q208416-var 0)))))))))))

;; Strong collection is an unbounded schema over every natural arity and
;; every bounded formula with n+2 free variables.

(defun q208416-collection-axiom (parameter-count phi)
  (q208416-repeat-forall
   (+ 1 (nfix parameter-count))
   (q208416-implies
    (q208416-forall
     (q208416-implies
      (q208416-member (q208416-var 0) (q208416-var 1))
      (q208416-exists
       (q208416-lift-formula phi 1 2))))
    (q208416-exists
     (q208416-and
      (q208416-forall
       (q208416-implies
        (q208416-member (q208416-var 0) (q208416-var 2))
        (q208416-exists
         (q208416-and
          (q208416-member (q208416-var 0) (q208416-var 2))
          (q208416-lift-formula phi 2 2)))))
      (q208416-forall
       (q208416-implies
        (q208416-member (q208416-var 0) (q208416-var 1))
        (q208416-exists
         (q208416-and
          (q208416-member (q208416-var 0) (q208416-var 3))
          (q208416-substitute-formula
           (q208416-lift-formula phi 3 2)
           (q208416-var 1)
           0))))))))))

;; A finite witness records membership in the infinite ZFC theory without
;; turning the collection schema into a finite list.

(defun q208416-zfc-membership-witness-p (formula witness)
  (cond
   ((equal witness 'q208416-emptyset)
    (equal formula (q208416-emptyset-axiom)))
   ((equal witness 'q208416-ordered-pairs)
    (equal formula (q208416-ordered-pairs-axiom)))
   ((equal witness 'q208416-extensionality)
    (equal formula (q208416-extensionality-axiom)))
   ((equal witness 'q208416-union)
    (equal formula (q208416-union-axiom)))
   ((equal witness 'q208416-powerset)
    (equal formula (q208416-powerset-axiom)))
   ((equal witness 'q208416-infinity)
    (equal formula (q208416-infinity-axiom)))
   ((equal witness 'q208416-regularity)
    (equal formula (q208416-regularity-axiom)))
   ((equal witness 'q208416-zorn)
    (equal formula (q208416-zorn-axiom)))
   ((and
     (true-listp witness)
     (equal (len witness) 3)
     (equal (car witness) 'q208416-collection))
    (let ((parameter-count (cadr witness))
          (phi (caddr witness)))
      (and
       (natp parameter-count)
       (q208416-bounded-formula-p
        (+ 2 parameter-count) phi)
       (equal
        formula
        (q208416-collection-axiom parameter-count phi)))))
   (t nil)))

;; Context descriptors and their witnesses implement insertion and the image
;; of a context under one-variable lifting, exactly as in the source rules.

(defun q208416-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((equal context '(q208416-zfc)) t)
   ((and
     (true-listp context)
     (equal (len context) 3)
     (equal (car context) 'q208416-insert))
    (and
     (q208416-formula-p (cadr context))
     (q208416-context-p (caddr context))))
   ((and
     (true-listp context)
     (equal (len context) 2)
     (equal (car context) 'q208416-lift))
    (q208416-context-p (cadr context)))
   (t nil)))

(defun q208416-context-member-witness-p
    (context formula witness)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((equal context '(q208416-zfc))
    (q208416-zfc-membership-witness-p formula witness))
   ((and
     (consp context)
     (equal (car context) 'q208416-insert))
    (cond
     ((equal witness '(q208416-here))
      (equal formula (cadr context)))
     ((and
       (true-listp witness)
       (equal (len witness) 2)
       (equal (car witness) 'q208416-there))
      (q208416-context-member-witness-p
       (caddr context) formula (cadr witness)))
     (t nil)))
   ((and
     (consp context)
     (equal (car context) 'q208416-lift)
     (true-listp witness)
     (equal (len witness) 3)
     (equal (car witness) 'q208416-lifted))
    (let ((original (cadr witness))
          (prior-witness (caddr witness)))
      (and
       (equal
        formula
        (q208416-lift-formula original 1 0))
       (q208416-context-member-witness-p
        (cadr context) original prior-witness))))
   (t nil)))

;; This fuelled checker is a direct finite-tree presentation of the eight
;; constructors of Flypitch's PRF relation. ACL2's unbounded existential below
;; ranges over all finite proof trees; no proof is supplied in this file.

(defun q208416-proof-p-fuel
    (context conclusion proof fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      nil
    (let ((next-fuel (- (nfix fuel) 1)))
      (cond
       ((and
         (true-listp proof)
         (equal (len proof) 2)
         (equal (car proof) 'q208416-axiom))
        (q208416-context-member-witness-p
         context conclusion (cadr proof)))
       ((and
         (true-listp proof)
         (equal (len proof) 4)
         (equal (car proof) 'q208416-imp-intro))
        (let ((antecedent (cadr proof))
              (consequent (caddr proof))
              (subproof (cadddr proof)))
          (and
           (q208416-formula-p antecedent)
           (q208416-formula-p consequent)
           (equal
            conclusion
            (q208416-implies antecedent consequent))
           (q208416-proof-p-fuel
            (list 'q208416-insert antecedent context)
            consequent subproof next-fuel))))
       ((and
         (true-listp proof)
         (equal (len proof) 4)
         (equal (car proof) 'q208416-imp-elim))
        (let ((antecedent (cadr proof))
              (implication-proof (caddr proof))
              (antecedent-proof (cadddr proof)))
          (and
           (q208416-formula-p antecedent)
           (q208416-proof-p-fuel
            context
            (q208416-implies antecedent conclusion)
            implication-proof
            next-fuel)
           (q208416-proof-p-fuel
            context antecedent antecedent-proof next-fuel))))
       ((and
         (true-listp proof)
         (equal (len proof) 3)
         (equal (car proof) 'q208416-falsum-elim))
        (let ((formula (cadr proof))
              (subproof (caddr proof)))
          (and
           (q208416-formula-p formula)
           (equal conclusion formula)
           (q208416-proof-p-fuel
            (list
             'q208416-insert
             (q208416-not formula)
             context)
            (q208416-false)
            subproof
            next-fuel))))
       ((and
         (true-listp proof)
         (equal (len proof) 3)
         (equal (car proof) 'q208416-all-intro))
        (let ((body (cadr proof))
              (subproof (caddr proof)))
          (and
           (q208416-formula-p body)
           (equal conclusion (q208416-forall body))
           (q208416-proof-p-fuel
            (list 'q208416-lift context)
            body subproof next-fuel))))
       ((and
         (true-listp proof)
         (equal (len proof) 4)
         (equal (car proof) 'q208416-all-elim))
        (let ((body (cadr proof))
              (term (caddr proof))
              (subproof (cadddr proof)))
          (and
           (q208416-formula-p body)
           (q208416-term-p term)
           (equal
            conclusion
            (q208416-substitute-formula body term 0))
           (q208416-proof-p-fuel
            context
            (q208416-forall body)
            subproof
            next-fuel))))
       ((and
         (true-listp proof)
         (equal (len proof) 2)
         (equal (car proof) 'q208416-reflexivity))
        (let ((term (cadr proof)))
          (and
           (q208416-term-p term)
           (equal
            conclusion
            (q208416-equal term term)))))
       ((and
         (true-listp proof)
         (equal (len proof) 6)
         (equal (car proof) 'q208416-substitution))
        (let ((left (cadr proof))
              (right (caddr proof))
              (formula (cadddr proof))
              (equality-proof (car (cddddr proof)))
              (left-proof (cadr (cddddr proof))))
          (and
           (q208416-term-p left)
           (q208416-term-p right)
           (q208416-formula-p formula)
           (equal
            conclusion
            (q208416-substitute-formula formula right 0))
           (q208416-proof-p-fuel
            context
            (q208416-equal left right)
            equality-proof
            next-fuel)
           (q208416-proof-p-fuel
            context
            (q208416-substitute-formula formula left 0)
            left-proof
            next-fuel))))
       (t nil)))))

(defun q208416-proof-p (context conclusion proof)
  (and
   (q208416-context-p context)
   (q208416-formula-p conclusion)
   (q208416-proof-p-fuel
    context conclusion proof (+ 1 (acl2-count proof)))))

(defun-sk q208416-zfc-provable-p (formula)
  (exists (proof)
    (q208416-proof-p
     '(q208416-zfc) formula proof)))

;; The continuum hypothesis sentence is the exact source formula:
;; every ordinal x has cardinality at most omega or at least the powerset of
;; omega, with cardinal comparison expressed by partial surjections.

(defun q208416-is-function-formula ()
  (q208416-repeat-forall
   4
   (q208416-implies
    (q208416-and
     (q208416-member
      (q208416-pair (q208416-var 3) (q208416-var 1))
      (q208416-var 4))
     (q208416-member
      (q208416-pair (q208416-var 2) (q208416-var 0))
      (q208416-var 4)))
    (q208416-implies
     (q208416-equal (q208416-var 3) (q208416-var 2))
     (q208416-equal (q208416-var 1) (q208416-var 0))))))

(defun q208416-is-total-reversed-formula ()
  (q208416-forall
   (q208416-implies
    (q208416-member (q208416-var 0) (q208416-var 2))
    (q208416-exists
     (q208416-and
      (q208416-member (q208416-var 0) (q208416-var 4))
      (q208416-member
       (q208416-pair (q208416-var 1) (q208416-var 0))
       (q208416-var 2)))))))

(defun q208416-is-function-reversed-formula ()
  (q208416-and
   (q208416-is-function-formula)
   (q208416-is-total-reversed-formula)))

(defun q208416-at-most-formula ()
  (q208416-exists
   (q208416-exists
    (q208416-and
     (q208416-and
      (q208416-subset-formula
       (q208416-var 1)
       (q208416-var 3))
      (q208416-is-function-reversed-formula))
     (q208416-forall
      (q208416-implies
       (q208416-member (q208416-var 0) (q208416-var 3))
       (q208416-exists
        (q208416-and
         (q208416-member (q208416-var 0) (q208416-var 3))
         (q208416-member
          (q208416-pair (q208416-var 0) (q208416-var 1))
          (q208416-var 2))))))))))

(defun q208416-continuum-hypothesis-formula ()
  (q208416-forall
   (q208416-implies
    (q208416-ordinal-formula)
    (q208416-or
     (q208416-substitute-formula
      (q208416-at-most-formula)
      (q208416-omega)
      1)
     (q208416-substitute-formula
      (q208416-at-most-formula)
      (q208416-powerset (q208416-omega))
      0)))))

(defun thousand-theorems-q208416-independence-of-ch-statement ()
  (and
   (not
    (q208416-zfc-provable-p
     (q208416-continuum-hypothesis-formula)))
   (not
    (q208416-zfc-provable-p
     (q208416-not
      (q208416-continuum-hypothesis-formula))))))

(value-triple :itpeval-statement-checked)
:q
