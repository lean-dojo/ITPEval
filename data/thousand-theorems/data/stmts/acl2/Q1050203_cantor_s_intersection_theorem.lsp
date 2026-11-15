;; Statement-only formalization of thousand-theorems corpus artifact Q1050203,
;; "Cantor's intersection theorem": a nonempty downward-directed family of
;; nonempty compact closed subsets of an arbitrary topological space has
;; nonempty total intersection. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Sets, families of sets, and the topology are characteristic function
;; objects over an arbitrary carrier. FN-EQUAL supplies unbounded universal
;; quantification; its negation supplies internal existential witnesses.

(defun q1050203-quoted (object)
  (list 'quote object))

(defun q1050203-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1050203-term-list (cdr terms)))
    (q1050203-quoted nil)))

(defun q1050203-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1050203-term-list arguments)))

(defun q1050203-static-apply-term (function arguments)
  (q1050203-apply-term
   (q1050203-quoted function)
   arguments))

(defun q1050203-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1050203-and-terms (cdr terms))
       (q1050203-quoted nil))
    (q1050203-quoted t)))

(defun q1050203-not-term (term)
  (list
   'if
   term
   (q1050203-quoted nil)
   (q1050203-quoted t)))

(defun q1050203-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1050203-quoted t)))

(defun q1050203-iff-term (left right)
  (list
   'if
   left
   (list 'if right
         (q1050203-quoted t)
         (q1050203-quoted nil))
   (list 'if right
         (q1050203-quoted nil)
         (q1050203-quoted t))))

(defun q1050203-true-function (formals)
  (list 'lambda formals (q1050203-quoted t)))

(defun q1050203-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1050203-set-subset-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (q1050203-static-apply-term carrier '(x))
      (q1050203-static-apply-term left '(x))))
    (q1050203-static-apply-term right '(x)))))

(defun q1050203-set-subset-p
    (carrier left right)
  (let ((condition
         (q1050203-set-subset-function
          carrier left right))
        (always-true
         (q1050203-true-function '(x))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp left)
     (tamep-functionp right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1050203-set-subset-p carrier set carrier)))

(defun q1050203-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1050203-implies-term
    (q1050203-static-apply-term carrier '(x))
    (q1050203-iff-term
     (q1050203-static-apply-term left '(x))
     (q1050203-static-apply-term right '(x))))))

(defun q1050203-set-equiv-p
    (carrier left right)
  (let ((condition
         (q1050203-set-equiv-function
          carrier left right))
        (always-true
         (q1050203-true-function '(x))))
    (and
     (q1050203-valid-set-p carrier left)
     (q1050203-valid-set-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-family-extensional-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (list
       'q1050203-valid-set-p
       (q1050203-quoted carrier)
       'left)
      (list
       'q1050203-valid-set-p
       (q1050203-quoted carrier)
       'right)
      (list
       'q1050203-set-equiv-p
       (q1050203-quoted carrier)
       'left
       'right)))
    (q1050203-iff-term
     (q1050203-static-apply-term family '(left))
     (q1050203-static-apply-term family '(right))))))

(defun q1050203-family-members-valid-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q1050203-implies-term
    (q1050203-static-apply-term family '(set))
    (list
     'q1050203-valid-set-p
     (q1050203-quoted carrier)
     'set))))

(defun q1050203-family-of-sets-p
    (carrier family)
  (let ((extensional
         (q1050203-family-extensional-function
          carrier family))
        (members-valid
         (q1050203-family-members-valid-function
          carrier family))
        (true2
         (q1050203-true-function '(left right)))
        (true1
         (q1050203-true-function '(set))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp family)
     (tamep-functionp extensional)
     (tamep-functionp members-valid)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal extensional true2)
     (fn-equal members-valid true1))))

(defun q1050203-set-nonempty-failure-function
    (carrier set)
  (list
   'lambda
   '(x)
   (list
    'if
    (q1050203-and-terms
     (list
      (q1050203-static-apply-term carrier '(x))
      (q1050203-static-apply-term set '(x))))
    (q1050203-quoted nil)
    (q1050203-quoted t))))

(defun q1050203-set-nonempty-p
    (carrier set)
  (let ((failure
         (q1050203-set-nonempty-failure-function
          carrier set))
        (always-true
         (q1050203-true-function '(x))))
    (and
     (q1050203-valid-set-p carrier set)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1050203-empty-set ()
  (list 'lambda '(x) (q1050203-quoted nil)))

(defun q1050203-full-set (carrier)
  (list
   'lambda
   '(x)
   (q1050203-static-apply-term carrier '(x))))

(defun q1050203-complement-set (carrier set)
  (list
   'lambda
   '(x)
   (q1050203-and-terms
    (list
     (q1050203-static-apply-term carrier '(x))
     (q1050203-not-term
      (q1050203-static-apply-term set '(x)))))))

(defun q1050203-intersection-set (left right)
  (list
   'lambda
   '(x)
   (q1050203-and-terms
    (list
     (q1050203-static-apply-term left '(x))
     (q1050203-static-apply-term right '(x))))))

(defun q1050203-union-member-witness-p
    (carrier family x set)
  (and
   (q1050203-valid-set-p carrier set)
   (q1050203-member-p family set)
   (q1050203-member-p set x)))

(defun q1050203-union-member-failure-function
    (carrier family x)
  (list
   'lambda
   '(set)
   (list
    'if
    (list
     'q1050203-union-member-witness-p
     (q1050203-quoted carrier)
     (q1050203-quoted family)
     (q1050203-quoted x)
     'set)
    (q1050203-quoted nil)
    (q1050203-quoted t))))

(defun q1050203-union-member-p
    (carrier family x)
  (let ((failure
         (q1050203-union-member-failure-function
          carrier family x))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1050203-union-set (carrier family)
  (list
   'lambda
   '(x)
   (list
    'q1050203-union-member-p
    (q1050203-quoted carrier)
    (q1050203-quoted family)
    'x)))

(defun q1050203-open-set-p
    (carrier topology set)
  (and
   (q1050203-valid-set-p carrier set)
   (q1050203-member-p topology set)))

(defun q1050203-family-members-open-function
    (carrier topology family)
  (list
   'lambda
   '(set)
   (q1050203-implies-term
    (q1050203-static-apply-term family '(set))
    (list
     'q1050203-open-set-p
     (q1050203-quoted carrier)
     (q1050203-quoted topology)
     'set))))

(defun q1050203-family-members-open-p
    (carrier topology family)
  (let ((condition
         (q1050203-family-members-open-function
          carrier topology family))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (q1050203-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-topology-intersection-function
    (carrier topology)
  (list
   'lambda
   '(left right)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (list
       'q1050203-open-set-p
       (q1050203-quoted carrier)
       (q1050203-quoted topology)
       'left)
      (list
       'q1050203-open-set-p
       (q1050203-quoted carrier)
       (q1050203-quoted topology)
       'right)))
    (list
     'q1050203-open-set-p
     (q1050203-quoted carrier)
     (q1050203-quoted topology)
     (list 'q1050203-intersection-set
           'left
           'right)))))

(defun q1050203-topology-union-function
    (carrier topology)
  (list
   'lambda
   '(family)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (list
       'q1050203-family-of-sets-p
       (q1050203-quoted carrier)
       'family)
      (list
       'q1050203-family-members-open-p
       (q1050203-quoted carrier)
       (q1050203-quoted topology)
       'family)))
    (list
     'q1050203-open-set-p
     (q1050203-quoted carrier)
     (q1050203-quoted topology)
     (list
      'q1050203-union-set
      (q1050203-quoted carrier)
      'family)))))

(defun q1050203-topological-space-p
    (carrier topology)
  (let ((empty
         (q1050203-empty-set))
        (full
         (q1050203-full-set carrier))
        (intersection-law
         (q1050203-topology-intersection-function
          carrier topology))
        (union-law
         (q1050203-topology-union-function
          carrier topology))
        (true2
         (q1050203-true-function '(left right)))
        (true1
         (q1050203-true-function '(family))))
    (and
     (tamep-functionp carrier)
     (q1050203-family-of-sets-p carrier topology)
     (tamep-functionp empty)
     (tamep-functionp full)
     (q1050203-open-set-p carrier topology empty)
     (q1050203-open-set-p carrier topology full)
     (tamep-functionp intersection-law)
     (tamep-functionp union-law)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal intersection-law true2)
     (fn-equal union-law true1))))

(defun q1050203-closed-set-p
    (carrier topology set)
  (and
   (q1050203-valid-set-p carrier set)
   (q1050203-open-set-p
    carrier
    topology
    (q1050203-complement-set carrier set))))

(defun q1050203-cover-point-function
    (carrier set cover)
  (list
   'lambda
   '(x)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (q1050203-static-apply-term carrier '(x))
      (q1050203-static-apply-term set '(x))))
    (list
     'q1050203-union-member-p
     (q1050203-quoted carrier)
     (q1050203-quoted cover)
     'x))))

(defun q1050203-cover-p
    (carrier topology set cover)
  (let ((condition
         (q1050203-cover-point-function
          carrier set cover))
        (always-true
         (q1050203-true-function '(x))))
    (and
     (q1050203-valid-set-p carrier set)
     (q1050203-family-of-sets-p carrier cover)
     (q1050203-family-members-open-p
      carrier topology cover)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-finite-subcover-elements-p
    (sets carrier cover)
  (if (consp sets)
      (and
       (q1050203-valid-set-p carrier (car sets))
       (q1050203-member-p cover (car sets))
       (q1050203-finite-subcover-elements-p
        (cdr sets) carrier cover))
    (equal sets nil)))

(defun q1050203-finite-subcover-point-p
    (sets x)
  (if (consp sets)
      (or
       (q1050203-member-p (car sets) x)
       (q1050203-finite-subcover-point-p
        (cdr sets) x))
    nil))

(defun q1050203-finite-subcover-point-function
    (carrier set sets)
  (list
   'lambda
   '(x)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (q1050203-static-apply-term carrier '(x))
      (q1050203-static-apply-term set '(x))))
    (list
     'q1050203-finite-subcover-point-p
     (q1050203-quoted sets)
     'x))))

(defun q1050203-finite-subcover-p
    (sets carrier set cover)
  (let ((condition
         (q1050203-finite-subcover-point-function
          carrier set sets))
        (always-true
         (q1050203-true-function '(x))))
    (and
     (true-listp sets)
     (q1050203-finite-subcover-elements-p
      sets carrier cover)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-finite-subcover-failure-function
    (carrier set cover)
  (list
   'lambda
   '(sets)
   (list
    'if
    (list
     'q1050203-finite-subcover-p
     'sets
     (q1050203-quoted carrier)
     (q1050203-quoted set)
     (q1050203-quoted cover))
    (q1050203-quoted nil)
    (q1050203-quoted t))))

(defun q1050203-finite-subcover-exists-p
    (carrier set cover)
  (let ((failure
         (q1050203-finite-subcover-failure-function
          carrier set cover))
        (always-true
         (q1050203-true-function '(sets))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1050203-compact-cover-function
    (carrier topology set)
  (list
   'lambda
   '(cover)
   (q1050203-implies-term
    (list
     'q1050203-cover-p
     (q1050203-quoted carrier)
     (q1050203-quoted topology)
     (q1050203-quoted set)
     'cover)
    (list
     'q1050203-finite-subcover-exists-p
     (q1050203-quoted carrier)
     (q1050203-quoted set)
     'cover))))

(defun q1050203-compact-set-p
    (carrier topology set)
  (let ((condition
         (q1050203-compact-cover-function
          carrier topology set))
        (always-true
         (q1050203-true-function '(cover))))
    (and
     (q1050203-valid-set-p carrier set)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-family-nonempty-failure-function
    (carrier family)
  (list
   'lambda
   '(set)
   (list
    'if
    (q1050203-and-terms
     (list
      (list
       'q1050203-valid-set-p
       (q1050203-quoted carrier)
       'set)
      (q1050203-static-apply-term family '(set))))
    (q1050203-quoted nil)
    (q1050203-quoted t))))

(defun q1050203-family-nonempty-p
    (carrier family)
  (let ((failure
         (q1050203-family-nonempty-failure-function
          carrier family))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (q1050203-family-of-sets-p carrier family)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1050203-directed-witness-p
    (carrier family left right witness)
  (and
   (q1050203-valid-set-p carrier witness)
   (q1050203-member-p family witness)
   (q1050203-set-subset-p carrier witness left)
   (q1050203-set-subset-p carrier witness right)))

(defun q1050203-directed-witness-failure-function
    (carrier family left right)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q1050203-directed-witness-p
     (q1050203-quoted carrier)
     (q1050203-quoted family)
     (q1050203-quoted left)
     (q1050203-quoted right)
     'witness)
    (q1050203-quoted nil)
    (q1050203-quoted t))))

(defun q1050203-directed-witness-exists-p
    (carrier family left right)
  (let ((failure
         (q1050203-directed-witness-failure-function
          carrier family left right))
        (always-true
         (q1050203-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1050203-directed-family-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1050203-implies-term
    (q1050203-and-terms
     (list
      (q1050203-static-apply-term family '(left))
      (q1050203-static-apply-term family '(right))))
    (list
     'q1050203-directed-witness-exists-p
     (q1050203-quoted carrier)
     (q1050203-quoted family)
     'left
     'right))))

(defun q1050203-directed-family-p
    (carrier family)
  (let ((condition
         (q1050203-directed-family-function
          carrier family))
        (always-true
         (q1050203-true-function '(left right))))
    (and
     (q1050203-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-family-members-nonempty-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q1050203-implies-term
    (q1050203-static-apply-term family '(set))
    (list
     'q1050203-set-nonempty-p
     (q1050203-quoted carrier)
     'set))))

(defun q1050203-family-members-nonempty-p
    (carrier family)
  (let ((condition
         (q1050203-family-members-nonempty-function
          carrier family))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (q1050203-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-family-members-compact-function
    (carrier topology family)
  (list
   'lambda
   '(set)
   (q1050203-implies-term
    (q1050203-static-apply-term family '(set))
    (list
     'q1050203-compact-set-p
     (q1050203-quoted carrier)
     (q1050203-quoted topology)
     'set))))

(defun q1050203-family-members-compact-p
    (carrier topology family)
  (let ((condition
         (q1050203-family-members-compact-function
          carrier topology family))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (q1050203-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-family-members-closed-function
    (carrier topology family)
  (list
   'lambda
   '(set)
   (q1050203-implies-term
    (q1050203-static-apply-term family '(set))
    (list
     'q1050203-closed-set-p
     (q1050203-quoted carrier)
     (q1050203-quoted topology)
     'set))))

(defun q1050203-family-members-closed-p
    (carrier topology family)
  (let ((condition
         (q1050203-family-members-closed-function
          carrier topology family))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (q1050203-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-point-in-all-function
    (family x)
  (list
   'lambda
   '(set)
   (q1050203-implies-term
    (q1050203-static-apply-term family '(set))
    (q1050203-apply-term 'set
                         (list (q1050203-quoted x))))))

(defun q1050203-point-in-all-p
    (family x)
  (let ((condition
         (q1050203-point-in-all-function family x))
        (always-true
         (q1050203-true-function '(set))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1050203-intersection-witness-p
    (carrier family x)
  (and
   (q1050203-member-p carrier x)
   (q1050203-point-in-all-p family x)))

(defun q1050203-intersection-failure-function
    (carrier family)
  (list
   'lambda
   '(x)
   (list
    'if
    (list
     'q1050203-intersection-witness-p
     (q1050203-quoted carrier)
     (q1050203-quoted family)
     'x)
    (q1050203-quoted nil)
    (q1050203-quoted t))))

(defun q1050203-intersection-nonempty-p
    (carrier family)
  (let ((failure
         (q1050203-intersection-failure-function
          carrier family))
        (always-true
         (q1050203-true-function '(x))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun thousand-theorems-q1050203-cantor-intersection-statement
    (carrier topology family)
  (implies
   (and
    (q1050203-topological-space-p carrier topology)
    (q1050203-family-of-sets-p carrier family)
    (q1050203-family-nonempty-p carrier family)
    (q1050203-directed-family-p carrier family)
    (q1050203-family-members-nonempty-p carrier family)
    (q1050203-family-members-compact-p
     carrier topology family)
    (q1050203-family-members-closed-p
     carrier topology family))
   (q1050203-intersection-nonempty-p
    carrier family)))

(value-triple :itpeval-statement-checked)
:q
