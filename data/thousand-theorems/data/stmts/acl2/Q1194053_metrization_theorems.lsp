;; Statement-only formalization of thousand-theorems corpus artifact Q1194053,
;; "Metrization theorems": every T3 topological space with a second-countable
;; topology admits a compatible metrizable-space structure. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Sets, relations, families, and sequences are tame function objects over an
;; arbitrary carrier. FN-EQUAL supplies unbounded universal quantification,
;; and its negation supplies internal existential witnesses. The conclusion
;; uses the standard bidirectional uniform metrization characterization: a
;; topology is metrizable exactly when it is T0 and is induced by a uniformity
;; with a countable entourage basis.

(defun q1194053-quoted (object)
  (list 'quote object))

(defun q1194053-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1194053-term-list (cdr terms)))
    (q1194053-quoted nil)))

(defun q1194053-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1194053-term-list arguments)))

(defun q1194053-static-apply-term (function arguments)
  (q1194053-apply-term
   (q1194053-quoted function)
   arguments))

(defun q1194053-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1194053-and-terms (cdr terms))
       (q1194053-quoted nil))
    (q1194053-quoted t)))

(defun q1194053-not-term (term)
  (list
   'if
   term
   (q1194053-quoted nil)
   (q1194053-quoted t)))

(defun q1194053-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1194053-quoted t)))

(defun q1194053-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q1194053-quoted t)
    (q1194053-quoted nil))
   (list
    'if
    right
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-true-function (formals)
  (list 'lambda formals (q1194053-quoted t)))

(defun q1194053-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1194053-set-subset-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term left '(x))))
    (q1194053-static-apply-term right '(x)))))

(defun q1194053-set-subset-p
    (carrier left right)
  (let ((condition
         (q1194053-set-subset-function
          carrier left right))
        (always-true
         (q1194053-true-function '(x))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp left)
     (tamep-functionp right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1194053-set-subset-p carrier set carrier)))

(defun q1194053-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1194053-implies-term
    (q1194053-static-apply-term carrier '(x))
    (q1194053-iff-term
     (q1194053-static-apply-term left '(x))
     (q1194053-static-apply-term right '(x))))))

(defun q1194053-set-equiv-p
    (carrier left right)
  (let ((condition
         (q1194053-set-equiv-function
          carrier left right))
        (always-true
         (q1194053-true-function '(x))))
    (and
     (q1194053-valid-set-p carrier left)
     (q1194053-valid-set-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-family-extensional-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (list
       'q1194053-valid-set-p
       (q1194053-quoted carrier)
       'left)
      (list
       'q1194053-valid-set-p
       (q1194053-quoted carrier)
       'right)
      (list
       'q1194053-set-equiv-p
       (q1194053-quoted carrier)
       'left
       'right)))
    (q1194053-iff-term
     (q1194053-static-apply-term family '(left))
     (q1194053-static-apply-term family '(right))))))

(defun q1194053-family-members-valid-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q1194053-implies-term
    (q1194053-static-apply-term family '(set))
    (list
     'q1194053-valid-set-p
     (q1194053-quoted carrier)
     'set))))

(defun q1194053-family-of-sets-p
    (carrier family)
  (let ((extensional
         (q1194053-family-extensional-function
          carrier family))
        (members-valid
         (q1194053-family-members-valid-function
          carrier family))
        (true2
         (q1194053-true-function '(left right)))
        (true1
         (q1194053-true-function '(set))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp family)
     (tamep-functionp extensional)
     (tamep-functionp members-valid)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal extensional true2)
     (fn-equal members-valid true1))))

(defun q1194053-set-nonempty-failure-function
    (carrier set)
  (list
   'lambda
   '(x)
   (list
    'if
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term set '(x))))
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-set-nonempty-p
    (carrier set)
  (let ((failure
         (q1194053-set-nonempty-failure-function
          carrier set))
        (always-true
         (q1194053-true-function '(x))))
    (and
     (q1194053-valid-set-p carrier set)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-empty-set ()
  (list 'lambda '(x) (q1194053-quoted nil)))

(defun q1194053-full-set (carrier)
  (list
   'lambda
   '(x)
   (q1194053-static-apply-term carrier '(x))))

(defun q1194053-intersection-set (left right)
  (list
   'lambda
   '(x)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term left '(x))
     (q1194053-static-apply-term right '(x))))))

(defun q1194053-complement-set (carrier set)
  (list
   'lambda
   '(x)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term carrier '(x))
     (q1194053-not-term
      (q1194053-static-apply-term set '(x)))))))

(defun q1194053-intersection-nonempty-p
    (carrier left right)
  (q1194053-set-nonempty-p
   carrier
   (q1194053-intersection-set left right)))

(defun q1194053-union-member-witness-p
    (carrier family x set)
  (and
   (q1194053-valid-set-p carrier set)
   (q1194053-member-p family set)
   (q1194053-member-p set x)))

(defun q1194053-union-member-failure-function
    (carrier family x)
  (list
   'lambda
   '(set)
   (list
    'if
    (list
     'q1194053-union-member-witness-p
     (q1194053-quoted carrier)
     (q1194053-quoted family)
     (q1194053-quoted x)
     'set)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-union-member-p
    (carrier family x)
  (let ((failure
         (q1194053-union-member-failure-function
          carrier family x))
        (always-true
         (q1194053-true-function '(set))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-union-set (carrier family)
  (list
   'lambda
   '(x)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term carrier '(x))
     (list
      'q1194053-union-member-p
      (q1194053-quoted carrier)
      (q1194053-quoted family)
      'x)))))

(defun q1194053-open-set-p
    (carrier topology set)
  (and
   (q1194053-valid-set-p carrier set)
   (q1194053-member-p topology set)))

(defun q1194053-closed-set-p
    (carrier topology set)
  (and
   (q1194053-valid-set-p carrier set)
   (q1194053-open-set-p
    carrier
    topology
    (q1194053-complement-set carrier set))))

(defun q1194053-family-members-open-function
    (carrier topology family)
  (list
   'lambda
   '(set)
   (q1194053-implies-term
    (q1194053-static-apply-term family '(set))
    (list
     'q1194053-open-set-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     'set))))

(defun q1194053-family-members-open-p
    (carrier topology family)
  (let ((condition
         (q1194053-family-members-open-function
          carrier topology family))
        (always-true
         (q1194053-true-function '(set))))
    (and
     (q1194053-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-topology-intersection-function
    (carrier topology)
  (list
   'lambda
   '(left right)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (list
       'q1194053-open-set-p
       (q1194053-quoted carrier)
       (q1194053-quoted topology)
       'left)
      (list
       'q1194053-open-set-p
       (q1194053-quoted carrier)
       (q1194053-quoted topology)
       'right)))
    (list
     'q1194053-open-set-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     (list
      'q1194053-intersection-set
      'left
      'right)))))

(defun q1194053-topology-union-function
    (carrier topology)
  (list
   'lambda
   '(family)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (list
       'q1194053-family-of-sets-p
       (q1194053-quoted carrier)
       'family)
      (list
       'q1194053-family-members-open-p
       (q1194053-quoted carrier)
       (q1194053-quoted topology)
       'family)))
    (list
     'q1194053-open-set-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     (list
      'q1194053-union-set
      (q1194053-quoted carrier)
      'family)))))

(defun q1194053-topological-space-p
    (carrier topology)
  (let ((empty
         (q1194053-empty-set))
        (full
         (q1194053-full-set carrier))
        (intersection-law
         (q1194053-topology-intersection-function
          carrier topology))
        (union-law
         (q1194053-topology-union-function
          carrier topology))
        (true2
         (q1194053-true-function '(left right)))
        (true1
         (q1194053-true-function '(family))))
    (and
     (tamep-functionp carrier)
     (q1194053-family-of-sets-p carrier topology)
     (tamep-functionp empty)
     (tamep-functionp full)
     (q1194053-open-set-p carrier topology empty)
     (q1194053-open-set-p carrier topology full)
     (tamep-functionp intersection-law)
     (tamep-functionp union-law)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal intersection-law true2)
     (fn-equal union-law true1))))

(defun q1194053-set-disjoint-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1194053-implies-term
    (q1194053-static-apply-term carrier '(x))
    (q1194053-not-term
     (q1194053-and-terms
      (list
       (q1194053-static-apply-term left '(x))
       (q1194053-static-apply-term right '(x))))))))

(defun q1194053-set-disjoint-p
    (carrier left right)
  (let ((condition
         (q1194053-set-disjoint-function
          carrier left right))
        (always-true
         (q1194053-true-function '(x))))
    (and
     (q1194053-valid-set-p carrier left)
     (q1194053-valid-set-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-topologically-indistinguishable-function
    (carrier topology x y)
  (list
   'lambda
   '(set)
   (q1194053-implies-term
    (list
     'q1194053-open-set-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     'set)
    (q1194053-iff-term
     (q1194053-apply-term
      'set
      (list (q1194053-quoted x)))
     (q1194053-apply-term
      'set
      (list (q1194053-quoted y)))))))

(defun q1194053-topologically-indistinguishable-p
    (carrier topology x y)
  (let ((condition
         (q1194053-topologically-indistinguishable-function
          carrier topology x y))
        (always-true
         (q1194053-true-function '(set))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-t0-law-function
    (carrier topology)
  (list
   'lambda
   '(x y)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term carrier '(y))
      (list
       'q1194053-topologically-indistinguishable-p
       (q1194053-quoted carrier)
       (q1194053-quoted topology)
       'x
       'y)))
    (list 'equal 'x 'y))))

(defun q1194053-t0-space-p
    (carrier topology)
  (let ((condition
         (q1194053-t0-law-function carrier topology))
        (always-true
         (q1194053-true-function '(x y))))
    (and
     (q1194053-topological-space-p carrier topology)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-regular-witness-p
    (carrier topology closed x witness)
  (let ((left (car witness))
        (right (cdr witness)))
    (and
     (consp witness)
     (q1194053-open-set-p carrier topology left)
     (q1194053-open-set-p carrier topology right)
     (q1194053-member-p left x)
     (q1194053-set-subset-p carrier closed right)
     (q1194053-set-disjoint-p carrier left right))))

(defun q1194053-regular-witness-failure-function
    (carrier topology closed x)
  (list
   'lambda
   '(witness)
   (list
    'if
    (list
     'q1194053-regular-witness-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     (q1194053-quoted closed)
     (q1194053-quoted x)
     'witness)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-regular-witness-exists-p
    (carrier topology closed x)
  (let ((failure
         (q1194053-regular-witness-failure-function
          carrier topology closed x))
        (always-true
         (q1194053-true-function '(witness))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-regular-law-function
    (carrier topology)
  (list
   'lambda
   '(x closed)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (list
       'q1194053-closed-set-p
       (q1194053-quoted carrier)
       (q1194053-quoted topology)
       'closed)
      (q1194053-not-term
       (q1194053-apply-term 'closed '(x)))))
    (list
     'q1194053-regular-witness-exists-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     'closed
     'x))))

(defun q1194053-regular-space-p
    (carrier topology)
  (let ((condition
         (q1194053-regular-law-function
          carrier topology))
        (always-true
         (q1194053-true-function '(x closed))))
    (and
     (q1194053-topological-space-p carrier topology)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-t3-space-p
    (carrier topology)
  (and
   (q1194053-t0-space-p carrier topology)
   (q1194053-regular-space-p carrier topology)))

(defun q1194053-open-basis-sequence-function
    (carrier topology basis)
  (list
   'lambda
   '(n)
   (q1194053-implies-term
    (list 'natp 'n)
    (list
     'q1194053-open-set-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     (q1194053-static-apply-term basis '(n))))))

(defun q1194053-open-basis-sequence-p
    (carrier topology basis)
  (let ((condition
         (q1194053-open-basis-sequence-function
          carrier topology basis))
        (always-true
         (q1194053-true-function '(n))))
    (and
     (tamep-functionp basis)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-open-basis-hit-p
    (carrier basis open x n)
  (let ((basic-open (apply$ basis (list n))))
    (and
     (natp n)
     (q1194053-member-p basic-open x)
     (q1194053-set-subset-p
      carrier basic-open open))))

(defun q1194053-open-basis-hit-failure-function
    (carrier basis open x)
  (list
   'lambda
   '(n)
   (list
    'if
    (list
     'q1194053-open-basis-hit-p
     (q1194053-quoted carrier)
     (q1194053-quoted basis)
     (q1194053-quoted open)
     (q1194053-quoted x)
     'n)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-open-basis-hit-exists-p
    (carrier basis open x)
  (let ((failure
         (q1194053-open-basis-hit-failure-function
          carrier basis open x))
        (always-true
         (q1194053-true-function '(n))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-open-basis-law-function
    (carrier topology basis)
  (list
   'lambda
   '(open x)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (list
       'q1194053-open-set-p
       (q1194053-quoted carrier)
       (q1194053-quoted topology)
       'open)
      (q1194053-static-apply-term carrier '(x))
      (q1194053-apply-term 'open '(x))))
    (list
     'q1194053-open-basis-hit-exists-p
     (q1194053-quoted carrier)
     (q1194053-quoted basis)
     'open
     'x))))

(defun q1194053-countable-open-basis-p
    (carrier topology basis)
  (let ((condition
         (q1194053-open-basis-law-function
          carrier topology basis))
        (always-true
         (q1194053-true-function '(open x))))
    (and
     (q1194053-open-basis-sequence-p
      carrier topology basis)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-second-countable-failure-function
    (carrier topology)
  (list
   'lambda
   '(basis)
   (list
    'if
    (list
     'q1194053-countable-open-basis-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     'basis)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-second-countable-topology-p
    (carrier topology)
  (let ((failure
         (q1194053-second-countable-failure-function
          carrier topology))
        (always-true
         (q1194053-true-function '(basis))))
    (and
     (q1194053-topological-space-p carrier topology)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-valid-relation-function
    (carrier relation)
  (list
   'lambda
   '(x y)
   (q1194053-implies-term
    (q1194053-static-apply-term relation '(x y))
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term carrier '(y)))))))

(defun q1194053-valid-relation-p
    (carrier relation)
  (let ((condition
         (q1194053-valid-relation-function
          carrier relation))
        (always-true
         (q1194053-true-function '(x y))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp relation)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-relation-subset-function
    (carrier left right)
  (list
   'lambda
   '(x y)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term carrier '(y))
      (q1194053-static-apply-term left '(x y))))
    (q1194053-static-apply-term right '(x y)))))

(defun q1194053-relation-subset-p
    (carrier left right)
  (let ((condition
         (q1194053-relation-subset-function
          carrier left right))
        (always-true
         (q1194053-true-function '(x y))))
    (and
     (q1194053-valid-relation-p carrier left)
     (q1194053-valid-relation-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-relation-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x y)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term carrier '(y))))
    (q1194053-iff-term
     (q1194053-static-apply-term left '(x y))
     (q1194053-static-apply-term right '(x y))))))

(defun q1194053-relation-equiv-p
    (carrier left right)
  (let ((condition
         (q1194053-relation-equiv-function
          carrier left right))
        (always-true
         (q1194053-true-function '(x y))))
    (and
     (q1194053-valid-relation-p carrier left)
     (q1194053-valid-relation-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-relation-family-extensional-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (list
       'q1194053-valid-relation-p
       (q1194053-quoted carrier)
       'left)
      (list
       'q1194053-valid-relation-p
       (q1194053-quoted carrier)
       'right)
      (list
       'q1194053-relation-equiv-p
       (q1194053-quoted carrier)
       'left
       'right)))
    (q1194053-iff-term
     (q1194053-static-apply-term family '(left))
     (q1194053-static-apply-term family '(right))))))

(defun q1194053-relation-family-members-valid-function
    (carrier family)
  (list
   'lambda
   '(relation)
   (q1194053-implies-term
    (q1194053-static-apply-term family '(relation))
    (list
     'q1194053-valid-relation-p
     (q1194053-quoted carrier)
     'relation))))

(defun q1194053-family-of-relations-p
    (carrier family)
  (let ((extensional
         (q1194053-relation-family-extensional-function
          carrier family))
        (members-valid
         (q1194053-relation-family-members-valid-function
          carrier family))
        (true2
         (q1194053-true-function '(left right)))
        (true1
         (q1194053-true-function '(relation))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp family)
     (tamep-functionp extensional)
     (tamep-functionp members-valid)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal extensional true2)
     (fn-equal members-valid true1))))

(defun q1194053-full-relation
    (carrier)
  (list
   'lambda
   '(x y)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term carrier '(x))
     (q1194053-static-apply-term carrier '(y))))))

(defun q1194053-intersection-relation
    (left right)
  (list
   'lambda
   '(x y)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term left '(x y))
     (q1194053-static-apply-term right '(x y))))))

(defun q1194053-transpose-relation
    (relation)
  (list
   'lambda
   '(x y)
   (q1194053-static-apply-term relation '(y x))))

(defun q1194053-composition-member-witness-p
    (carrier left right x z y)
  (and
   (q1194053-member-p carrier y)
   (apply$ left (list x y))
   (apply$ right (list y z))))

(defun q1194053-composition-member-failure-function
    (carrier left right x z)
  (list
   'lambda
   '(y)
   (list
    'if
    (list
     'q1194053-composition-member-witness-p
     (q1194053-quoted carrier)
     (q1194053-quoted left)
     (q1194053-quoted right)
     (q1194053-quoted x)
     (q1194053-quoted z)
     'y)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-composition-member-p
    (carrier left right x z)
  (let ((failure
         (q1194053-composition-member-failure-function
          carrier left right x z))
        (always-true
         (q1194053-true-function '(y))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-composition-relation
    (carrier left right)
  (list
   'lambda
   '(x z)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term carrier '(x))
     (q1194053-static-apply-term carrier '(z))
     (list
      'q1194053-composition-member-p
      (q1194053-quoted carrier)
      (q1194053-quoted left)
      (q1194053-quoted right)
      'x
      'z)))))

(defun q1194053-filter-intersection-function
    (family)
  (list
   'lambda
   '(left right)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term family '(left))
      (q1194053-static-apply-term family '(right))))
    (q1194053-static-apply-term
     family
     (list
      (list
       'q1194053-intersection-relation
       'left
       'right))))))

(defun q1194053-filter-upward-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term family '(left))
      (list
       'q1194053-valid-relation-p
       (q1194053-quoted carrier)
       'right)
      (list
       'q1194053-relation-subset-p
       (q1194053-quoted carrier)
       'left
       'right)))
    (q1194053-static-apply-term family '(right)))))

(defun q1194053-relation-filter-p
    (carrier family)
  (let ((full
         (q1194053-full-relation carrier))
        (intersection-law
         (q1194053-filter-intersection-function
          family))
        (upward-law
         (q1194053-filter-upward-function
          carrier family))
        (true2
         (q1194053-true-function '(left right))))
    (and
     (q1194053-family-of-relations-p carrier family)
     (tamep-functionp full)
     (q1194053-member-p family full)
     (tamep-functionp intersection-law)
     (tamep-functionp upward-law)
     (tamep-functionp true2)
     (fn-equal intersection-law true2)
     (fn-equal upward-law true2))))

(defun q1194053-uniformity-diagonal-function
    (carrier family)
  (list
   'lambda
   '(relation x)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term family '(relation))
      (q1194053-static-apply-term carrier '(x))))
    (q1194053-apply-term 'relation '(x x)))))

(defun q1194053-uniformity-symmetry-function
    (family)
  (list
   'lambda
   '(relation)
   (q1194053-implies-term
    (q1194053-static-apply-term family '(relation))
    (q1194053-static-apply-term
     family
     (list
      (list
       'q1194053-transpose-relation
       'relation))))))

(defun q1194053-uniformity-square-witness-p
    (carrier family relation square-root)
  (and
   (q1194053-member-p family square-root)
   (q1194053-relation-subset-p
    carrier
    (q1194053-composition-relation
     carrier square-root square-root)
    relation)))

(defun q1194053-uniformity-square-failure-function
    (carrier family relation)
  (list
   'lambda
   '(square-root)
   (list
    'if
    (list
     'q1194053-uniformity-square-witness-p
     (q1194053-quoted carrier)
     (q1194053-quoted family)
     (q1194053-quoted relation)
     'square-root)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-uniformity-square-exists-p
    (carrier family relation)
  (let ((failure
         (q1194053-uniformity-square-failure-function
          carrier family relation))
        (always-true
         (q1194053-true-function '(square-root))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-uniformity-square-function
    (carrier family)
  (list
   'lambda
   '(relation)
   (q1194053-implies-term
    (q1194053-static-apply-term family '(relation))
    (list
     'q1194053-uniformity-square-exists-p
     (q1194053-quoted carrier)
     (q1194053-quoted family)
     'relation))))

(defun q1194053-uniformity-p
    (carrier family)
  (let ((diagonal-law
         (q1194053-uniformity-diagonal-function
          carrier family))
        (symmetry-law
         (q1194053-uniformity-symmetry-function
          family))
        (square-law
         (q1194053-uniformity-square-function
          carrier family))
        (true2
         (q1194053-true-function '(relation x)))
        (true1
         (q1194053-true-function '(relation))))
    (and
     (q1194053-relation-filter-p carrier family)
     (tamep-functionp diagonal-law)
     (tamep-functionp symmetry-law)
     (tamep-functionp square-law)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal diagonal-law true2)
     (fn-equal symmetry-law true1)
     (fn-equal square-law true1))))

(defun q1194053-relation-section
    (carrier relation x)
  (list
   'lambda
   '(y)
   (q1194053-and-terms
    (list
     (q1194053-static-apply-term carrier '(y))
     (q1194053-static-apply-term
      relation
      (list (q1194053-quoted x) 'y))))))

(defun q1194053-uniform-neighborhood-witness-p
    (carrier family open x relation)
  (and
   (q1194053-member-p family relation)
   (q1194053-relation-subset-p
    carrier
    relation
    relation)
   (q1194053-set-subset-p
    carrier
    (q1194053-relation-section
     carrier relation x)
    open)))

(defun q1194053-uniform-neighborhood-failure-function
    (carrier family open x)
  (list
   'lambda
   '(relation)
   (list
    'if
    (list
     'q1194053-uniform-neighborhood-witness-p
     (q1194053-quoted carrier)
     (q1194053-quoted family)
     (q1194053-quoted open)
     (q1194053-quoted x)
     'relation)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-uniform-neighborhood-exists-p
    (carrier family open x)
  (let ((failure
         (q1194053-uniform-neighborhood-failure-function
          carrier family open x))
        (always-true
         (q1194053-true-function '(relation))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-uniformly-open-function
    (carrier family open)
  (list
   'lambda
   '(x)
   (q1194053-implies-term
    (q1194053-and-terms
     (list
      (q1194053-static-apply-term carrier '(x))
      (q1194053-static-apply-term open '(x))))
    (list
     'q1194053-uniform-neighborhood-exists-p
     (q1194053-quoted carrier)
     (q1194053-quoted family)
     (q1194053-quoted open)
     'x))))

(defun q1194053-uniformly-open-p
    (carrier family open)
  (let ((condition
         (q1194053-uniformly-open-function
          carrier family open))
        (always-true
         (q1194053-true-function '(x))))
    (and
     (q1194053-valid-set-p carrier open)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-compatible-topology-function
    (carrier topology family)
  (list
   'lambda
   '(set)
   (q1194053-implies-term
    (list
     'q1194053-valid-set-p
     (q1194053-quoted carrier)
     'set)
    (q1194053-iff-term
     (list
      'q1194053-open-set-p
      (q1194053-quoted carrier)
      (q1194053-quoted topology)
      'set)
     (list
      'q1194053-uniformly-open-p
      (q1194053-quoted carrier)
      (q1194053-quoted family)
      'set)))))

(defun q1194053-compatible-topology-p
    (carrier topology family)
  (let ((condition
         (q1194053-compatible-topology-function
          carrier topology family))
        (always-true
         (q1194053-true-function '(set))))
    (and
     (q1194053-topological-space-p carrier topology)
     (q1194053-uniformity-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-uniform-basis-sequence-function
    (carrier family basis)
  (list
   'lambda
   '(n)
   (q1194053-implies-term
    (list 'natp 'n)
    (q1194053-and-terms
     (list
      (list
       'q1194053-valid-relation-p
       (q1194053-quoted carrier)
       (q1194053-static-apply-term basis '(n)))
      (q1194053-static-apply-term
       family
       (list
        (q1194053-static-apply-term basis '(n)))))))))

(defun q1194053-uniform-basis-sequence-p
    (carrier family basis)
  (let ((condition
         (q1194053-uniform-basis-sequence-function
          carrier family basis))
        (always-true
         (q1194053-true-function '(n))))
    (and
     (tamep-functionp basis)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-uniform-basis-hit-p
    (carrier basis relation n)
  (let ((basic-relation (apply$ basis (list n))))
    (and
     (natp n)
     (q1194053-relation-subset-p
      carrier basic-relation relation))))

(defun q1194053-uniform-basis-hit-failure-function
    (carrier basis relation)
  (list
   'lambda
   '(n)
   (list
    'if
    (list
     'q1194053-uniform-basis-hit-p
     (q1194053-quoted carrier)
     (q1194053-quoted basis)
     (q1194053-quoted relation)
     'n)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-uniform-basis-hit-exists-p
    (carrier basis relation)
  (let ((failure
         (q1194053-uniform-basis-hit-failure-function
          carrier basis relation))
        (always-true
         (q1194053-true-function '(n))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-uniform-basis-law-function
    (carrier family basis)
  (list
   'lambda
   '(relation)
   (q1194053-implies-term
    (q1194053-static-apply-term family '(relation))
    (list
     'q1194053-uniform-basis-hit-exists-p
     (q1194053-quoted carrier)
     (q1194053-quoted basis)
     'relation))))

(defun q1194053-countable-uniform-basis-p
    (carrier family basis)
  (let ((condition
         (q1194053-uniform-basis-law-function
          carrier family basis))
        (always-true
         (q1194053-true-function '(relation))))
    (and
     (q1194053-uniform-basis-sequence-p
      carrier family basis)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1194053-countably-generated-failure-function
    (carrier family)
  (list
   'lambda
   '(basis)
   (list
    'if
    (list
     'q1194053-countable-uniform-basis-p
     (q1194053-quoted carrier)
     (q1194053-quoted family)
     'basis)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-countably-generated-uniformity-p
    (carrier family)
  (let ((failure
         (q1194053-countably-generated-failure-function
          carrier family))
        (always-true
         (q1194053-true-function '(basis))))
    (and
     (q1194053-uniformity-p carrier family)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1194053-metrizable-uniformity-witness-p
    (carrier topology family)
  (and
   (q1194053-compatible-topology-p
    carrier topology family)
   (q1194053-countably-generated-uniformity-p
    carrier family)))

(defun q1194053-metrizable-uniformity-failure-function
    (carrier topology)
  (list
   'lambda
   '(family)
   (list
    'if
    (list
     'q1194053-metrizable-uniformity-witness-p
     (q1194053-quoted carrier)
     (q1194053-quoted topology)
     'family)
    (q1194053-quoted nil)
    (q1194053-quoted t))))

(defun q1194053-metrizable-space-p
    (carrier topology)
  (let ((failure
         (q1194053-metrizable-uniformity-failure-function
          carrier topology))
        (always-true
         (q1194053-true-function '(family))))
    (and
     (q1194053-t0-space-p carrier topology)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun thousand-theorems-q1194053-metrization-theorems-statement
    (carrier topology)
  (implies
   (and
    (q1194053-t3-space-p carrier topology)
    (q1194053-second-countable-topology-p
     carrier topology))
   (q1194053-metrizable-space-p carrier topology)))

(value-triple :itpeval-statement-checked)
:q
