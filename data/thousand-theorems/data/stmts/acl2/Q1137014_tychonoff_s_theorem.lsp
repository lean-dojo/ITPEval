;; Statement-only formalization of thousand-theorems corpus artifact Q1137014,
;; "Tychonoff's theorem": the dependent product of an arbitrary indexed
;; family of compact subsets of topological spaces is compact in the product
;; topology. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Sets, families, dependent points, and topologies are tame characteristic
;; function objects. FN-EQUAL supplies unbounded universal quantification;
;; its negation supplies internal existential witnesses. Product-open sets
;; are defined by genuine finite-support basic neighborhoods.

(defun q1137014-quoted (object)
  (list 'quote object))

(defun q1137014-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1137014-term-list (cdr terms)))
    (q1137014-quoted nil)))

(defun q1137014-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1137014-term-list arguments)))

(defun q1137014-static-apply-term (function arguments)
  (q1137014-apply-term
   (q1137014-quoted function)
   arguments))

(defun q1137014-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q1137014-and-terms (cdr terms))
       (q1137014-quoted nil))
    (q1137014-quoted t)))

(defun q1137014-not-term (term)
  (list
   'if
   term
   (q1137014-quoted nil)
   (q1137014-quoted t)))

(defun q1137014-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1137014-quoted t)))

(defun q1137014-iff-term (left right)
  (list
   'if
   left
   (list 'if right
         (q1137014-quoted t)
         (q1137014-quoted nil))
   (list 'if right
         (q1137014-quoted nil)
         (q1137014-quoted t))))

(defun q1137014-true-function (formals)
  (list 'lambda formals (q1137014-quoted t)))

(defun q1137014-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

(defun q1137014-set-subset-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (q1137014-static-apply-term carrier '(x))
      (q1137014-static-apply-term left '(x))))
    (q1137014-static-apply-term right '(x)))))

(defun q1137014-set-subset-p
    (carrier left right)
  (let ((condition
         (q1137014-set-subset-function
          carrier left right))
        (always-true
         (q1137014-true-function '(x))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp left)
     (tamep-functionp right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-valid-set-p (carrier set)
  (and
   (tamep-functionp carrier)
   (tamep-functionp set)
   (q1137014-set-subset-p carrier set carrier)))

(defun q1137014-set-equiv-function
    (carrier left right)
  (list
   'lambda
   '(x)
   (q1137014-implies-term
    (q1137014-static-apply-term carrier '(x))
    (q1137014-iff-term
     (q1137014-static-apply-term left '(x))
     (q1137014-static-apply-term right '(x))))))

(defun q1137014-set-equiv-p
    (carrier left right)
  (let ((condition
         (q1137014-set-equiv-function
          carrier left right))
        (always-true
         (q1137014-true-function '(x))))
    (and
     (q1137014-valid-set-p carrier left)
     (q1137014-valid-set-p carrier right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-family-extensional-function
    (carrier family)
  (list
   'lambda
   '(left right)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (list
       'q1137014-valid-set-p
       (q1137014-quoted carrier)
       'left)
      (list
       'q1137014-valid-set-p
       (q1137014-quoted carrier)
       'right)
      (list
       'q1137014-set-equiv-p
       (q1137014-quoted carrier)
       'left
       'right)))
    (q1137014-iff-term
     (q1137014-static-apply-term family '(left))
     (q1137014-static-apply-term family '(right))))))

(defun q1137014-family-members-valid-function
    (carrier family)
  (list
   'lambda
   '(set)
   (q1137014-implies-term
    (q1137014-static-apply-term family '(set))
    (list
     'q1137014-valid-set-p
     (q1137014-quoted carrier)
     'set))))

(defun q1137014-family-of-sets-p
    (carrier family)
  (let ((extensional
         (q1137014-family-extensional-function
          carrier family))
        (members-valid
         (q1137014-family-members-valid-function
          carrier family))
        (true2
         (q1137014-true-function '(left right)))
        (true1
         (q1137014-true-function '(set))))
    (and
     (tamep-functionp carrier)
     (tamep-functionp family)
     (tamep-functionp extensional)
     (tamep-functionp members-valid)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal extensional true2)
     (fn-equal members-valid true1))))

(defun q1137014-set-nonempty-failure-function
    (carrier set)
  (list
   'lambda
   '(x)
   (list
    'if
    (q1137014-and-terms
     (list
      (q1137014-static-apply-term carrier '(x))
      (q1137014-static-apply-term set '(x))))
    (q1137014-quoted nil)
    (q1137014-quoted t))))

(defun q1137014-set-nonempty-p
    (carrier set)
  (let ((failure
         (q1137014-set-nonempty-failure-function
          carrier set))
        (always-true
         (q1137014-true-function '(x))))
    (and
     (q1137014-valid-set-p carrier set)
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1137014-empty-set ()
  (list 'lambda '(x) (q1137014-quoted nil)))

(defun q1137014-full-set (carrier)
  (list
   'lambda
   '(x)
   (q1137014-static-apply-term carrier '(x))))

(defun q1137014-complement-set (carrier set)
  (list
   'lambda
   '(x)
   (q1137014-and-terms
    (list
     (q1137014-static-apply-term carrier '(x))
     (q1137014-not-term
      (q1137014-static-apply-term set '(x)))))))

(defun q1137014-intersection-set (left right)
  (list
   'lambda
   '(x)
   (q1137014-and-terms
    (list
     (q1137014-static-apply-term left '(x))
     (q1137014-static-apply-term right '(x))))))

(defun q1137014-union-member-witness-p
    (carrier family x set)
  (and
   (q1137014-valid-set-p carrier set)
   (q1137014-member-p family set)
   (q1137014-member-p set x)))

(defun q1137014-union-member-failure-function
    (carrier family x)
  (list
   'lambda
   '(set)
   (list
    'if
    (list
     'q1137014-union-member-witness-p
     (q1137014-quoted carrier)
     (q1137014-quoted family)
     (q1137014-quoted x)
     'set)
    (q1137014-quoted nil)
    (q1137014-quoted t))))

(defun q1137014-union-member-p
    (carrier family x)
  (let ((failure
         (q1137014-union-member-failure-function
          carrier family x))
        (always-true
         (q1137014-true-function '(set))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1137014-union-set (carrier family)
  (list
   'lambda
   '(x)
   (list
    'q1137014-union-member-p
    (q1137014-quoted carrier)
    (q1137014-quoted family)
    'x)))

(defun q1137014-open-set-p
    (carrier topology set)
  (and
   (q1137014-valid-set-p carrier set)
   (q1137014-member-p topology set)))

(defun q1137014-family-members-open-function
    (carrier topology family)
  (list
   'lambda
   '(set)
   (q1137014-implies-term
    (q1137014-static-apply-term family '(set))
    (list
     'q1137014-open-set-p
     (q1137014-quoted carrier)
     (q1137014-quoted topology)
     'set))))

(defun q1137014-family-members-open-p
    (carrier topology family)
  (let ((condition
         (q1137014-family-members-open-function
          carrier topology family))
        (always-true
         (q1137014-true-function '(set))))
    (and
     (q1137014-family-of-sets-p carrier family)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-topology-intersection-function
    (carrier topology)
  (list
   'lambda
   '(left right)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (list
       'q1137014-open-set-p
       (q1137014-quoted carrier)
       (q1137014-quoted topology)
       'left)
      (list
       'q1137014-open-set-p
       (q1137014-quoted carrier)
       (q1137014-quoted topology)
       'right)))
    (list
     'q1137014-open-set-p
     (q1137014-quoted carrier)
     (q1137014-quoted topology)
     (list 'q1137014-intersection-set
           'left
           'right)))))

(defun q1137014-topology-union-function
    (carrier topology)
  (list
   'lambda
   '(family)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (list
       'q1137014-family-of-sets-p
       (q1137014-quoted carrier)
       'family)
      (list
       'q1137014-family-members-open-p
       (q1137014-quoted carrier)
       (q1137014-quoted topology)
       'family)))
    (list
     'q1137014-open-set-p
     (q1137014-quoted carrier)
     (q1137014-quoted topology)
     (list
      'q1137014-union-set
      (q1137014-quoted carrier)
      'family)))))

(defun q1137014-topological-space-p
    (carrier topology)
  (let ((empty
         (q1137014-empty-set))
        (full
         (q1137014-full-set carrier))
        (intersection-law
         (q1137014-topology-intersection-function
          carrier topology))
        (union-law
         (q1137014-topology-union-function
          carrier topology))
        (true2
         (q1137014-true-function '(left right)))
        (true1
         (q1137014-true-function '(family))))
    (and
     (tamep-functionp carrier)
     (q1137014-family-of-sets-p carrier topology)
     (tamep-functionp empty)
     (tamep-functionp full)
     (q1137014-open-set-p carrier topology empty)
     (q1137014-open-set-p carrier topology full)
     (tamep-functionp intersection-law)
     (tamep-functionp union-law)
     (tamep-functionp true2)
     (tamep-functionp true1)
     (fn-equal intersection-law true2)
     (fn-equal union-law true1))))

(defun q1137014-closed-set-p
    (carrier topology set)
  (and
   (q1137014-valid-set-p carrier set)
   (q1137014-open-set-p
    carrier
    topology
    (q1137014-complement-set carrier set))))

(defun q1137014-cover-point-function
    (carrier set cover)
  (list
   'lambda
   '(x)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (q1137014-static-apply-term carrier '(x))
      (q1137014-static-apply-term set '(x))))
    (list
     'q1137014-union-member-p
     (q1137014-quoted carrier)
     (q1137014-quoted cover)
     'x))))

(defun q1137014-cover-p
    (carrier topology set cover)
  (let ((condition
         (q1137014-cover-point-function
          carrier set cover))
        (always-true
         (q1137014-true-function '(x))))
    (and
     (q1137014-valid-set-p carrier set)
     (q1137014-family-of-sets-p carrier cover)
     (q1137014-family-members-open-p
      carrier topology cover)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-finite-subcover-elements-p
    (sets carrier cover)
  (if (consp sets)
      (and
       (q1137014-valid-set-p carrier (car sets))
       (q1137014-member-p cover (car sets))
       (q1137014-finite-subcover-elements-p
        (cdr sets) carrier cover))
    (equal sets nil)))

(defun q1137014-finite-subcover-point-p
    (sets x)
  (if (consp sets)
      (or
       (q1137014-member-p (car sets) x)
       (q1137014-finite-subcover-point-p
        (cdr sets) x))
    nil))

(defun q1137014-finite-subcover-point-function
    (carrier set sets)
  (list
   'lambda
   '(x)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (q1137014-static-apply-term carrier '(x))
      (q1137014-static-apply-term set '(x))))
    (list
     'q1137014-finite-subcover-point-p
     (q1137014-quoted sets)
     'x))))

(defun q1137014-finite-subcover-p
    (sets carrier set cover)
  (let ((condition
         (q1137014-finite-subcover-point-function
          carrier set sets))
        (always-true
         (q1137014-true-function '(x))))
    (and
     (true-listp sets)
     (q1137014-finite-subcover-elements-p
      sets carrier cover)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-finite-subcover-failure-function
    (carrier set cover)
  (list
   'lambda
   '(sets)
   (list
    'if
    (list
     'q1137014-finite-subcover-p
     'sets
     (q1137014-quoted carrier)
     (q1137014-quoted set)
     (q1137014-quoted cover))
    (q1137014-quoted nil)
    (q1137014-quoted t))))

(defun q1137014-finite-subcover-exists-p
    (carrier set cover)
  (let ((failure
         (q1137014-finite-subcover-failure-function
          carrier set cover))
        (always-true
         (q1137014-true-function '(sets))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1137014-compact-cover-function
    (carrier topology set)
  (list
   'lambda
   '(cover)
   (q1137014-implies-term
    (list
     'q1137014-cover-p
     (q1137014-quoted carrier)
     (q1137014-quoted topology)
     (q1137014-quoted set)
     'cover)
    (list
     'q1137014-finite-subcover-exists-p
     (q1137014-quoted carrier)
     (q1137014-quoted set)
     'cover))))

(defun q1137014-compact-set-p
    (carrier topology set)
  (let ((condition
         (q1137014-compact-cover-function
          carrier topology set))
        (always-true
         (q1137014-true-function '(cover))))
    (and
     (q1137014-valid-set-p carrier set)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-fiber-carrier-set
    (fiber-carrier index)
  (list
   'lambda
   '(x)
   (q1137014-static-apply-term
    fiber-carrier
    (list (q1137014-quoted index) 'x))))

(defun q1137014-fiber-topology-set
    (fiber-topology index)
  (list
   'lambda
   '(set)
   (q1137014-static-apply-term
    fiber-topology
    (list (q1137014-quoted index) 'set))))

(defun q1137014-fiber-subset-set
    (fiber-subset index)
  (list
   'lambda
   '(x)
   (q1137014-static-apply-term
    fiber-subset
    (list (q1137014-quoted index) 'x))))

(defun q1137014-coordinate-law-function
    (index-carrier fiber-carrier fiber-topology fiber-subset)
  (list
   'lambda
   '(i)
   (q1137014-implies-term
    (q1137014-static-apply-term index-carrier '(i))
    (q1137014-and-terms
     (list
      (list
       'q1137014-topological-space-p
       (list
        'q1137014-fiber-carrier-set
        (q1137014-quoted fiber-carrier)
        'i)
       (list
        'q1137014-fiber-topology-set
        (q1137014-quoted fiber-topology)
        'i))
      (list
       'q1137014-compact-set-p
       (list
        'q1137014-fiber-carrier-set
        (q1137014-quoted fiber-carrier)
        'i)
       (list
        'q1137014-fiber-topology-set
        (q1137014-quoted fiber-topology)
        'i)
       (list
        'q1137014-fiber-subset-set
        (q1137014-quoted fiber-subset)
        'i)))))))

(defun q1137014-coordinate-family-p
    (index-carrier fiber-carrier fiber-topology fiber-subset)
  (let ((condition
         (q1137014-coordinate-law-function
          index-carrier fiber-carrier
          fiber-topology fiber-subset))
        (always-true
         (q1137014-true-function '(i))))
    (and
     (tamep-functionp index-carrier)
     (tamep-functionp fiber-carrier)
     (tamep-functionp fiber-topology)
     (tamep-functionp fiber-subset)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-product-point-row-function
    (index-carrier fiber-carrier point)
  (list
   'lambda
   '(i)
   (q1137014-implies-term
    (q1137014-static-apply-term index-carrier '(i))
    (q1137014-static-apply-term
     fiber-carrier
     (list
      'i
      (q1137014-static-apply-term point '(i)))))))

(defun q1137014-product-point-p
    (index-carrier fiber-carrier point)
  (let ((condition
         (q1137014-product-point-row-function
          index-carrier fiber-carrier point))
        (always-true
         (q1137014-true-function '(i))))
    (and
     (tamep-functionp point)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-product-carrier-set
    (index-carrier fiber-carrier)
  (list
   'lambda
   '(point)
   (list
    'q1137014-product-point-p
    (q1137014-quoted index-carrier)
    (q1137014-quoted fiber-carrier)
    'point)))

(defun q1137014-product-subset-row-function
    (index-carrier fiber-subset point)
  (list
   'lambda
   '(i)
   (q1137014-implies-term
    (q1137014-static-apply-term index-carrier '(i))
    (q1137014-static-apply-term
     fiber-subset
     (list
      'i
      (q1137014-static-apply-term point '(i)))))))

(defun q1137014-product-subset-member-p
    (index-carrier fiber-carrier fiber-subset point)
  (let ((condition
         (q1137014-product-subset-row-function
          index-carrier fiber-subset point))
        (always-true
         (q1137014-true-function '(i))))
    (and
     (q1137014-product-point-p
      index-carrier fiber-carrier point)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-product-subset-set
    (index-carrier fiber-carrier fiber-subset)
  (list
   'lambda
   '(point)
   (list
    'q1137014-product-subset-member-p
    (q1137014-quoted index-carrier)
    (q1137014-quoted fiber-carrier)
    (q1137014-quoted fiber-subset)
    'point)))

(defun q1137014-basic-data-p
    (data index-carrier fiber-carrier fiber-topology point)
  (if (consp data)
      (let* ((entry (car data))
             (index (nth 0 entry))
             (open (nth 1 entry))
             (coordinate
              (apply$ point (list index))))
        (and
         (true-listp entry)
         (equal (len entry) 2)
         (q1137014-member-p index-carrier index)
         (q1137014-open-set-p
          (q1137014-fiber-carrier-set
           fiber-carrier index)
          (q1137014-fiber-topology-set
           fiber-topology index)
          open)
         (q1137014-member-p open coordinate)
         (q1137014-basic-data-p
          (cdr data)
          index-carrier fiber-carrier
          fiber-topology point)))
    (equal data nil)))

(defun q1137014-basic-contains-point-p
    (data point)
  (if (consp data)
      (let* ((entry (car data))
             (index (nth 0 entry))
             (open (nth 1 entry)))
        (and
         (q1137014-member-p
          open
          (apply$ point (list index)))
         (q1137014-basic-contains-point-p
          (cdr data) point)))
    (equal data nil)))

(defun q1137014-basic-subset-function
    (data index-carrier fiber-carrier set)
  (list
   'lambda
   '(point)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (list
       'q1137014-product-point-p
       (q1137014-quoted index-carrier)
       (q1137014-quoted fiber-carrier)
       'point)
      (list
       'q1137014-basic-contains-point-p
       (q1137014-quoted data)
       'point)))
    (q1137014-static-apply-term set '(point)))))

(defun q1137014-basic-subset-p
    (data index-carrier fiber-carrier set)
  (let ((condition
         (q1137014-basic-subset-function
          data index-carrier fiber-carrier set))
        (always-true
         (q1137014-true-function '(point))))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-open-witness-p
    (data index-carrier fiber-carrier
          fiber-topology set point)
  (and
   (true-listp data)
   (q1137014-basic-data-p
    data index-carrier fiber-carrier
    fiber-topology point)
   (q1137014-basic-subset-p
    data index-carrier fiber-carrier set)))

(defun q1137014-open-witness-failure-function
    (index-carrier fiber-carrier fiber-topology set point)
  (list
   'lambda
   '(data)
   (list
    'if
    (list
     'q1137014-open-witness-p
     'data
     (q1137014-quoted index-carrier)
     (q1137014-quoted fiber-carrier)
     (q1137014-quoted fiber-topology)
     (q1137014-quoted set)
     (q1137014-quoted point))
    (q1137014-quoted nil)
    (q1137014-quoted t))))

(defun q1137014-open-witness-exists-p
    (index-carrier fiber-carrier fiber-topology set point)
  (let ((failure
         (q1137014-open-witness-failure-function
          index-carrier fiber-carrier
          fiber-topology set point))
        (always-true
         (q1137014-true-function '(data))))
    (and
     (tamep-functionp failure)
     (tamep-functionp always-true)
     (not (fn-equal failure always-true)))))

(defun q1137014-product-open-row-function
    (index-carrier fiber-carrier fiber-topology set)
  (list
   'lambda
   '(point)
   (q1137014-implies-term
    (q1137014-and-terms
     (list
      (list
       'q1137014-product-point-p
       (q1137014-quoted index-carrier)
       (q1137014-quoted fiber-carrier)
       'point)
      (q1137014-static-apply-term set '(point))))
    (list
     'q1137014-open-witness-exists-p
     (q1137014-quoted index-carrier)
     (q1137014-quoted fiber-carrier)
     (q1137014-quoted fiber-topology)
     (q1137014-quoted set)
     'point))))

(defun q1137014-product-open-set-p
    (index-carrier fiber-carrier fiber-topology set)
  (let ((product-carrier
         (q1137014-product-carrier-set
          index-carrier fiber-carrier))
        (condition
         (q1137014-product-open-row-function
          index-carrier fiber-carrier
          fiber-topology set))
        (always-true
         (q1137014-true-function '(point))))
    (and
     (q1137014-valid-set-p product-carrier set)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1137014-product-topology-set
    (index-carrier fiber-carrier fiber-topology)
  (list
   'lambda
   '(set)
   (list
    'q1137014-product-open-set-p
    (q1137014-quoted index-carrier)
    (q1137014-quoted fiber-carrier)
    (q1137014-quoted fiber-topology)
    'set)))

(defun thousand-theorems-q1137014-tychonoff-statement
    (index-carrier fiber-carrier fiber-topology fiber-subset)
  (implies
   (q1137014-coordinate-family-p
    index-carrier fiber-carrier
    fiber-topology fiber-subset)
   (q1137014-compact-set-p
    (q1137014-product-carrier-set
     index-carrier fiber-carrier)
    (q1137014-product-topology-set
     index-carrier fiber-carrier fiber-topology)
    (q1137014-product-subset-set
     index-carrier fiber-carrier fiber-subset))))

(value-triple :itpeval-statement-checked)
:q
