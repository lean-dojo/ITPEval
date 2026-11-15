;; Statement-only formalization of thousand-theorems corpus artifact Q1077462,
;; "König's theorem (set theory)": for arbitrary indexed families of
;; cardinals, pointwise strict inequality makes the cardinal sum of the first
;; family strictly smaller than the dependent product of the second.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Carriers and maps are tame APPLY$ function objects.  Existential map
;; witnesses remain inside DEFUN-SK.  Dependent functions are compared
;; pointwise, so their representation is extensional rather than syntactic.

(defun q1077462-quoted (object)
  (list 'quote object))

(defun q1077462-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q1077462-term-list (cdr terms)))
    (q1077462-quoted nil)))

(defun q1077462-apply-term (function-term arguments)
  (list
   'apply$
   function-term
   (q1077462-term-list arguments)))

(defun q1077462-static-apply-term (function arguments)
  (q1077462-apply-term
   (q1077462-quoted function)
   arguments))

(defun q1077462-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q1077462-quoted t)))

(defun q1077462-true-function (formals)
  (list 'lambda formals (q1077462-quoted t)))

(defun q1077462-member-p (carrier object)
  (if (apply$ carrier (list object))
      t
    nil))

(defun q1077462-related-p (relation left right)
  (if (apply$ relation (list left right))
      t
    nil))

(defun q1077462-map-value (map object)
  (apply$ map (list object)))

(defun q1077462-equality-relation ()
  (list
   'lambda
   '(left right)
   (list 'equal 'left 'right)))

;; An injection between setoid carriers is a total extensional map that
;; reflects the target equivalence relation.

(defun-sk q1077462-map-total-p
    (source-carrier target-carrier map)
  (forall (object)
    (implies
     (q1077462-member-p source-carrier object)
     (q1077462-member-p
      target-carrier
      (q1077462-map-value map object)))))

(defun-sk q1077462-map-extensional-p
    (source-carrier source-equality target-equality map)
  (forall (left right)
    (implies
     (and
      (q1077462-member-p source-carrier left)
      (q1077462-member-p source-carrier right)
      (q1077462-related-p source-equality left right))
     (q1077462-related-p
      target-equality
      (q1077462-map-value map left)
      (q1077462-map-value map right)))))

(defun-sk q1077462-map-injective-p
    (source-carrier source-equality target-equality map)
  (forall (left right)
    (implies
     (and
      (q1077462-member-p source-carrier left)
      (q1077462-member-p source-carrier right)
      (q1077462-related-p
       target-equality
       (q1077462-map-value map left)
       (q1077462-map-value map right)))
     (q1077462-related-p source-equality left right))))

(defun q1077462-injection-p
    (source-carrier source-equality
     target-carrier target-equality map)
  (and
   (tamep-functionp source-carrier)
   (tamep-functionp source-equality)
   (tamep-functionp target-carrier)
   (tamep-functionp target-equality)
   (tamep-functionp map)
   (q1077462-map-total-p
    source-carrier target-carrier map)
   (q1077462-map-extensional-p
    source-carrier source-equality target-equality map)
   (q1077462-map-injective-p
    source-carrier source-equality target-equality map)))

(defun-sk q1077462-injection-exists-p
    (source-carrier source-equality
     target-carrier target-equality)
  (exists (map)
    (q1077462-injection-p
     source-carrier source-equality
     target-carrier target-equality map)))

;; Strict cardinal inequality is injection in the forward direction and no
;; injection in the reverse direction.

(defun q1077462-cardinal-lt-p
    (left-carrier left-equality
     right-carrier right-equality)
  (and
   (q1077462-injection-exists-p
    left-carrier left-equality
    right-carrier right-equality)
   (not
    (q1077462-injection-exists-p
     right-carrier right-equality
     left-carrier left-equality))))

(defun q1077462-fiber-carrier (family index)
  (apply$ family (list index)))

(defun-sk q1077462-family-valid-p (index-carrier family)
  (forall (index)
    (implies
     (q1077462-member-p index-carrier index)
     (tamep-functionp
      (q1077462-fiber-carrier family index)))))

(defun-sk q1077462-pointwise-lt-p
    (index-carrier left-family right-family)
  (forall (index)
    (implies
     (q1077462-member-p index-carrier index)
     (q1077462-cardinal-lt-p
      (q1077462-fiber-carrier left-family index)
      (q1077462-equality-relation)
      (q1077462-fiber-carrier right-family index)
      (q1077462-equality-relation)))))

;; The indexed cardinal sum is represented by dependent pairs (index, value).

(defun q1077462-sum-member-p
    (index-carrier family pair)
  (and
   (true-listp pair)
   (equal (len pair) 2)
   (q1077462-member-p index-carrier (nth 0 pair))
   (q1077462-member-p
    (q1077462-fiber-carrier family (nth 0 pair))
    (nth 1 pair))))

(defun q1077462-sum-carrier
    (index-carrier family)
  (list
   'lambda
   '(pair)
   (list
    'q1077462-sum-member-p
    (q1077462-quoted index-carrier)
    (q1077462-quoted family)
    'pair)))

;; A dependent-product point is a function whose value at every index belongs
;; to the corresponding fiber.  FN-EQUAL supplies the unbounded universal
;; quantifier over the index carrier.

(defun q1077462-product-point-row-function
    (index-carrier family point)
  (list
   'lambda
   '(index)
   (q1077462-implies-term
    (q1077462-static-apply-term index-carrier '(index))
    (q1077462-apply-term
     (q1077462-static-apply-term family '(index))
     (list
      (q1077462-static-apply-term point '(index)))))))

(defun q1077462-product-point-p
    (index-carrier family point)
  (let ((condition
         (q1077462-product-point-row-function
          index-carrier family point))
        (always-true
         (q1077462-true-function '(index))))
    (and
     (tamep-functionp index-carrier)
     (tamep-functionp family)
     (tamep-functionp point)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1077462-product-carrier
    (index-carrier family)
  (list
   'lambda
   '(point)
   (list
    'q1077462-product-point-p
    (q1077462-quoted index-carrier)
    (q1077462-quoted family)
    'point)))

;; Product points are equal exactly when all indexed coordinates agree.

(defun q1077462-product-equality-row-function
    (index-carrier left right)
  (list
   'lambda
   '(index)
   (q1077462-implies-term
    (q1077462-static-apply-term index-carrier '(index))
    (list
     'equal
     (q1077462-static-apply-term left '(index))
     (q1077462-static-apply-term right '(index))))))

(defun q1077462-product-point-equal-p
    (index-carrier left right)
  (let ((condition
         (q1077462-product-equality-row-function
          index-carrier left right))
        (always-true
         (q1077462-true-function '(index))))
    (and
     (tamep-functionp left)
     (tamep-functionp right)
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q1077462-product-equality-relation
    (index-carrier)
  (list
   'lambda
   '(left right)
   (list
    'q1077462-product-point-equal-p
    (q1077462-quoted index-carrier)
    'left
    'right)))

(defun thousand-theorems-q1077462-konig-statement
    (index-carrier left-family right-family)
  (implies
   (and
    (tamep-functionp index-carrier)
    (tamep-functionp left-family)
    (tamep-functionp right-family)
    (q1077462-family-valid-p index-carrier left-family)
    (q1077462-family-valid-p index-carrier right-family)
    (q1077462-pointwise-lt-p
     index-carrier left-family right-family))
   (q1077462-cardinal-lt-p
    (q1077462-sum-carrier
     index-carrier left-family)
    (q1077462-equality-relation)
    (q1077462-product-carrier
     index-carrier right-family)
    (q1077462-product-equality-relation
     index-carrier))))

(value-triple :itpeval-statement-checked)
:q
