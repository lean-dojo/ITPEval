;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_combinators_Combinators_reduction2qtvc: the call-by-value
;; reduction verification condition for S-K combinator terms containing only
;; K, using evaluation contexts and reflexive-transitive reduction. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Terms are represented bijectively by the finite constructor records
;; (:C2Q-S), (:C2Q-K), and (:C2Q-APP term term).

(defun c2q-s-shape-p (term)
  (equal term (list :c2q-s)))

(defun c2q-k-shape-p (term)
  (equal term (list :c2q-k)))

(defun c2q-app-shape-p (term)
  (and
   (true-listp term)
   (equal (len term) 3)
   (equal (car term) :c2q-app)))

(defun c2q-term-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((c2q-s-shape-p term)
    t)
   ((c2q-k-shape-p term)
    t)
   ((c2q-app-shape-p term)
    (and
     (c2q-term-p (cadr term))
     (c2q-term-p (caddr term))))
   (t nil)))

(defun c2q-s ()
  (list :c2q-s))

(defun c2q-k ()
  (list :c2q-k))

(defun c2q-app (function argument)
  (list :c2q-app function argument))

(defun c2q-app-function (term)
  (cadr term))

(defun c2q-app-argument (term)
  (caddr term))

;; This is the source call-by-value predicate on valid terms.

(defun c2q-is-value-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((c2q-k-shape-p term)
    t)
   ((c2q-s-shape-p term)
    t)
   ((c2q-app-shape-p term)
    (let ((function (c2q-app-function term))
          (argument (c2q-app-argument term)))
      (and
       (c2q-term-p function)
       (c2q-term-p argument)
       (cond
        ((c2q-k-shape-p function)
         (c2q-is-value-p argument))
        ((c2q-s-shape-p function)
         (c2q-is-value-p argument))
        ((and
          (c2q-app-shape-p function)
          (c2q-s-shape-p
           (c2q-app-function function)))
         (and
          (c2q-is-value-p
           (c2q-app-argument function))
          (c2q-is-value-p argument)))
        (t nil)))))
   (t nil)))

;; Contexts are represented bijectively by the finite constructor records
;; (:C2Q-HOLE), (:C2Q-LEFT context term), and
;; (:C2Q-RIGHT term context).

(defun c2q-hole-shape-p (context)
  (equal context (list :c2q-hole)))

(defun c2q-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :c2q-left)))

(defun c2q-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :c2q-right)))

(defun c2q-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c2q-hole-shape-p context)
    t)
   ((c2q-left-shape-p context)
    (and
     (c2q-context-p (cadr context))
     (c2q-term-p (caddr context))))
   ((c2q-right-shape-p context)
    (and
     (c2q-term-p (cadr context))
     (c2q-context-p (caddr context))))
   (t nil)))

(defun c2q-hole ()
  (list :c2q-hole))

(defun c2q-left (context term)
  (list :c2q-left context term))

(defun c2q-right (term context)
  (list :c2q-right term context))

(defun c2q-left-context (context)
  (cadr context))

(defun c2q-left-term (context)
  (caddr context))

(defun c2q-right-term (context)
  (cadr context))

(defun c2q-right-context (context)
  (caddr context))

(defun c2q-is-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c2q-hole-shape-p context)
    t)
   ((c2q-left-shape-p context)
    (and
     (c2q-term-p
      (c2q-left-term context))
     (c2q-is-context-p
      (c2q-left-context context))))
   ((c2q-right-shape-p context)
    (and
     (c2q-term-p
      (c2q-right-term context))
     (c2q-is-value-p
      (c2q-right-term context))
     (c2q-is-context-p
      (c2q-right-context context))))
   (t nil)))

(defun c2q-subst (context term)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c2q-hole-shape-p context)
    term)
   ((c2q-left-shape-p context)
    (c2q-app
     (c2q-subst
      (c2q-left-context context)
      term)
     (c2q-left-term context)))
   ((c2q-right-shape-p context)
    (c2q-app
     (c2q-right-term context)
     (c2q-subst
      (c2q-right-context context)
      term)))
   (t term)))

;; The source one-step relation is the union of its two inductive rules.

(defun-sk c2q-red-k-p (source target)
  (exists (context value1 value2)
    (and
     (c2q-context-p context)
     (c2q-term-p value1)
     (c2q-term-p value2)
     (c2q-is-context-p context)
     (c2q-is-value-p value1)
     (c2q-is-value-p value2)
     (equal
      source
      (c2q-subst
       context
       (c2q-app
        (c2q-app (c2q-k) value1)
        value2)))
     (equal
      target
      (c2q-subst context value1)))))

(defun-sk c2q-red-s-p (source target)
  (exists (context value1 value2 value3)
    (and
     (c2q-context-p context)
     (c2q-term-p value1)
     (c2q-term-p value2)
     (c2q-term-p value3)
     (c2q-is-context-p context)
     (c2q-is-value-p value1)
     (c2q-is-value-p value2)
     (c2q-is-value-p value3)
     (equal
      source
      (c2q-subst
       context
       (c2q-app
        (c2q-app
         (c2q-app (c2q-s) value1)
         value2)
        value3)))
     (equal
      target
      (c2q-subst
       context
       (c2q-app
        (c2q-app value1 value3)
        (c2q-app value2 value3)))))))

(defun c2q-one-step-p (source target)
  (and
   (c2q-term-p source)
   (c2q-term-p target)
   (or
    (c2q-red-k-p source target)
    (c2q-red-s-p source target))))

;; A nonempty finite term sequence is constructor evidence for the source
;; reflexive-transitive closure: a singleton is reflexivity, and each extra
;; element is one StepTransRefl application.

(defun c2q-term-list-p (terms)
  (if (consp terms)
      (and
       (c2q-term-p (car terms))
       (c2q-term-list-p (cdr terms)))
    (equal terms nil)))

(defun c2q-reduction-path-steps-p (terms)
  (if (and
       (consp terms)
       (consp (cdr terms)))
      (and
       (c2q-one-step-p
        (car terms)
        (cadr terms))
       (c2q-reduction-path-steps-p
        (cdr terms)))
    (and
     (consp terms)
     (equal (cdr terms) nil))))

(defun c2q-reduction-path-witness-p
    (terms source target)
  (and
   (c2q-term-list-p terms)
   (consp terms)
   (equal (car terms) source)
   (equal (car (last terms)) target)
   (c2q-reduction-path-steps-p terms)))

(defun-sk c2q-reltr-p (source target)
  (exists (terms)
    (and
     (c2q-term-p source)
     (c2q-term-p target)
     (c2q-reduction-path-witness-p
      terms source target))))

;; This is the source context-composition function.

(defun c2q-subst-c (context inner-context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c2q-hole-shape-p context)
    inner-context)
   ((c2q-left-shape-p context)
    (c2q-left
     (c2q-subst-c
      (c2q-left-context context)
      inner-context)
     (c2q-left-term context)))
   ((c2q-right-shape-p context)
    (c2q-right
     (c2q-right-term context)
     (c2q-subst-c
      (c2q-right-context context)
      inner-context)))
   (t inner-context)))

(defun c2q-context-composition-spec-p
    (context inner-context)
  (implies
   (and
    (c2q-is-context-p context)
    (c2q-is-context-p inner-context))
   (c2q-is-context-p
    (c2q-subst-c context inner-context))))

;; This is the source inductive predicate for terms built only from K and App.

(defun c2q-only-k-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((c2q-k-shape-p term)
    t)
   ((c2q-app-shape-p term)
    (and
     (c2q-only-k-p
      (c2q-app-function term))
     (c2q-only-k-p
      (c2q-app-argument term))))
   (t nil)))

;; Exact target-native renderings of the constructor matches in the VC.

(defun c2q-app-component-match-p (term component)
  (and
   (c2q-app-shape-p term)
   (or
    (equal
     (c2q-app-function term)
     component)
    (equal
     (c2q-app-argument term)
     component))))

(defun c2q-k-or-app-k-p (term)
  (and
   (c2q-term-p term)
   (or
    (c2q-k-shape-p term)
    (and
     (c2q-app-shape-p term)
     (c2q-k-shape-p
      (c2q-app-function term))))))

(defun c2q-result-match-p
    (value1 value2 result)
  (cond
   ((c2q-k-shape-p value1)
    (equal
     result
     (c2q-app value1 value2)))
   ((and
     (c2q-app-shape-p value1)
     (c2q-k-shape-p
      (c2q-app-function value1)))
    (equal
     result
     (c2q-app-argument value1)))
   (t nil)))

;; The first conjunct of reduction2'vc contains two nested universal
;; quantifiers over possible recursively computed values.

(defun-sk c2q-all-second-values-p
    (term term2 context4 value1)
  (forall (value2)
    (implies
     (c2q-term-p value2)
     (implies
      (and
       (c2q-only-k-p value2)
       (c2q-is-value-p value2)
       (c2q-reltr-p
        (c2q-subst context4 term2)
        (c2q-subst context4 value2)))
      (c2q-k-or-app-k-p value1)))))

(defun c2q-second-phase-obligation-p
    (term context term2 value1)
  (let* ((context3
          (c2q-right value1 (c2q-hole)))
         (context4
          (c2q-subst-c context context3)))
    (implies
     (c2q-context-composition-spec-p
      context context3)
     (and
      (c2q-app-component-match-p
       term term2)
      (c2q-only-k-p term2)
      (c2q-is-context-p context4)
      (c2q-all-second-values-p
       term term2 context4 value1)))))

(defun-sk c2q-all-first-values-p
    (term context term1 term2 context2)
  (forall (value1)
    (implies
     (c2q-term-p value1)
     (implies
      (and
       (c2q-only-k-p value1)
       (c2q-is-value-p value1)
       (c2q-reltr-p
        (c2q-subst context2 term1)
        (c2q-subst context2 value1)))
      (c2q-second-phase-obligation-p
       term context term2 value1)))))

(defun c2q-first-conjunct-p (term context)
  (cond
   ((c2q-k-shape-p term)
    t)
   ((c2q-app-shape-p term)
    (let* ((term1
            (c2q-app-function term))
           (term2
            (c2q-app-argument term))
           (context1
            (c2q-left (c2q-hole) term2))
           (context2
            (c2q-subst-c context context1)))
      (implies
       (c2q-context-composition-spec-p
        context context1)
       (and
        (c2q-app-component-match-p
         term term1)
        (c2q-only-k-p term1)
        (c2q-is-context-p context2)
        (c2q-all-first-values-p
         term context term1 term2 context2)))))
   (t nil)))

;; The second conjunct preserves the source's existentially quantified
;; intermediate values inside the premise for each universally quantified
;; result.

(defun-sk c2q-second-value-exists-p
    (term2 context4 value1 result)
  (exists (value2)
    (and
     (c2q-term-p value2)
     (c2q-only-k-p value2)
     (c2q-is-value-p value2)
     (c2q-reltr-p
      (c2q-subst context4 term2)
      (c2q-subst context4 value2))
     (c2q-result-match-p
      value1 value2 result))))

(defun-sk c2q-first-value-exists-p
    (context term1 term2 context2 result)
  (exists (value1)
    (and
     (c2q-term-p value1)
     (c2q-only-k-p value1)
     (c2q-is-value-p value1)
     (c2q-reltr-p
      (c2q-subst context2 term1)
      (c2q-subst context2 value1))
     (let* ((context3
             (c2q-right value1 (c2q-hole)))
            (context4
             (c2q-subst-c context context3)))
       (and
        (c2q-context-composition-spec-p
         context context3)
        (c2q-second-value-exists-p
         term2 context4 value1 result))))))

(defun c2q-result-premise-p
    (term context result)
  (cond
   ((c2q-k-shape-p term)
    (equal result (c2q-k)))
   ((c2q-app-shape-p term)
    (let* ((term1
            (c2q-app-function term))
           (term2
            (c2q-app-argument term))
           (context1
            (c2q-left (c2q-hole) term2))
           (context2
            (c2q-subst-c context context1)))
      (and
       (c2q-context-composition-spec-p
        context context1)
       (c2q-first-value-exists-p
        context term1 term2 context2 result))))
   (t nil)))

(defun-sk c2q-all-results-p (term context)
  (forall (result)
    (implies
     (c2q-term-p result)
     (implies
      (c2q-result-premise-p
       term context result)
      (and
       (c2q-only-k-p result)
       (c2q-is-value-p result)
       (c2q-reltr-p
        (c2q-subst context term)
        (c2q-subst context result)))))))

(defun
  ntp4vc-pearl-vstte12-combinators-combinators-reduction2qtvc-statement
  (term context)
  (implies
   (and
    (c2q-term-p term)
    (c2q-context-p context)
    (c2q-only-k-p term)
    (c2q-is-context-p context))
   (and
    (c2q-first-conjunct-p term context)
    (c2q-all-results-p term context))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
