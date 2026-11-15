;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_combinators_Combinators_reductionqtvc: the call-by-value
;; reduction verification condition for S-K combinator terms, using evaluation
;; contexts and reflexive-transitive reduction. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Terms are represented bijectively by the finite constructor records
;; (:CRQ-S), (:CRQ-K), and (:CRQ-APP term term).

(defun crq-s-shape-p (term)
  (equal term (list :crq-s)))

(defun crq-k-shape-p (term)
  (equal term (list :crq-k)))

(defun crq-app-shape-p (term)
  (and
   (true-listp term)
   (equal (len term) 3)
   (equal (car term) :crq-app)))

(defun crq-term-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((crq-s-shape-p term)
    t)
   ((crq-k-shape-p term)
    t)
   ((crq-app-shape-p term)
    (and
     (crq-term-p (cadr term))
     (crq-term-p (caddr term))))
   (t nil)))

(defun crq-s ()
  (list :crq-s))

(defun crq-k ()
  (list :crq-k))

(defun crq-app (function argument)
  (list :crq-app function argument))

(defun crq-app-function (term)
  (cadr term))

(defun crq-app-argument (term)
  (caddr term))

;; This is the source call-by-value predicate on valid terms.

(defun crq-is-value-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((crq-k-shape-p term)
    t)
   ((crq-s-shape-p term)
    t)
   ((crq-app-shape-p term)
    (let ((function (crq-app-function term))
          (argument (crq-app-argument term)))
      (and
       (crq-term-p function)
       (crq-term-p argument)
       (cond
        ((crq-k-shape-p function)
         (crq-is-value-p argument))
        ((crq-s-shape-p function)
         (crq-is-value-p argument))
        ((and
          (crq-app-shape-p function)
          (crq-s-shape-p
           (crq-app-function function)))
         (and
          (crq-is-value-p
           (crq-app-argument function))
          (crq-is-value-p argument)))
        (t nil)))))
   (t nil)))

;; Contexts are represented bijectively by the finite constructor records
;; (:CRQ-HOLE), (:CRQ-LEFT context term), and
;; (:CRQ-RIGHT term context).

(defun crq-hole-shape-p (context)
  (equal context (list :crq-hole)))

(defun crq-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :crq-left)))

(defun crq-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :crq-right)))

(defun crq-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((crq-hole-shape-p context)
    t)
   ((crq-left-shape-p context)
    (and
     (crq-context-p (cadr context))
     (crq-term-p (caddr context))))
   ((crq-right-shape-p context)
    (and
     (crq-term-p (cadr context))
     (crq-context-p (caddr context))))
   (t nil)))

(defun crq-hole ()
  (list :crq-hole))

(defun crq-left (context term)
  (list :crq-left context term))

(defun crq-right (term context)
  (list :crq-right term context))

(defun crq-left-context (context)
  (cadr context))

(defun crq-left-term (context)
  (caddr context))

(defun crq-right-term (context)
  (cadr context))

(defun crq-right-context (context)
  (caddr context))

(defun crq-is-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((crq-hole-shape-p context)
    t)
   ((crq-left-shape-p context)
    (and
     (crq-term-p
      (crq-left-term context))
     (crq-is-context-p
      (crq-left-context context))))
   ((crq-right-shape-p context)
    (and
     (crq-term-p
      (crq-right-term context))
     (crq-is-value-p
      (crq-right-term context))
     (crq-is-context-p
      (crq-right-context context))))
   (t nil)))

(defun crq-subst (context term)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((crq-hole-shape-p context)
    term)
   ((crq-left-shape-p context)
    (crq-app
     (crq-subst
      (crq-left-context context)
      term)
     (crq-left-term context)))
   ((crq-right-shape-p context)
    (crq-app
     (crq-right-term context)
     (crq-subst
      (crq-right-context context)
      term)))
   (t term)))

;; The source one-step relation is the union of its two inductive rules.

(defun-sk crq-red-k-p (source target)
  (exists (context value1 value2)
    (and
     (crq-context-p context)
     (crq-term-p value1)
     (crq-term-p value2)
     (crq-is-context-p context)
     (crq-is-value-p value1)
     (crq-is-value-p value2)
     (equal
      source
      (crq-subst
       context
       (crq-app
        (crq-app (crq-k) value1)
        value2)))
     (equal
      target
      (crq-subst context value1)))))

(defun-sk crq-red-s-p (source target)
  (exists (context value1 value2 value3)
    (and
     (crq-context-p context)
     (crq-term-p value1)
     (crq-term-p value2)
     (crq-term-p value3)
     (crq-is-context-p context)
     (crq-is-value-p value1)
     (crq-is-value-p value2)
     (crq-is-value-p value3)
     (equal
      source
      (crq-subst
       context
       (crq-app
        (crq-app
         (crq-app (crq-s) value1)
         value2)
        value3)))
     (equal
      target
      (crq-subst
       context
       (crq-app
        (crq-app value1 value3)
        (crq-app value2 value3)))))))

(defun crq-one-step-p (source target)
  (and
   (crq-term-p source)
   (crq-term-p target)
   (or
    (crq-red-k-p source target)
    (crq-red-s-p source target))))

;; A nonempty finite term sequence is constructor evidence for the source
;; reflexive-transitive closure: a singleton is reflexivity, and each extra
;; element is one StepTransRefl application.

(defun crq-term-list-p (terms)
  (if (consp terms)
      (and
       (crq-term-p (car terms))
       (crq-term-list-p (cdr terms)))
    (equal terms nil)))

(defun crq-reduction-path-steps-p (terms)
  (if (and
       (consp terms)
       (consp (cdr terms)))
      (and
       (crq-one-step-p
        (car terms)
        (cadr terms))
       (crq-reduction-path-steps-p
        (cdr terms)))
    (and
     (consp terms)
     (equal (cdr terms) nil))))

(defun crq-reduction-path-witness-p
    (terms source target)
  (and
   (crq-term-list-p terms)
   (consp terms)
   (equal (car terms) source)
   (equal (car (last terms)) target)
   (crq-reduction-path-steps-p terms)))

(defun-sk crq-reltr-p (source target)
  (exists (terms)
    (and
     (crq-term-p source)
     (crq-term-p target)
     (crq-reduction-path-witness-p
      terms source target))))

;; This is the source context-composition function.

(defun crq-subst-c (context inner-context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((crq-hole-shape-p context)
    inner-context)
   ((crq-left-shape-p context)
    (crq-left
     (crq-subst-c
      (crq-left-context context)
      inner-context)
     (crq-left-term context)))
   ((crq-right-shape-p context)
    (crq-right
     (crq-right-term context)
     (crq-subst-c
      (crq-right-context context)
      inner-context)))
   (t inner-context)))

(defun crq-context-composition-spec-p
    (context inner-context)
  (implies
   (and
    (crq-is-context-p context)
    (crq-is-context-p inner-context))
   (crq-is-context-p
    (crq-subst-c context inner-context))))

;; This universal predicate is the recursive S-branch of the source match.

(defun-sk crq-all-recursive-results-p
    (term context value2 value3 value4)
  (forall (result)
    (implies
     (crq-term-p result)
     (implies
      (and
       (crq-reltr-p
        (crq-subst
         context
         (crq-app
          (crq-app value3 value2)
          (crq-app value4 value2)))
        (crq-subst context result))
       (crq-is-value-p result))
      (and
       (crq-reltr-p
        (crq-subst context term)
        (crq-subst context result))
       (crq-is-value-p result))))))

;; Exact target-native rendering of the source match on the first value.

(defun crq-value-branch-obligation-p
    (term context value1 value2)
  (cond
   ((crq-k-shape-p value1)
    (let ((result (crq-app value1 value2)))
      (and
       (crq-reltr-p
        (crq-subst context term)
        (crq-subst context result))
       (crq-is-value-p result))))
   ((crq-s-shape-p value1)
    (let ((result (crq-app value1 value2)))
      (and
       (crq-reltr-p
        (crq-subst context term)
        (crq-subst context result))
       (crq-is-value-p result))))
   ((and
     (crq-app-shape-p value1)
     (crq-s-shape-p
      (crq-app-function value1)))
    (let ((result (crq-app value1 value2)))
      (and
       (crq-reltr-p
        (crq-subst context term)
        (crq-subst context result))
       (crq-is-value-p result))))
   ((and
     (crq-app-shape-p value1)
     (crq-k-shape-p
      (crq-app-function value1)))
    (let ((value3 (crq-app-argument value1)))
      (and
       (crq-reltr-p
        (crq-subst context term)
        (crq-subst context value3))
       (crq-is-value-p value3))))
   ((and
     (crq-app-shape-p value1)
     (crq-app-shape-p
      (crq-app-function value1))
     (crq-s-shape-p
      (crq-app-function
       (crq-app-function value1))))
    (let ((value3
           (crq-app-argument
            (crq-app-function value1)))
          (value4
           (crq-app-argument value1)))
      (and
       (crq-is-context-p context)
       (crq-all-recursive-results-p
        term context value2 value3 value4))))
   (t nil)))

;; These predicates preserve the two nested universal quantifiers over
;; possible recursively computed values.

(defun-sk crq-all-second-values-p
    (term context term2 context4 value1)
  (forall (value2)
    (implies
     (crq-term-p value2)
     (implies
      (and
       (crq-reltr-p
        (crq-subst context4 term2)
        (crq-subst context4 value2))
       (crq-is-value-p value2))
      (crq-value-branch-obligation-p
       term context value1 value2)))))

(defun crq-second-phase-obligation-p
    (term context term2 value1)
  (let* ((context3
          (crq-right value1 (crq-hole)))
         (context4
          (crq-subst-c context context3)))
    (implies
     (crq-context-composition-spec-p
      context context3)
     (and
      (crq-is-context-p context4)
      (crq-all-second-values-p
       term context term2 context4 value1)))))

(defun-sk crq-all-first-values-p
    (term context term1 term2 context2)
  (forall (value1)
    (implies
     (crq-term-p value1)
     (implies
      (and
       (crq-reltr-p
        (crq-subst context2 term1)
        (crq-subst context2 value1))
       (crq-is-value-p value1))
      (crq-second-phase-obligation-p
       term context term2 value1)))))

(defun crq-app-obligation-p (term context)
  (let* ((term1
          (crq-app-function term))
         (term2
          (crq-app-argument term))
         (context1
          (crq-left (crq-hole) term2))
         (context2
          (crq-subst-c context context1)))
    (implies
     (crq-context-composition-spec-p
      context context1)
     (and
      (crq-is-context-p context2)
      (crq-all-first-values-p
       term context term1 term2 context2)))))

(defun
  ntp4vc-pearl-vstte12-combinators-combinators-reductionqtvc-statement
  (context term)
  (implies
   (and
    (crq-context-p context)
    (crq-term-p term)
    (crq-is-context-p context))
   (cond
    ((crq-s-shape-p term)
     (let ((result (crq-s)))
       (and
        (crq-reltr-p
         (crq-subst context term)
         (crq-subst context result))
        (crq-is-value-p result))))
    ((crq-k-shape-p term)
     (let ((result (crq-k)))
       (and
        (crq-reltr-p
         (crq-subst context term)
         (crq-subst context result))
        (crq-is-value-p result))))
    ((crq-app-shape-p term)
     (crq-app-obligation-p term context))
    (t nil))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
