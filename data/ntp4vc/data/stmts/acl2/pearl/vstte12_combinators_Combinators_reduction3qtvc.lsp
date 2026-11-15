;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vstte12_combinators_Combinators_reduction3qtvc: the call-by-value
;; reduction verification condition for the recursively defined sequence of
;; S-K combinator terms ks, with evaluation contexts, reflexive-transitive
;; reduction, and parity-sensitive results. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Terms are represented bijectively by the finite constructor records
;; (:C3Q-S), (:C3Q-K), and (:C3Q-APP term term).

(defun c3q-s-shape-p (term)
  (equal term (list :c3q-s)))

(defun c3q-k-shape-p (term)
  (equal term (list :c3q-k)))

(defun c3q-app-shape-p (term)
  (and
   (true-listp term)
   (equal (len term) 3)
   (equal (car term) :c3q-app)))

(defun c3q-term-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((c3q-s-shape-p term)
    t)
   ((c3q-k-shape-p term)
    t)
   ((c3q-app-shape-p term)
    (and
     (c3q-term-p (cadr term))
     (c3q-term-p (caddr term))))
   (t nil)))

(defun c3q-s ()
  (list :c3q-s))

(defun c3q-k ()
  (list :c3q-k))

(defun c3q-app (function argument)
  (list :c3q-app function argument))

(defun c3q-app-function (term)
  (cadr term))

(defun c3q-app-argument (term)
  (caddr term))

;; This is the source call-by-value predicate on valid terms.

(defun c3q-is-value-p (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((c3q-k-shape-p term)
    t)
   ((c3q-s-shape-p term)
    t)
   ((c3q-app-shape-p term)
    (let ((function (c3q-app-function term))
          (argument (c3q-app-argument term)))
      (and
       (c3q-term-p function)
       (c3q-term-p argument)
       (cond
        ((c3q-k-shape-p function)
         (c3q-is-value-p argument))
        ((c3q-s-shape-p function)
         (c3q-is-value-p argument))
        ((and
          (c3q-app-shape-p function)
          (c3q-s-shape-p
           (c3q-app-function function)))
         (and
          (c3q-is-value-p
           (c3q-app-argument function))
          (c3q-is-value-p argument)))
        (t nil)))))
   (t nil)))

;; Contexts are represented bijectively by the finite constructor records
;; (:C3Q-HOLE), (:C3Q-LEFT context term), and
;; (:C3Q-RIGHT term context).

(defun c3q-hole-shape-p (context)
  (equal context (list :c3q-hole)))

(defun c3q-left-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :c3q-left)))

(defun c3q-right-shape-p (context)
  (and
   (true-listp context)
   (equal (len context) 3)
   (equal (car context) :c3q-right)))

(defun c3q-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c3q-hole-shape-p context)
    t)
   ((c3q-left-shape-p context)
    (and
     (c3q-context-p (cadr context))
     (c3q-term-p (caddr context))))
   ((c3q-right-shape-p context)
    (and
     (c3q-term-p (cadr context))
     (c3q-context-p (caddr context))))
   (t nil)))

(defun c3q-hole ()
  (list :c3q-hole))

(defun c3q-left (context term)
  (list :c3q-left context term))

(defun c3q-right (term context)
  (list :c3q-right term context))

(defun c3q-left-context (context)
  (cadr context))

(defun c3q-left-term (context)
  (caddr context))

(defun c3q-right-term (context)
  (cadr context))

(defun c3q-right-context (context)
  (caddr context))

(defun c3q-is-context-p (context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c3q-hole-shape-p context)
    t)
   ((c3q-left-shape-p context)
    (and
     (c3q-term-p
      (c3q-left-term context))
     (c3q-is-context-p
      (c3q-left-context context))))
   ((c3q-right-shape-p context)
    (and
     (c3q-term-p
      (c3q-right-term context))
     (c3q-is-value-p
      (c3q-right-term context))
     (c3q-is-context-p
      (c3q-right-context context))))
   (t nil)))

(defun c3q-subst (context term)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c3q-hole-shape-p context)
    term)
   ((c3q-left-shape-p context)
    (c3q-app
     (c3q-subst
      (c3q-left-context context)
      term)
     (c3q-left-term context)))
   ((c3q-right-shape-p context)
    (c3q-app
     (c3q-right-term context)
     (c3q-subst
      (c3q-right-context context)
      term)))
   (t term)))

;; The source one-step relation is the union of its two inductive rules.

(defun-sk c3q-red-k-p (source target)
  (exists (context value1 value2)
    (and
     (c3q-context-p context)
     (c3q-term-p value1)
     (c3q-term-p value2)
     (c3q-is-context-p context)
     (c3q-is-value-p value1)
     (c3q-is-value-p value2)
     (equal
      source
      (c3q-subst
       context
       (c3q-app
        (c3q-app (c3q-k) value1)
        value2)))
     (equal
      target
      (c3q-subst context value1)))))

(defun-sk c3q-red-s-p (source target)
  (exists (context value1 value2 value3)
    (and
     (c3q-context-p context)
     (c3q-term-p value1)
     (c3q-term-p value2)
     (c3q-term-p value3)
     (c3q-is-context-p context)
     (c3q-is-value-p value1)
     (c3q-is-value-p value2)
     (c3q-is-value-p value3)
     (equal
      source
      (c3q-subst
       context
       (c3q-app
        (c3q-app
         (c3q-app (c3q-s) value1)
         value2)
        value3)))
     (equal
      target
      (c3q-subst
       context
       (c3q-app
        (c3q-app value1 value3)
        (c3q-app value2 value3)))))))

(defun c3q-one-step-p (source target)
  (and
   (c3q-term-p source)
   (c3q-term-p target)
   (or
    (c3q-red-k-p source target)
    (c3q-red-s-p source target))))

;; A nonempty finite term sequence is constructor evidence for the source
;; reflexive-transitive closure: a singleton is reflexivity, and each extra
;; element is one StepTransRefl application.

(defun c3q-term-list-p (terms)
  (if (consp terms)
      (and
       (c3q-term-p (car terms))
       (c3q-term-list-p (cdr terms)))
    (equal terms nil)))

(defun c3q-reduction-path-steps-p (terms)
  (if (and
       (consp terms)
       (consp (cdr terms)))
      (and
       (c3q-one-step-p
        (car terms)
        (cadr terms))
       (c3q-reduction-path-steps-p
        (cdr terms)))
    (and
     (consp terms)
     (equal (cdr terms) nil))))

(defun c3q-reduction-path-witness-p
    (terms source target)
  (and
   (c3q-term-list-p terms)
   (consp terms)
   (equal (car terms) source)
   (equal (car (last terms)) target)
   (c3q-reduction-path-steps-p terms)))

(defun-sk c3q-reltr-p (source target)
  (exists (terms)
    (and
     (c3q-term-p source)
     (c3q-term-p target)
     (c3q-reduction-path-witness-p
      terms source target))))

;; This is the source context-composition function and the implication
;; generated from its postcondition.

(defun c3q-subst-c (context inner-context)
  (declare (xargs :measure (acl2-count context)))
  (cond
   ((c3q-hole-shape-p context)
    inner-context)
   ((c3q-left-shape-p context)
    (c3q-left
     (c3q-subst-c
      (c3q-left-context context)
      inner-context)
     (c3q-left-term context)))
   ((c3q-right-shape-p context)
    (c3q-right
     (c3q-right-term context)
     (c3q-subst-c
      (c3q-right-context context)
      inner-context)))
   (t inner-context)))

(defun c3q-context-composition-spec-p
    (context inner-context)
  (implies
   (and
    (c3q-is-context-p context)
    (c3q-is-context-p inner-context))
   (c3q-is-context-p
    (c3q-subst-c context inner-context))))

;; On nonnegative integers this is definitionally the source function:
;; ks 0 = K and ks n = App (ks (n - 1)) K when n is positive.

(defun c3q-ks (n)
  (declare (xargs :measure (nfix n)))
  (if (and
       (integerp n)
       (< 0 n))
      (c3q-app
       (c3q-ks (- n 1))
       (c3q-k))
    (c3q-k)))

;; Exact target-native renderings of the constructor matches in the VC.

(defun c3q-k-or-app-k-p (term)
  (and
   (c3q-term-p term)
   (or
    (c3q-k-shape-p term)
    (and
     (c3q-app-shape-p term)
     (c3q-k-shape-p
      (c3q-app-function term))))))

(defun c3q-result-match-p
    (value1 value2 result)
  (cond
   ((c3q-k-shape-p value1)
    (equal
     result
     (c3q-app value1 value2)))
   ((and
     (c3q-app-shape-p value1)
     (c3q-k-shape-p
      (c3q-app-function value1)))
    (equal
     result
     (c3q-app-argument value1)))
   (t nil)))

;; The first conjunct of reduction3'vc preserves both nested universal
;; quantifiers over possible recursively computed values.

(defun-sk c3q-all-second-values-p
    (term2 context5 value1)
  (forall (value2)
    (implies
     (c3q-term-p value2)
     (implies
      (and
       (c3q-reltr-p
        (c3q-subst context5 term2)
        (c3q-subst context5 value2))
       (c3q-is-value-p value2)
       (implies
        (evenp 0)
        (equal value2 (c3q-k)))
       (implies
        (oddp 0)
        (equal
         value2
         (c3q-app (c3q-k) (c3q-k)))))
      (c3q-k-or-app-k-p value1)))))

(defun c3q-second-phase-obligation-p
    (n context term2 value1)
  (let* ((context4
          (c3q-right value1 (c3q-hole)))
         (context5
          (c3q-subst-c context context4)))
    (implies
     (c3q-context-composition-spec-p
      context context4)
     (and
      (<= 0 n)
      (< 0 n)
      (<= 0 0)
      (equal term2 (c3q-ks 0))
      (c3q-is-context-p context5)
      (c3q-all-second-values-p
       term2 context5 value1)))))

(defun-sk c3q-all-first-values-p
    (n context term1 term2 context3)
  (forall (value1)
    (implies
     (c3q-term-p value1)
     (implies
      (and
       (c3q-reltr-p
        (c3q-subst context3 term1)
        (c3q-subst context3 value1))
       (c3q-is-value-p value1)
       (implies
        (evenp (- n 1))
        (equal value1 (c3q-k)))
       (implies
        (oddp (- n 1))
        (equal
         value1
         (c3q-app (c3q-k) (c3q-k)))))
      (c3q-second-phase-obligation-p
       n context term2 value1)))))

(defun c3q-first-conjunct-p (n context)
  (let ((term (c3q-ks n)))
    (cond
     ((c3q-k-shape-p term)
      t)
     ((c3q-app-shape-p term)
      (let* ((term1
              (c3q-app-function term))
             (term2
              (c3q-app-argument term))
             (index1
              (- n 1))
             (context2
              (c3q-left (c3q-hole) term2))
             (context3
              (c3q-subst-c context context2)))
        (implies
         (c3q-context-composition-spec-p
          context context2)
         (and
          (<= 0 n)
          (< index1 n)
          (<= 0 index1)
          (equal term1 (c3q-ks index1))
          (c3q-is-context-p context3)
          (c3q-all-first-values-p
           n context term1 term2 context3)))))
     (t nil))))

;; The second conjunct preserves the source's existentially quantified
;; intermediate values inside the premise for each universally quantified
;; result.

(defun-sk c3q-second-value-exists-p
    (term2 context5 value1 result)
  (exists (value2)
    (and
     (c3q-term-p value2)
     (c3q-reltr-p
      (c3q-subst context5 term2)
      (c3q-subst context5 value2))
     (c3q-is-value-p value2)
     (implies
      (evenp 0)
      (equal value2 (c3q-k)))
     (implies
      (oddp 0)
      (equal
       value2
       (c3q-app (c3q-k) (c3q-k))))
     (c3q-result-match-p
      value1 value2 result))))

(defun-sk c3q-first-value-exists-p
    (n context term1 term2 context3 result)
  (exists (value1)
    (and
     (c3q-term-p value1)
     (c3q-reltr-p
      (c3q-subst context3 term1)
      (c3q-subst context3 value1))
     (c3q-is-value-p value1)
     (implies
      (evenp (- n 1))
      (equal value1 (c3q-k)))
     (implies
      (oddp (- n 1))
      (equal
       value1
       (c3q-app (c3q-k) (c3q-k))))
     (let* ((context4
             (c3q-right value1 (c3q-hole)))
            (context5
             (c3q-subst-c context context4)))
       (and
        (c3q-context-composition-spec-p
         context context4)
        (c3q-second-value-exists-p
         term2 context5 value1 result))))))

(defun c3q-result-premise-p
    (n context result)
  (let ((term (c3q-ks n)))
    (cond
     ((c3q-k-shape-p term)
      (equal result (c3q-k)))
     ((c3q-app-shape-p term)
      (let* ((term1
              (c3q-app-function term))
             (term2
              (c3q-app-argument term))
             (context2
              (c3q-left (c3q-hole) term2))
             (context3
              (c3q-subst-c context context2)))
        (and
         (c3q-context-composition-spec-p
          context context2)
         (c3q-first-value-exists-p
          n context term1 term2 context3 result))))
     (t nil))))

(defun-sk c3q-all-results-p (n context)
  (forall (result)
    (implies
     (c3q-term-p result)
     (implies
      (c3q-result-premise-p
       n context result)
      (and
       (c3q-reltr-p
        (c3q-subst context (c3q-ks n))
        (c3q-subst context result))
       (c3q-is-value-p result)
       (implies
        (evenp n)
        (equal result (c3q-k)))
       (implies
        (oddp n)
        (equal
         result
         (c3q-app (c3q-k) (c3q-k)))))))))

(defun
  ntp4vc-pearl-vstte12-combinators-combinators-reduction3qtvc-statement
  (n context)
  (implies
   (and
    (integerp n)
    (<= 0 n)
    (c3q-context-p context)
    (c3q-is-context-p context))
   (and
    (c3q-first-conjunct-p n context)
    (c3q-all-results-p n context))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
