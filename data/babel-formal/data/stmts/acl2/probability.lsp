;; Statement-only formalization of Babel-formal corpus artifact probability:
;; probability identities for arbitrary events over an arbitrary outcome type,
;; valued in an arbitrary commutative ring satisfying the source laws. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative interfaces represent the source's arbitrary types, events,
;; operations, probability function, and conditional-probability function.
;; Carrier predicates restrict quantifiers without enumerating any domain, and
;; function tags select arbitrary functions rather than finite lookup tables.

(defstub bf-pr-ring-member-p (ring-type value) t)
(defstub bf-pr-outcome-member-p (outcome-type value) t)
(defstub bf-pr-event-p (outcome-type event) t)
(defstub bf-pr-event-holds (outcome-type event outcome) t)

(defstub bf-pr-zero (ring-type) t)
(defstub bf-pr-one (ring-type) t)
(defstub bf-pr-add (ring-type left right) t)
(defstub bf-pr-mul (ring-type left right) t)
(defstub bf-pr-opp (ring-type value) t)

(defstub bf-pr-ev-false (outcome-type) t)
(defstub bf-pr-ev-true (outcome-type) t)
(defstub bf-pr-ev-inter (outcome-type left right) t)
(defstub bf-pr-ev-union (outcome-type left right) t)
(defstub bf-pr-ev-compl (outcome-type event) t)

(defstub bf-pr-prob
  (ring-type outcome-type prob-function event)
  t)
(defstub bf-pr-cprob
  (ring-type outcome-type cprob-function left right)
  t)

(defun bf-pr-sub (ring-type x y)
  (bf-pr-add ring-type x (bf-pr-opp ring-type y)))

(defun bf-pr-ev-diff (outcome-type a b)
  (bf-pr-ev-inter
   outcome-type a (bf-pr-ev-compl outcome-type b)))

;; Native ACL2 naturals and true lists present the source's Peano naturals and
;; inductive finite lists.

(defun bf-pr-mynat-add (n m)
  (if (zp n)
      m
    (+ 1 (bf-pr-mynat-add (- n 1) m))))

(defun bf-pr-event-list-p (outcome-type events)
  (if (consp events)
      (and
       (bf-pr-event-p outcome-type (car events))
       (bf-pr-event-list-p outcome-type (cdr events)))
    (equal events nil)))

(defun bf-pr-in-l-p (event events)
  (if (member-equal event events) t nil))

(defun bf-pr-no-duplicates-p (events)
  (if (consp events)
      (and
       (not (member-equal (car events) (cdr events)))
       (bf-pr-no-duplicates-p (cdr events)))
    (equal events nil)))

(defun bf-pr-no-dup-l-p (outcome-type events)
  (and
   (bf-pr-event-list-p outcome-type events)
   (bf-pr-no-duplicates-p events)))

;; Ring structure and the four additional negation laws hold over every member
;; of the arbitrary carrier. Closure records the source result types.

(defun-sk bf-pr-ring-laws-p (ring-type)
  (forall (x y z)
    (and
     (implies
      (bf-pr-ring-member-p ring-type x)
      (and
       (bf-pr-ring-member-p
        ring-type (bf-pr-opp ring-type x))
       (equal
        (bf-pr-add ring-type x (bf-pr-zero ring-type))
        x)
       (equal
        (bf-pr-add ring-type x (bf-pr-opp ring-type x))
        (bf-pr-zero ring-type))
       (equal
        (bf-pr-mul ring-type x (bf-pr-one ring-type))
        x)
       (equal
        (bf-pr-mul ring-type x (bf-pr-zero ring-type))
        (bf-pr-zero ring-type))
       (equal
        (bf-pr-opp ring-type (bf-pr-opp ring-type x))
        x)))
     (implies
      (and
       (bf-pr-ring-member-p ring-type x)
       (bf-pr-ring-member-p ring-type y))
      (and
       (bf-pr-ring-member-p
        ring-type (bf-pr-add ring-type x y))
       (bf-pr-ring-member-p
        ring-type (bf-pr-mul ring-type x y))
       (equal
        (bf-pr-add ring-type x y)
        (bf-pr-add ring-type y x))
       (equal
        (bf-pr-mul ring-type x y)
        (bf-pr-mul ring-type y x))
       (implies
        (equal
         (bf-pr-mul ring-type x y)
         (bf-pr-zero ring-type))
        (or
         (equal x (bf-pr-zero ring-type))
         (equal y (bf-pr-zero ring-type))))
       (equal
        (bf-pr-mul ring-type x (bf-pr-opp ring-type y))
        (bf-pr-opp
         ring-type (bf-pr-mul ring-type x y)))
       (equal
        (bf-pr-mul ring-type (bf-pr-opp ring-type x) y)
        (bf-pr-opp
         ring-type (bf-pr-mul ring-type x y)))))
     (implies
      (and
       (bf-pr-ring-member-p ring-type x)
       (bf-pr-ring-member-p ring-type y)
       (bf-pr-ring-member-p ring-type z))
      (and
       (equal
        (bf-pr-add
         ring-type (bf-pr-add ring-type x y) z)
        (bf-pr-add
         ring-type x (bf-pr-add ring-type y z)))
       (equal
        (bf-pr-mul
         ring-type (bf-pr-mul ring-type x y) z)
        (bf-pr-mul
         ring-type x (bf-pr-mul ring-type y z)))
       (equal
        (bf-pr-mul
         ring-type x (bf-pr-add ring-type y z))
        (bf-pr-add
         ring-type
         (bf-pr-mul ring-type x y)
         (bf-pr-mul ring-type x z))))))))

(defun bf-pr-ring-p (ring-type)
  (and
   (bf-pr-ring-member-p
    ring-type (bf-pr-zero ring-type))
   (bf-pr-ring-member-p
    ring-type (bf-pr-one ring-type))
   (not
    (equal
     (bf-pr-one ring-type)
     (bf-pr-zero ring-type)))
   (equal
    (bf-pr-opp ring-type (bf-pr-zero ring-type))
    (bf-pr-zero ring-type))
   (bf-pr-ring-laws-p ring-type)))

;; Event objects are reified predicates. Evaluation and extensionality give
;; them function-like equality on the arbitrary outcome carrier; the Boolean
;; constructors have their pointwise source meanings and remain events.

(defun-sk bf-pr-event-ext-equal-p (outcome-type a b)
  (forall (outcome)
    (implies
     (bf-pr-outcome-member-p outcome-type outcome)
     (iff
      (bf-pr-event-holds outcome-type a outcome)
      (bf-pr-event-holds outcome-type b outcome)))))

(defun-sk bf-pr-event-laws-p (outcome-type)
  (forall (a b outcome)
    (and
     (implies
      (bf-pr-event-p outcome-type a)
      (and
       (bf-pr-event-p
        outcome-type (bf-pr-ev-compl outcome-type a))
       (implies
        (bf-pr-outcome-member-p outcome-type outcome)
        (iff
         (bf-pr-event-holds
          outcome-type
          (bf-pr-ev-compl outcome-type a)
          outcome)
         (not
          (bf-pr-event-holds outcome-type a outcome))))))
     (implies
      (and
       (bf-pr-event-p outcome-type a)
       (bf-pr-event-p outcome-type b))
      (and
       (bf-pr-event-p
        outcome-type (bf-pr-ev-inter outcome-type a b))
       (bf-pr-event-p
        outcome-type (bf-pr-ev-union outcome-type a b))
       (implies
        (bf-pr-outcome-member-p outcome-type outcome)
        (and
         (iff
          (bf-pr-event-holds
           outcome-type
           (bf-pr-ev-inter outcome-type a b)
           outcome)
          (and
           (bf-pr-event-holds outcome-type a outcome)
           (bf-pr-event-holds outcome-type b outcome)))
         (iff
          (bf-pr-event-holds
           outcome-type
           (bf-pr-ev-union outcome-type a b)
           outcome)
          (or
           (bf-pr-event-holds outcome-type a outcome)
           (bf-pr-event-holds outcome-type b outcome)))))
       (implies
        (bf-pr-event-ext-equal-p outcome-type a b)
        (equal a b))))
     (implies
      (bf-pr-outcome-member-p outcome-type outcome)
      (and
       (not
        (bf-pr-event-holds
         outcome-type
         (bf-pr-ev-false outcome-type)
         outcome))
       (bf-pr-event-holds
        outcome-type
        (bf-pr-ev-true outcome-type)
        outcome))))))

(defun bf-pr-event-space-p (outcome-type)
  (and
   (bf-pr-event-p
    outcome-type (bf-pr-ev-false outcome-type))
   (bf-pr-event-p
    outcome-type (bf-pr-ev-true outcome-type))
   (bf-pr-event-laws-p outcome-type)))

(defun-sk bf-pr-disjoint-p (outcome-type a b)
  (forall (outcome)
    (implies
     (bf-pr-outcome-member-p outcome-type outcome)
     (not
      (and
       (bf-pr-event-holds outcome-type a outcome)
       (bf-pr-event-holds outcome-type b outcome))))))

(defun bf-pr-disjoint-with-all-p (outcome-type a events)
  (if (consp events)
      (and
       (bf-pr-disjoint-p outcome-type a (car events))
       (bf-pr-disjoint-with-all-p
        outcome-type a (cdr events)))
    (equal events nil)))

(defun bf-pr-pairwise-disjoint-p (outcome-type events)
  (if (consp events)
      (and
       (bf-pr-disjoint-with-all-p
        outcome-type (car events) (cdr events))
       (bf-pr-pairwise-disjoint-p
        outcome-type (cdr events)))
    (equal events nil)))

(defun bf-pr-big-union (outcome-type events)
  (if (consp events)
      (bf-pr-ev-union
       outcome-type
       (car events)
       (bf-pr-big-union outcome-type (cdr events)))
    (bf-pr-ev-false outcome-type)))

;; Probability and conditional probability are arbitrary tagged functions.
;; Their result typing, extensionality, and all base source axioms are explicit.

(defun-sk bf-pr-probability-laws-p
    (ring-type outcome-type prob-function cprob-function)
  (forall (a b)
    (and
     (implies
      (bf-pr-event-p outcome-type a)
      (and
       (bf-pr-ring-member-p
        ring-type
        (bf-pr-prob
         ring-type outcome-type prob-function a))
       (equal
        (bf-pr-prob
         ring-type
         outcome-type
         prob-function
         (bf-pr-ev-compl outcome-type a))
        (bf-pr-add
         ring-type
         (bf-pr-one ring-type)
         (bf-pr-opp
          ring-type
          (bf-pr-prob
           ring-type outcome-type prob-function a))))))
     (implies
      (and
       (bf-pr-event-p outcome-type a)
       (bf-pr-event-p outcome-type b))
      (and
       (bf-pr-ring-member-p
        ring-type
        (bf-pr-cprob
         ring-type outcome-type cprob-function a b))
       (implies
        (bf-pr-event-ext-equal-p outcome-type a b)
        (equal
         (bf-pr-prob
          ring-type outcome-type prob-function a)
         (bf-pr-prob
          ring-type outcome-type prob-function b)))
       (equal
        (bf-pr-prob
         ring-type
         outcome-type
         prob-function
         (bf-pr-ev-union outcome-type a b))
        (bf-pr-add
         ring-type
         (bf-pr-prob
          ring-type outcome-type prob-function a)
         (bf-pr-add
          ring-type
          (bf-pr-prob
           ring-type outcome-type prob-function b)
          (bf-pr-opp
           ring-type
           (bf-pr-prob
            ring-type
            outcome-type
            prob-function
            (bf-pr-ev-inter outcome-type a b))))))
       (equal
        (bf-pr-prob
         ring-type
         outcome-type
         prob-function
         (bf-pr-ev-inter outcome-type a b))
        (bf-pr-mul
         ring-type
         (bf-pr-cprob
          ring-type outcome-type cprob-function a b)
         (bf-pr-prob
          ring-type outcome-type prob-function b))))))))

(defun bf-pr-base-context-p
    (ring-type outcome-type prob-function cprob-function)
  (and
   (bf-pr-ring-p ring-type)
   (bf-pr-event-space-p outcome-type)
   (equal
    (bf-pr-prob
     ring-type
     outcome-type
     prob-function
     (bf-pr-ev-false outcome-type))
    (bf-pr-zero ring-type))
   (equal
    (bf-pr-prob
     ring-type
     outcome-type
     prob-function
     (bf-pr-ev-true outcome-type))
    (bf-pr-one ring-type))
   (bf-pr-probability-laws-p
    ring-type outcome-type prob-function cprob-function)))

(defun bf-pr-indep-p
    (ring-type outcome-type prob-function a b)
  (equal
   (bf-pr-prob
    ring-type
    outcome-type
    prob-function
    (bf-pr-ev-inter outcome-type a b))
   (bf-pr-mul
    ring-type
    (bf-pr-prob
     ring-type outcome-type prob-function a)
    (bf-pr-prob
     ring-type outcome-type prob-function b))))

(defun bf-pr-map-prob
    (ring-type outcome-type prob-function events)
  (if (consp events)
      (cons
       (bf-pr-prob
        ring-type
        outcome-type
        prob-function
        (car events))
       (bf-pr-map-prob
        ring-type
        outcome-type
        prob-function
        (cdr events)))
    nil))

(defun bf-pr-fold-add (ring-type values)
  (if (consp values)
      (bf-pr-add
       ring-type
       (car values)
       (bf-pr-fold-add ring-type (cdr values)))
    (bf-pr-zero ring-type)))

(defun-sk bf-pr-all-prob-zero-p
    (ring-type outcome-type prob-function events)
  (forall (event)
    (implies
     (bf-pr-in-l-p event events)
     (equal
      (bf-pr-prob
       ring-type outcome-type prob-function event)
      (bf-pr-zero ring-type)))))

;; These predicates are source axioms extending the base probability setup.
;; Separation keeps every standalone axiom statement out of its own premises.

(defun-sk bf-pr-prob-union-disjoint-axiom-p
    (ring-type outcome-type prob-function)
  (forall (a b)
    (implies
     (and
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-disjoint-p outcome-type a b))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-union outcome-type a b))
      (bf-pr-add
       ring-type
       (bf-pr-prob
        ring-type outcome-type prob-function a)
       (bf-pr-prob
        ring-type outcome-type prob-function b))))))

(defun-sk bf-pr-disjoint-head-tail-axiom-p (outcome-type)
  (forall (a events)
    (implies
     (and
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-list-p outcome-type events)
      (bf-pr-pairwise-disjoint-p
       outcome-type (cons a events)))
     (bf-pr-disjoint-p
      outcome-type
      a
      (bf-pr-big-union outcome-type events)))))

(defun-sk bf-pr-indep-compl-both-axiom-p
    (ring-type outcome-type prob-function)
  (forall (a b)
    (implies
     (and
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-indep-p
       ring-type outcome-type prob-function a b))
     (bf-pr-indep-p
      ring-type
      outcome-type
      prob-function
      (bf-pr-ev-compl outcome-type a)
      (bf-pr-ev-compl outcome-type b)))))

(defun bf-pr-inclusion-exclusion-formula-p
    (ring-type outcome-type prob-function a b c)
  (equal
   (bf-pr-prob
    ring-type
    outcome-type
    prob-function
    (bf-pr-ev-union
     outcome-type
     (bf-pr-ev-union outcome-type a b)
     c))
   (bf-pr-add
    ring-type
    (bf-pr-prob
     ring-type outcome-type prob-function a)
    (bf-pr-add
     ring-type
     (bf-pr-prob
      ring-type outcome-type prob-function b)
     (bf-pr-add
      ring-type
      (bf-pr-prob
       ring-type outcome-type prob-function c)
      (bf-pr-opp
       ring-type
       (bf-pr-add
        ring-type
        (bf-pr-prob
         ring-type
         outcome-type
         prob-function
         (bf-pr-ev-inter outcome-type a b))
        (bf-pr-add
         ring-type
         (bf-pr-prob
          ring-type
          outcome-type
          prob-function
          (bf-pr-ev-inter outcome-type a c))
         (bf-pr-add
          ring-type
          (bf-pr-prob
           ring-type
           outcome-type
           prob-function
           (bf-pr-ev-inter outcome-type b c))
          (bf-pr-opp
           ring-type
           (bf-pr-prob
            ring-type
            outcome-type
            prob-function
            (bf-pr-ev-inter
             outcome-type
             (bf-pr-ev-inter outcome-type a b)
             c))))))))))))

(defun-sk bf-pr-inclusion-exclusion-axiom-p
    (ring-type outcome-type prob-function)
  (forall (a b c)
    (implies
     (and
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-event-p outcome-type c))
     (bf-pr-inclusion-exclusion-formula-p
      ring-type outcome-type prob-function a b c))))

(defun bf-pr-full-context-p
    (ring-type outcome-type prob-function cprob-function)
  (and
   (bf-pr-base-context-p
    ring-type outcome-type prob-function cprob-function)
   (bf-pr-prob-union-disjoint-axiom-p
    ring-type outcome-type prob-function)
   (bf-pr-disjoint-head-tail-axiom-p outcome-type)
   (bf-pr-indep-compl-both-axiom-p
    ring-type outcome-type prob-function)
   (bf-pr-inclusion-exclusion-axiom-p
    ring-type outcome-type prob-function)))

;; Peano-natural equations.

(defun-sk babel-formal-probability-mynat-add-o-left-statement ()
  (forall (m)
    (implies
     (natp m)
     (equal (bf-pr-mynat-add 0 m) m))))

(defun-sk babel-formal-probability-mynat-add-s-left-statement ()
  (forall (n m)
    (implies
     (and (natp n) (natp m))
     (equal
      (bf-pr-mynat-add (+ 1 n) m)
      (+ 1 (bf-pr-mynat-add n m))))))

;; Pointwise event-algebra statements.

(defun-sk babel-formal-probability-ev-inter-comm-statement ()
  (forall (outcome-type a b outcome)
    (implies
     (and
      (bf-pr-event-space-p outcome-type)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-outcome-member-p outcome-type outcome))
     (iff
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-inter outcome-type a b)
       outcome)
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-inter outcome-type b a)
       outcome)))))

(defun-sk babel-formal-probability-ev-union-comm-statement ()
  (forall (outcome-type a b outcome)
    (implies
     (and
      (bf-pr-event-space-p outcome-type)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-outcome-member-p outcome-type outcome))
     (iff
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-union outcome-type a b)
       outcome)
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-union outcome-type b a)
       outcome)))))

(defun-sk babel-formal-probability-ev-inter-assoc-statement ()
  (forall (outcome-type a b c outcome)
    (implies
     (and
      (bf-pr-event-space-p outcome-type)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-event-p outcome-type c)
      (bf-pr-outcome-member-p outcome-type outcome))
     (iff
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-inter
        outcome-type
        (bf-pr-ev-inter outcome-type a b)
        c)
       outcome)
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-inter
        outcome-type
        a
        (bf-pr-ev-inter outcome-type b c))
       outcome)))))

(defun-sk babel-formal-probability-ev-union-assoc-statement ()
  (forall (outcome-type a b c outcome)
    (implies
     (and
      (bf-pr-event-space-p outcome-type)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-event-p outcome-type c)
      (bf-pr-outcome-member-p outcome-type outcome))
     (iff
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-union
        outcome-type
        (bf-pr-ev-union outcome-type a b)
        c)
       outcome)
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-union
        outcome-type
        a
        (bf-pr-ev-union outcome-type b c))
       outcome)))))

(defun-sk
    babel-formal-probability-ev-inter-distrib-left-statement ()
  (forall (outcome-type a b c outcome)
    (implies
     (and
      (bf-pr-event-space-p outcome-type)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-event-p outcome-type c)
      (bf-pr-outcome-member-p outcome-type outcome))
     (iff
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-inter
        outcome-type
        a
        (bf-pr-ev-union outcome-type b c))
       outcome)
      (bf-pr-event-holds
       outcome-type
       (bf-pr-ev-union
        outcome-type
        (bf-pr-ev-inter outcome-type a b)
        (bf-pr-ev-inter outcome-type a c))
       outcome)))))

;; Standalone source axioms use only the assumptions preceding each axiom.

(defun-sk
    babel-formal-probability-disjoint-head-tail-statement ()
  (forall (outcome-type a events)
    (implies
     (and
      (bf-pr-event-space-p outcome-type)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-list-p outcome-type events)
      (bf-pr-pairwise-disjoint-p
       outcome-type (cons a events)))
     (bf-pr-disjoint-p
      outcome-type
      a
      (bf-pr-big-union outcome-type events)))))

(defun-sk
    babel-formal-probability-prob-union-disjoint-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-base-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-disjoint-p outcome-type a b))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-union outcome-type a b))
      (bf-pr-add
       ring-type
       (bf-pr-prob
        ring-type outcome-type prob-function a)
       (bf-pr-prob
        ring-type outcome-type prob-function b))))))

;; Probability identities under the complete source setup.

(defun-sk babel-formal-probability-prob-union-comm-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-union outcome-type a b))
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-union outcome-type b a))))))

(defun-sk babel-formal-probability-prob-union-idem-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-union outcome-type a a))
      (bf-pr-prob
       ring-type outcome-type prob-function a)))))

(defun-sk babel-formal-probability-prob-diff-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-diff outcome-type a b))
      (bf-pr-sub
       ring-type
       (bf-pr-prob
        ring-type outcome-type prob-function a)
       (bf-pr-prob
        ring-type
        outcome-type
        prob-function
        (bf-pr-ev-inter outcome-type a b)))))))

(defun-sk babel-formal-probability-bayes-symm-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b))
     (equal
      (bf-pr-mul
       ring-type
       (bf-pr-cprob
        ring-type outcome-type cprob-function a b)
       (bf-pr-prob
        ring-type outcome-type prob-function b))
      (bf-pr-mul
       ring-type
       (bf-pr-cprob
        ring-type outcome-type cprob-function b a)
       (bf-pr-prob
        ring-type outcome-type prob-function a))))))

(defun-sk babel-formal-probability-law-total-prob-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b))
     (equal
      (bf-pr-prob
       ring-type outcome-type prob-function a)
      (bf-pr-add
       ring-type
       (bf-pr-mul
        ring-type
        (bf-pr-cprob
         ring-type outcome-type cprob-function a b)
        (bf-pr-prob
         ring-type outcome-type prob-function b))
       (bf-pr-mul
        ring-type
        (bf-pr-cprob
         ring-type
         outcome-type
         cprob-function
         a
         (bf-pr-ev-compl outcome-type b))
        (bf-pr-prob
         ring-type
         outcome-type
         prob-function
         (bf-pr-ev-compl outcome-type b))))))))

(defun-sk babel-formal-probability-prob-union-indep-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-indep-p
       ring-type outcome-type prob-function a b))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-ev-union outcome-type a b))
      (bf-pr-add
       ring-type
       (bf-pr-prob
        ring-type outcome-type prob-function a)
       (bf-pr-add
        ring-type
        (bf-pr-prob
         ring-type outcome-type prob-function b)
        (bf-pr-opp
         ring-type
         (bf-pr-mul
          ring-type
          (bf-pr-prob
           ring-type outcome-type prob-function a)
          (bf-pr-prob
           ring-type outcome-type prob-function b)))))))))

(defun-sk babel-formal-probability-indep-compl-right-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-indep-p
       ring-type outcome-type prob-function a b))
     (bf-pr-indep-p
      ring-type
      outcome-type
      prob-function
      a
      (bf-pr-ev-compl outcome-type b)))))

(defun-sk babel-formal-probability-indep-symm-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-indep-p
       ring-type outcome-type prob-function a b))
     (bf-pr-indep-p
      ring-type outcome-type prob-function b a))))

(defun-sk babel-formal-probability-indep-compl-left-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-indep-p
       ring-type outcome-type prob-function a b))
     (bf-pr-indep-p
      ring-type
      outcome-type
      prob-function
      (bf-pr-ev-compl outcome-type a)
      b))))

(defun-sk babel-formal-probability-indep-compl-both-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b)
    (implies
     (and
      (bf-pr-base-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-indep-p
       ring-type outcome-type prob-function a b))
     (bf-pr-indep-p
      ring-type
      outcome-type
      prob-function
      (bf-pr-ev-compl outcome-type a)
      (bf-pr-ev-compl outcome-type b)))))

(defun-sk
    babel-formal-probability-prob-big-union-disjoint-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function events)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-list-p outcome-type events)
      (bf-pr-pairwise-disjoint-p outcome-type events))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-big-union outcome-type events))
      (bf-pr-fold-add
       ring-type
       (bf-pr-map-prob
        ring-type
        outcome-type
        prob-function
        events))))))

(defun-sk
    babel-formal-probability-prob-big-union-disjoint-zero-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function events)
    (implies
     (and
      (bf-pr-full-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-list-p outcome-type events)
      (bf-pr-pairwise-disjoint-p outcome-type events)
      (bf-pr-all-prob-zero-p
       ring-type outcome-type prob-function events))
     (equal
      (bf-pr-prob
       ring-type
       outcome-type
       prob-function
       (bf-pr-big-union outcome-type events))
      (bf-pr-zero ring-type)))))

(defun-sk
    babel-formal-probability-inclusion-exclusion-three-statement ()
  (forall
    (ring-type outcome-type prob-function cprob-function a b c)
    (implies
     (and
      (bf-pr-base-context-p
       ring-type outcome-type prob-function cprob-function)
      (bf-pr-event-p outcome-type a)
      (bf-pr-event-p outcome-type b)
      (bf-pr-event-p outcome-type c))
     (bf-pr-inclusion-exclusion-formula-p
      ring-type outcome-type prob-function a b c))))

(defun babel-formal-probability-statement ()
  (and
   (babel-formal-probability-mynat-add-o-left-statement)
   (babel-formal-probability-mynat-add-s-left-statement)
   (babel-formal-probability-ev-inter-comm-statement)
   (babel-formal-probability-ev-union-comm-statement)
   (babel-formal-probability-ev-inter-assoc-statement)
   (babel-formal-probability-ev-union-assoc-statement)
   (babel-formal-probability-ev-inter-distrib-left-statement)
   (babel-formal-probability-disjoint-head-tail-statement)
   (babel-formal-probability-prob-union-disjoint-statement)
   (babel-formal-probability-prob-union-comm-statement)
   (babel-formal-probability-prob-union-idem-statement)
   (babel-formal-probability-prob-diff-statement)
   (babel-formal-probability-bayes-symm-statement)
   (babel-formal-probability-law-total-prob-statement)
   (babel-formal-probability-prob-union-indep-statement)
   (babel-formal-probability-indep-compl-right-statement)
   (babel-formal-probability-indep-symm-statement)
   (babel-formal-probability-indep-compl-left-statement)
   (babel-formal-probability-indep-compl-both-statement)
   (babel-formal-probability-prob-big-union-disjoint-statement)
   (babel-formal-probability-prob-big-union-disjoint-zero-statement)
   (babel-formal-probability-inclusion-exclusion-three-statement)))

(value-triple :itpeval-statement-checked)
:q
