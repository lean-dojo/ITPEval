;; Statement-only formalization of Logipedia corpus artifact
;; permutation.axiom_invert_permut, catalog title
;; "permutation.axiom_invert_permut": for every natural index, the source's
;; primitive equality relates the permutation-inversion higher-order value to
;; the natural-filtered inversion-body value. This file contains no proof.

(in-package "ACL2")

;; Natural functions and the higher-order values that consume them are
;; reified by tokens with total natural-valued application operations.

(defstub logipedia-permutation-invert-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-invert-function-at
    (function natural)
  (nfix
   (logipedia-permutation-invert-raw-function-at
    function natural)))

(defstub logipedia-permutation-invert-raw-higher-apply
  (value function natural)
  t)

(defun logipedia-permutation-invert-higher-apply
    (value function natural)
  (nfix
   (logipedia-permutation-invert-raw-higher-apply
    value function natural)))

;; Structured value constructors keep the three source objects distinct.

(defun logipedia-permutation-invert-permut-value (index)
  (list 'logipedia-invert-permut index))

(defun logipedia-permutation-invert-permut-body-value (index)
  (list 'logipedia-invert-permut-body index))

(defun logipedia-permutation-filtered-invert-permut-body-value
    (index)
  (list 'logipedia-filtered-invert-permut-body index))

;; These application functions definitionally connect each value token to its
;; action on a reified natural-to-natural function and a natural argument.

(defun logipedia-permutation-invert-permut-at
    (index function natural)
  (logipedia-permutation-invert-higher-apply
   (logipedia-permutation-invert-permut-value index)
   function natural))

(defun logipedia-permutation-invert-permut-body-at
    (index function natural)
  (logipedia-permutation-invert-higher-apply
   (logipedia-permutation-invert-permut-body-value index)
   function natural))

(defun logipedia-permutation-filtered-invert-permut-body-at
    (index function natural)
  (logipedia-permutation-invert-higher-apply
   (logipedia-permutation-filtered-invert-permut-body-value index)
   function natural))

;; Conservative interfaces reify the source's primitive equality and every
;; predicate on the fixed higher-order value type.

(defstub logipedia-permutation-invert-source-equal-p
  (left right)
  t)

(defstub logipedia-permutation-invert-predicate-holds-p
  (predicate value)
  t)

;; This constructor supplies the predicates that observe application at any
;; reified input. Its semantics makes pointwise equality derivable from
;; Leibniz transport rather than assuming pointwise equality directly.

(defun logipedia-permutation-invert-application-equality-predicate
    (function natural expected)
  (list
   'logipedia-application-equality
   function natural expected))

(defun-sk logipedia-permutation-invert-application-predicate-semantics-p
    ()
  (forall (value function natural expected)
    (implies
     (and
      (natp natural)
      (natp expected))
     (iff
      (logipedia-permutation-invert-predicate-holds-p
       (logipedia-permutation-invert-application-equality-predicate
        function natural expected)
       value)
      (equal
       (logipedia-permutation-invert-higher-apply
        value function natural)
       expected)))))

;; This is the full equal_leibniz interface: source equality transports every
;; predicate on the higher-order value type. Application predicates above are
;; only one family among the universally quantified predicates.

(defun-sk logipedia-permutation-invert-source-equal-leibniz-p ()
  (forall (left right predicate)
    (implies
     (logipedia-permutation-invert-source-equal-p left right)
     (implies
      (logipedia-permutation-invert-predicate-holds-p
       predicate left)
      (logipedia-permutation-invert-predicate-holds-p
       predicate right)))))

;; The nat module gives Leibniz transport from filter_nat_type body n to
;; body n and, by symmetry, back again. This bidirectional condition retains
;; the filtered value as a distinct object while justifying either transport.

(defun-sk logipedia-permutation-invert-filter-bidirectional-transport-p
    ()
  (forall (index predicate)
    (implies
     (natp index)
     (iff
      (logipedia-permutation-invert-predicate-holds-p
       predicate
       (logipedia-permutation-filtered-invert-permut-body-value
        index))
      (logipedia-permutation-invert-predicate-holds-p
       predicate
       (logipedia-permutation-invert-permut-body-value
        index))))))

(defun-sk logipedia-permutation-axiom-invert-permut-source-equality-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-permutation-invert-source-equal-p
      (logipedia-permutation-invert-permut-value index)
      (logipedia-permutation-filtered-invert-permut-body-value
       index)))))

(defun logipedia-permutation-axiom-invert-permut-statement ()
  (implies
   (and
    (logipedia-permutation-invert-application-predicate-semantics-p)
    (logipedia-permutation-invert-source-equal-leibniz-p)
    (logipedia-permutation-invert-filter-bidirectional-transport-p))
   (logipedia-permutation-axiom-invert-permut-source-equality-p)))

(value-triple :itpeval-statement-checked)
:q
