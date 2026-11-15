;; Statement-only formalization of Logipedia corpus artifact
;; permutation.axiom_invert_permut_body_O, catalog title
;; "permutation.axiom_invert_permut_body_O": the source's abstract equality
;; relates the permutation-inversion body at zero to the natural function
;; that selects zero in both branches after comparing m with f(0). This file
;; contains no proof.

(in-package "ACL2")

;; Natural functions and higher-order values are reified by unrestricted
;; tokens with total natural-valued application operations.

(defstub logipedia-permutation-invert-body-o-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-invert-body-o-function-at
    (function natural)
  (nfix
   (logipedia-permutation-invert-body-o-raw-function-at
    function natural)))

(defstub logipedia-permutation-invert-body-o-raw-body-at
  (index function natural)
  t)

(defun logipedia-permutation-invert-body-o-body-at
    (index function natural)
  (nfix
   (logipedia-permutation-invert-body-o-raw-body-at
    index function natural)))

(defstub logipedia-permutation-invert-body-o-raw-higher-apply
  (value function natural)
  t)

;; Distinct value constructors represent invert_permut_body(0) and the
;; source lambda on the right-hand side of the equality.

(defun logipedia-permutation-invert-body-o-body-value ()
  (list 'logipedia-invert-permut-body 0))

(defun logipedia-permutation-invert-body-o-lambda-value ()
  (list 'logipedia-invert-permut-body-o-lambda))

(defun logipedia-permutation-invert-body-o-higher-apply
    (value function natural)
  (cond
   ((equal
     value
     (logipedia-permutation-invert-body-o-body-value))
    (logipedia-permutation-invert-body-o-body-at
     0 function natural))
   ((equal
     value
     (logipedia-permutation-invert-body-o-lambda-value))
    (if
     (equal
      natural
      (logipedia-permutation-invert-body-o-function-at
       function 0))
     0
     0))
   (t
    (nfix
     (logipedia-permutation-invert-body-o-raw-higher-apply
      value function natural)))))

;; Conservative interfaces reify the source's primitive equality and
;; predicates on the fixed higher-order value type.

(defstub logipedia-permutation-invert-body-o-source-equal-p
  (left right)
  t)

(defstub logipedia-permutation-invert-body-o-predicate-holds-p
  (predicate value)
  t)

(defun logipedia-permutation-invert-body-o-application-predicate
    (function natural expected)
  (list
   'logipedia-application-equality
   function natural expected))

(defun-sk
 logipedia-permutation-invert-body-o-application-semantics-p
 ()
 (forall (value function natural expected)
   (implies
    (and
     (natp natural)
     (natp expected))
    (iff
     (logipedia-permutation-invert-body-o-predicate-holds-p
      (logipedia-permutation-invert-body-o-application-predicate
       function natural expected)
      value)
     (equal
      (logipedia-permutation-invert-body-o-higher-apply
       value function natural)
      expected)))))

;; This is the imported equal_leibniz behavior of connectives.equal:
;; source equality transports every predicate on the higher-order type.

(defun-sk
 logipedia-permutation-invert-body-o-source-equal-leibniz-p
 ()
 (forall (left right predicate)
   (implies
    (logipedia-permutation-invert-body-o-source-equal-p
     left right)
    (implies
     (logipedia-permutation-invert-body-o-predicate-holds-p
      predicate left)
     (logipedia-permutation-invert-body-o-predicate-holds-p
      predicate right)))))

(defun
 logipedia-permutation-axiom-invert-permut-body-o-statement
 ()
 (implies
  (and
   (logipedia-permutation-invert-body-o-application-semantics-p)
   (logipedia-permutation-invert-body-o-source-equal-leibniz-p))
  (logipedia-permutation-invert-body-o-source-equal-p
   (logipedia-permutation-invert-body-o-body-value)
   (logipedia-permutation-invert-body-o-lambda-value))))

(value-triple :itpeval-statement-checked)
:q
