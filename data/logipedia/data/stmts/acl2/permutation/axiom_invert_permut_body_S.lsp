;; Statement-only formalization of Logipedia corpus artifact
;; permutation.axiom_invert_permut_body_S, catalog title
;; "permutation.axiom_invert_permut_body_S": at every successor index, the
;; source's abstract equality relates the permutation-inversion body to the
;; natural function that returns the successor when m equals f at that
;; successor, and otherwise uses the preceding inversion. This file contains
;; no proof.

(in-package "ACL2")

;; Natural functions and higher-order values are reified by unrestricted
;; tokens with total natural-valued application operations.

(defstub logipedia-permutation-invert-body-s-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-invert-body-s-function-at
    (function natural)
  (nfix
   (logipedia-permutation-invert-body-s-raw-function-at
    function natural)))

(defstub logipedia-permutation-invert-body-s-raw-body-at
  (index function natural)
  t)

(defun logipedia-permutation-invert-body-s-body-at
    (index function natural)
  (nfix
   (logipedia-permutation-invert-body-s-raw-body-at
    index function natural)))

(defstub logipedia-permutation-invert-body-s-raw-invert-at
  (index function natural)
  t)

(defun logipedia-permutation-invert-body-s-invert-at
    (index function natural)
  (nfix
   (logipedia-permutation-invert-body-s-raw-invert-at
    index function natural)))

(defstub logipedia-permutation-invert-body-s-raw-higher-apply
  (value function natural)
  t)

;; Distinct value constructors represent invert_permut_body(S n) and the
;; source lambda on the right-hand side of the equality.

(defun logipedia-permutation-invert-body-s-body-value (index)
  (list 'logipedia-invert-permut-body-s (nfix index)))

(defun logipedia-permutation-invert-body-s-lambda-value (index)
  (list 'logipedia-invert-permut-body-s-lambda (nfix index)))

(defun logipedia-permutation-invert-body-s-higher-apply
    (value function natural)
  (cond
   ((and
     (true-listp value)
     (equal (len value) 2)
     (equal (car value) 'logipedia-invert-permut-body-s)
     (natp (cadr value)))
    (logipedia-permutation-invert-body-s-body-at
     (+ 1 (cadr value)) function natural))
   ((and
     (true-listp value)
     (equal (len value) 2)
     (equal (car value) 'logipedia-invert-permut-body-s-lambda)
     (natp (cadr value)))
    (if
     (equal
      (nfix natural)
      (logipedia-permutation-invert-body-s-function-at
       function (+ 1 (cadr value))))
     (+ 1 (cadr value))
     (logipedia-permutation-invert-body-s-invert-at
      (cadr value) function natural)))
   (t
    (nfix
     (logipedia-permutation-invert-body-s-raw-higher-apply
      value function natural)))))

;; Conservative interfaces reify the source's primitive equality and
;; predicates on the fixed higher-order value type.

(defstub logipedia-permutation-invert-body-s-source-equal-p
  (left right)
  t)

(defstub logipedia-permutation-invert-body-s-predicate-holds-p
  (predicate value)
  t)

(defun logipedia-permutation-invert-body-s-application-predicate
    (function natural expected)
  (list
   'logipedia-application-equality
   function
   (nfix natural)
   (nfix expected)))

(defun-sk
 logipedia-permutation-invert-body-s-application-semantics-p
 ()
 (forall (value function natural expected)
   (implies
    (and
     (natp natural)
     (natp expected))
    (iff
      (logipedia-permutation-invert-body-s-predicate-holds-p
      (logipedia-permutation-invert-body-s-application-predicate
       function natural expected)
      value)
     (equal
      (logipedia-permutation-invert-body-s-higher-apply
       value function natural)
      expected)))))

;; This is the imported equal_leibniz behavior of connectives.equal:
;; source equality transports every predicate on the higher-order type.

(defun-sk
 logipedia-permutation-invert-body-s-source-equal-leibniz-p
 ()
 (forall (left right predicate)
   (implies
    (logipedia-permutation-invert-body-s-source-equal-p
     left right)
    (implies
     (logipedia-permutation-invert-body-s-predicate-holds-p
      predicate left)
     (logipedia-permutation-invert-body-s-predicate-holds-p
      predicate right)))))

(defun-sk
 logipedia-permutation-axiom-invert-permut-body-s-source-equality-p
 ()
 (forall (index)
   (implies
    (natp index)
    (logipedia-permutation-invert-body-s-source-equal-p
     (logipedia-permutation-invert-body-s-body-value index)
     (logipedia-permutation-invert-body-s-lambda-value index)))))

(defun
 logipedia-permutation-axiom-invert-permut-body-s-statement
 ()
 (implies
  (and
   (logipedia-permutation-invert-body-s-application-semantics-p)
   (logipedia-permutation-invert-body-s-source-equal-leibniz-p))
  (logipedia-permutation-axiom-invert-permut-body-s-source-equality-p)))

(value-triple :itpeval-statement-checked)
:q
