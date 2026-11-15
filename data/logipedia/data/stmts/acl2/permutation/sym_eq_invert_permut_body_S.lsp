;; Statement-only formalization of Logipedia corpus artifact
;; permutation.sym_eq_invert_permut_body_S, catalog title
;; "permutation.sym_eq_invert_permut_body_S": at every successor index, the
;; natural function that returns the successor when m equals f at that
;; successor, and otherwise uses the preceding permutation inversion, is
;; Leibniz-equal to the permutation-inversion body. This file contains no
;; proof.

(in-package "ACL2")

;; Natural functions and the higher-order values that consume them are
;; reified by unrestricted ACL2 objects with total natural-valued application.

(defstub logipedia-permutation-sym-eq-invert-body-s-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-sym-eq-invert-body-s-function-at
    (function natural)
  (nfix
   (logipedia-permutation-sym-eq-invert-body-s-raw-function-at
    function natural)))

(defstub logipedia-permutation-sym-eq-invert-body-s-raw-invert-at
  (index function natural)
  t)

(defun logipedia-permutation-sym-eq-invert-body-s-invert-at
    (index function natural)
  (nfix
   (logipedia-permutation-sym-eq-invert-body-s-raw-invert-at
    index function natural)))

(defstub logipedia-permutation-sym-eq-invert-body-s-invert-permut-body
  (index)
  t)

(defstub logipedia-permutation-sym-eq-invert-body-s-generic-apply
  (function-value function natural)
  t)

(defun logipedia-permutation-sym-eq-invert-body-s-successor-function
    (index)
  (list
   'logipedia-permutation-sym-eq-invert-body-s-successor-function
   (nfix index)))

(defun logipedia-permutation-sym-eq-invert-body-s-apply
    (function-value function natural)
  (if
      (and
       (true-listp function-value)
       (equal (len function-value) 2)
       (equal
        (car function-value)
        'logipedia-permutation-sym-eq-invert-body-s-successor-function)
       (natp (cadr function-value)))
      (if
       (equal
        (nfix natural)
        (logipedia-permutation-sym-eq-invert-body-s-function-at
         function (+ 1 (cadr function-value))))
       (+ 1 (cadr function-value))
       (logipedia-permutation-sym-eq-invert-body-s-invert-at
        (cadr function-value) function natural))
    (logipedia-permutation-sym-eq-invert-body-s-generic-apply
     function-value function natural)))

(defun-sk logipedia-permutation-sym-eq-invert-body-s-function-value-p
    (function-value)
  (forall (function natural)
    (implies
     (natp natural)
     (natp
      (logipedia-permutation-sym-eq-invert-body-s-apply
       function-value function natural)))))

(defun-sk logipedia-permutation-sym-eq-invert-body-s-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-permutation-sym-eq-invert-body-s-function-value-p
      (logipedia-permutation-sym-eq-invert-body-s-invert-permut-body
       index)))))

;; Identity of the reified higher-order values is exactly source Leibniz
;; equality: identity transports every predicate, and the converse follows
;; by choosing the predicate that tests identity with the left value.

(defun-sk logipedia-permutation-sym-eq-invert-permut-body-s-leibniz-p ()
  (forall (index)
    (implies
     (natp index)
     (equal
      (logipedia-permutation-sym-eq-invert-body-s-successor-function
       index)
      (logipedia-permutation-sym-eq-invert-body-s-invert-permut-body
       (+ 1 index))))))

(defun logipedia-permutation-sym-eq-invert-permut-body-s-statement ()
  (implies
   (logipedia-permutation-sym-eq-invert-body-s-typed-p)
   (logipedia-permutation-sym-eq-invert-permut-body-s-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
