;; Statement-only formalization of Logipedia corpus artifact
;; permutation.eq_invert_permut_body_O, catalog title
;; "permutation.eq_invert_permut_body_O": the permutation-inversion body at
;; zero is Leibniz-equal at its higher-order natural-function type to the
;; function that returns zero in both branches after comparing m with f(0).
;; This file contains no proof.

(in-package "ACL2")

;; Natural functions and the higher-order values that consume them are
;; reified by unrestricted ACL2 objects with total natural-valued application.

(defstub logipedia-permutation-eq-invert-body-o-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-eq-invert-body-o-function-at
    (function natural)
  (nfix
   (logipedia-permutation-eq-invert-body-o-raw-function-at
    function natural)))

(defstub logipedia-permutation-eq-invert-body-o-invert-permut-body
  (index)
  t)

(defstub logipedia-permutation-eq-invert-body-o-generic-apply
  (function-value function natural)
  t)

(defun logipedia-permutation-eq-invert-body-o-zero-function ()
  (list 'logipedia-permutation-eq-invert-body-o-zero-function))

(defun logipedia-permutation-eq-invert-body-o-apply
    (function-value function natural)
  (if
      (equal
       function-value
       (logipedia-permutation-eq-invert-body-o-zero-function))
      (if
       (equal
        natural
        (logipedia-permutation-eq-invert-body-o-function-at
         function 0))
       0
       0)
    (logipedia-permutation-eq-invert-body-o-generic-apply
     function-value function natural)))

(defun-sk logipedia-permutation-eq-invert-body-o-function-value-p
    (function-value)
  (forall (function natural)
    (implies
     (natp natural)
     (natp
      (logipedia-permutation-eq-invert-body-o-apply
       function-value function natural)))))

(defun-sk logipedia-permutation-eq-invert-body-o-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-permutation-eq-invert-body-o-function-value-p
      (logipedia-permutation-eq-invert-body-o-invert-permut-body
       index)))))

;; Identity of the reified higher-order values is exactly source Leibniz
;; equality: identity transports every predicate, and the converse follows
;; by choosing the predicate that tests identity with the left value.

(defun logipedia-permutation-eq-invert-permut-body-o-statement ()
  (implies
   (logipedia-permutation-eq-invert-body-o-typed-p)
   (equal
    (logipedia-permutation-eq-invert-body-o-invert-permut-body 0)
    (logipedia-permutation-eq-invert-body-o-zero-function))))

(value-triple :itpeval-statement-checked)
:q
