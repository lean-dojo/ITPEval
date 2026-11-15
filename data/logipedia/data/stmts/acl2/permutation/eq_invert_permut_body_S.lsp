;; Statement-only formalization of Logipedia corpus artifact
;; permutation.eq_invert_permut_body_S, catalog title
;; "permutation.eq_invert_permut_body_S": at every successor index, the
;; permutation-inversion body is Leibniz-equal to the natural function that
;; returns the successor when m equals f at that successor, and otherwise
;; uses the preceding inversion. This file contains no proof.

(in-package "ACL2")

;; Natural functions and the higher-order values that consume them are
;; reified by unrestricted ACL2 objects with total natural-valued application.

(defstub logipedia-permutation-eq-invert-body-s-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-eq-invert-body-s-function-at
    (function natural)
  (nfix
   (logipedia-permutation-eq-invert-body-s-raw-function-at
    function natural)))

(defstub logipedia-permutation-eq-invert-body-s-raw-invert-at
  (index function natural)
  t)

(defun logipedia-permutation-eq-invert-body-s-invert-at
    (index function natural)
  (nfix
   (logipedia-permutation-eq-invert-body-s-raw-invert-at
    index function natural)))

(defstub logipedia-permutation-eq-invert-body-s-invert-permut-body
  (index)
  t)

(defstub logipedia-permutation-eq-invert-body-s-generic-apply
  (function-value function natural)
  t)

(defun logipedia-permutation-eq-invert-body-s-successor-function
    (index)
  (list
   'logipedia-permutation-eq-invert-body-s-successor-function
   (nfix index)))

(defun logipedia-permutation-eq-invert-body-s-apply
    (function-value function natural)
  (if
      (and
       (true-listp function-value)
       (equal (len function-value) 2)
       (equal
        (car function-value)
        'logipedia-permutation-eq-invert-body-s-successor-function)
       (natp (cadr function-value)))
      (if
       (equal
        (nfix natural)
        (logipedia-permutation-eq-invert-body-s-function-at
         function (+ 1 (cadr function-value))))
       (+ 1 (cadr function-value))
       (logipedia-permutation-eq-invert-body-s-invert-at
        (cadr function-value) function natural))
    (logipedia-permutation-eq-invert-body-s-generic-apply
     function-value function natural)))

(defun-sk logipedia-permutation-eq-invert-body-s-function-value-p
    (function-value)
  (forall (function natural)
    (implies
     (natp natural)
     (natp
      (logipedia-permutation-eq-invert-body-s-apply
       function-value function natural)))))

(defun-sk logipedia-permutation-eq-invert-body-s-typed-p ()
  (forall (index)
    (implies
     (natp index)
     (logipedia-permutation-eq-invert-body-s-function-value-p
      (logipedia-permutation-eq-invert-body-s-invert-permut-body
       index)))))

;; Identity of the reified higher-order values is exactly source Leibniz
;; equality: identity transports every predicate, and the converse follows
;; by choosing the predicate that tests identity with the left value.

(defun-sk logipedia-permutation-eq-invert-permut-body-s-leibniz-p ()
  (forall (index)
    (implies
     (natp index)
     (equal
      (logipedia-permutation-eq-invert-body-s-invert-permut-body
       (+ 1 index))
      (logipedia-permutation-eq-invert-body-s-successor-function
       index)))))

(defun logipedia-permutation-eq-invert-permut-body-s-statement ()
  (implies
   (logipedia-permutation-eq-invert-body-s-typed-p)
   (logipedia-permutation-eq-invert-permut-body-s-leibniz-p)))

(value-triple :itpeval-statement-checked)
:q
