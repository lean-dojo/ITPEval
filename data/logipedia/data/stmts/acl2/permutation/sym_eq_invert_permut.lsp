;; Statement-only formalization of Logipedia corpus artifact
;; permutation.sym_eq_invert_permut, catalog title
;; "permutation.sym_eq_invert_permut": for every natural index, the
;; natural-filtered inversion-body higher-order value is Leibniz-equal to the
;; permutation-inversion value. This file contains no proof.

(in-package "ACL2")

;; Natural functions, natural-indexed families, and the higher-order values
;; that consume natural functions are represented by unrestricted ACL2
;; objects with total application operations.

(defstub logipedia-permutation-sym-eq-invert-permut-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-sym-eq-invert-permut-function-at
    (function natural)
  (nfix
   (logipedia-permutation-sym-eq-invert-permut-raw-function-at
    function natural)))

(defstub logipedia-permutation-sym-eq-invert-permut-raw-higher-apply
  (value function natural)
  t)

(defun logipedia-permutation-sym-eq-invert-permut-higher-apply
    (value function natural)
  (nfix
   (logipedia-permutation-sym-eq-invert-permut-raw-higher-apply
    value function natural)))

(defstub logipedia-permutation-sym-eq-invert-permut-invert-permut-value
  (index)
  t)

(defun logipedia-permutation-sym-eq-invert-permut-body-family ()
  (list 'logipedia-permutation-sym-eq-invert-permut-body-family))

(defstub logipedia-permutation-sym-eq-invert-permut-filter-nat-type-value
  (family index)
  t)

;; Leibniz equality in the source is bidirectionally equivalent to object
;; identity: identity transports every predicate, while the converse follows
;; by instantiating the transported predicate with equality to the left value.

(defun-sk logipedia-permutation-sym-eq-invert-permut-leibniz-p ()
  (forall (index)
    (implies
     (natp index)
     (equal
      (logipedia-permutation-sym-eq-invert-permut-filter-nat-type-value
       (logipedia-permutation-sym-eq-invert-permut-body-family)
       index)
      (logipedia-permutation-sym-eq-invert-permut-invert-permut-value
       index)))))

(defun logipedia-permutation-sym-eq-invert-permut-statement ()
  (logipedia-permutation-sym-eq-invert-permut-leibniz-p))

(value-triple :itpeval-statement-checked)
:q
