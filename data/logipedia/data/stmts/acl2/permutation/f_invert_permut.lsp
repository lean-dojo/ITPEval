;; Statement-only formalization of Logipedia corpus artifact
;; permutation.f_invert_permut, catalog title "permutation.f_invert_permut":
;; a bounded permutation of the naturals is a left inverse of its recursive
;; permutation inversion through the given bound. This file contains no proof.

(in-package "ACL2")

;; Function tokens reify arbitrary source functions Nat -> Nat. The wrapper
;; preserves the natural codomain without replacing a function by a finite
;; table.
(defstub logipedia-permutation-f-invert-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-f-invert-function-at
    (function natural)
  (nfix
   (logipedia-permutation-f-invert-raw-function-at
    function natural)))

;; These two predicates are the source definitions of bounded range and
;; injectivity on the natural interval from zero through n.
(defun-sk logipedia-permutation-f-invert-bounded-range-p
    (function n)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= index n))
     (<=
      (logipedia-permutation-f-invert-function-at
       function index)
      n))))

(defun-sk logipedia-permutation-f-invert-injective-p
    (function n)
  (forall (left right)
    (implies
     (and
      (natp left)
      (<= left n)
      (natp right)
      (<= right n)
      (equal
       (logipedia-permutation-f-invert-function-at
        function left)
       (logipedia-permutation-f-invert-function-at
        function right)))
     (equal left right))))

(defun logipedia-permutation-f-invert-permut-p
    (function n)
  (and
   (logipedia-permutation-f-invert-bounded-range-p
    function n)
   (logipedia-permutation-f-invert-injective-p
    function n)))

;; This is the source recursion: at zero return zero; at a positive n return
;; n when f(n) is the requested value, and otherwise continue below n.
(defun logipedia-permutation-f-invert-invert-permut
    (n function value)
  (if (zp n)
      0
    (if
        (equal
         value
         (logipedia-permutation-f-invert-function-at
          function n))
        n
      (logipedia-permutation-f-invert-invert-permut
       (- n 1) function value))))

(defun-sk logipedia-permutation-f-invert-permut-statement-p ()
  (forall (function n m)
    (implies
     (and
      (natp n)
      (natp m)
      (<= m n)
      (logipedia-permutation-f-invert-permut-p
       function n))
     (equal
      (logipedia-permutation-f-invert-function-at
       function
       (logipedia-permutation-f-invert-invert-permut
        n function m))
      m))))

(value-triple :itpeval-statement-checked)
:q
