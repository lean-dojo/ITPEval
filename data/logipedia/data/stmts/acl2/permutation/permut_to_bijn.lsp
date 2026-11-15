;; Statement-only formalization of Logipedia corpus artifact
;; permutation.permut_to_bijn, catalog title "permutation.permut_to_bijn":
;; every natural-number function that maps the indices from zero through n
;; into that range injectively is surjective onto the same range. This file
;; contains no proof.

(in-package "ACL2")

;; Function tokens reify arbitrary source functions Nat -> Nat. The wrapper
;; enforces the source codomain without restricting the function to a table.
(defstub logipedia-permutation-permut-to-bijn-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-permut-to-bijn-function-at
    (function natural)
  (nfix
   (logipedia-permutation-permut-to-bijn-raw-function-at
    function natural)))

(defun-sk logipedia-permutation-permut-to-bijn-range-p
    (function n)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= index n))
     (<=
      (logipedia-permutation-permut-to-bijn-function-at
       function index)
      n))))

(defun-sk logipedia-permutation-permut-to-bijn-injective-p
    (function n)
  (forall (left right)
    (implies
     (and
      (natp left)
      (natp right)
      (<= left n)
      (<= right n)
      (equal
       (logipedia-permutation-permut-to-bijn-function-at
        function left)
       (logipedia-permutation-permut-to-bijn-function-at
        function right)))
     (equal left right))))

(defun logipedia-permutation-permut-to-bijn-permut-p
    (function n)
  (and
   (logipedia-permutation-permut-to-bijn-range-p function n)
   (logipedia-permutation-permut-to-bijn-injective-p function n)))

(defun-sk logipedia-permutation-permut-to-bijn-preimage-p
    (function n value)
  (exists (preimage)
    (and
     (natp preimage)
     (<= preimage n)
     (equal
      (logipedia-permutation-permut-to-bijn-function-at
       function preimage)
      value))))

(defun-sk logipedia-permutation-permut-to-bijn-bijn-p
    (function n)
  (forall (value)
    (implies
     (and
      (natp value)
      (<= value n))
     (logipedia-permutation-permut-to-bijn-preimage-p
      function n value))))

(defun-sk logipedia-permutation-permut-to-bijn-statement ()
  (forall (n function)
    (implies
     (natp n)
     (implies
      (logipedia-permutation-permut-to-bijn-permut-p
       function n)
      (logipedia-permutation-permut-to-bijn-bijn-p
       function n)))))

(value-triple :itpeval-statement-checked)
:q
