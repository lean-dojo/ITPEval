;; Statement-only formalization of Logipedia corpus artifact
;; permutation.eq_to_bijn, catalog title "permutation.eq_to_bijn": two
;; natural-valued functions that agree at every index through n preserve
;; bounded preimage-surjectivity through n. This file contains no proof.

(in-package "ACL2")

;; Function tokens reify arbitrary source functions Nat -> Nat. The wrapper
;; enforces the source codomain without restricting either function to a
;; finite table.
(defstub logipedia-permutation-eq-to-bijn-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-eq-to-bijn-function-at
    (function natural)
  (nfix
   (logipedia-permutation-eq-to-bijn-raw-function-at
    function natural)))

(defun-sk logipedia-permutation-eq-to-bijn-agree-through-p
    (f g n)
  (forall (index)
    (implies
     (and
      (natp index)
      (<= index n))
     (equal
      (logipedia-permutation-eq-to-bijn-function-at
       f index)
      (logipedia-permutation-eq-to-bijn-function-at
       g index)))))

(defun-sk logipedia-permutation-eq-to-bijn-preimage-p
    (function n value)
  (exists (preimage)
    (and
     (natp preimage)
     (<= preimage n)
     (equal
      (logipedia-permutation-eq-to-bijn-function-at
       function preimage)
      value))))

(defun-sk logipedia-permutation-eq-to-bijn-bijn-p
    (function n)
  (forall (value)
    (implies
     (and
      (natp value)
      (<= value n))
     (logipedia-permutation-eq-to-bijn-preimage-p
      function n value))))

(defun-sk logipedia-permutation-eq-to-bijn-statement ()
  (forall (f g n)
    (implies
     (natp n)
     (implies
      (logipedia-permutation-eq-to-bijn-agree-through-p
       f g n)
      (implies
       (logipedia-permutation-eq-to-bijn-bijn-p f n)
       (logipedia-permutation-eq-to-bijn-bijn-p g n))))))

(value-triple :itpeval-statement-checked)
:q
