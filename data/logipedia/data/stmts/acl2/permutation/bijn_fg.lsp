;; Statement-only formalization of Logipedia corpus artifact
;; permutation.bijn_fg, catalog title "permutation.bijn_fg": composing two
;; natural functions that are surjective onto the naturals at most n using
;; preimages at most n preserves that surjectivity. This file contains no proof.

(in-package "ACL2")

;; Function tokens reify arbitrary source functions Nat -> Nat. The wrapper
;; enforces the source codomain without restricting the underlying token.
(defstub logipedia-permutation-bijn-fg-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-bijn-fg-function-at
    (function natural)
  (nfix
   (logipedia-permutation-bijn-fg-raw-function-at
    function natural)))

(defun-sk logipedia-permutation-bijn-fg-preimage-p
    (function n value)
  (exists (preimage)
    (and
     (natp preimage)
     (<= preimage n)
     (equal
      (logipedia-permutation-bijn-fg-function-at
       function preimage)
      value))))

(defun-sk logipedia-permutation-bijn-fg-bijn-p
    (function n)
  (forall (value)
    (implies
     (and
      (natp value)
      (<= value n))
     (logipedia-permutation-bijn-fg-preimage-p
      function n value))))

(defun-sk logipedia-permutation-bijn-fg-composed-preimage-p
    (f g n value)
  (exists (preimage)
    (and
     (natp preimage)
     (<= preimage n)
     (equal
      (logipedia-permutation-bijn-fg-function-at
       f
       (logipedia-permutation-bijn-fg-function-at
        g preimage))
      value))))

(defun-sk logipedia-permutation-bijn-fg-composed-bijn-p
    (f g n)
  (forall (value)
    (implies
     (and
      (natp value)
      (<= value n))
     (logipedia-permutation-bijn-fg-composed-preimage-p
      f g n value))))

(defun-sk logipedia-permutation-bijn-fg-statement ()
  (forall (f g n)
    (implies
     (natp n)
     (implies
      (logipedia-permutation-bijn-fg-bijn-p f n)
      (implies
       (logipedia-permutation-bijn-fg-bijn-p g n)
       (logipedia-permutation-bijn-fg-composed-bijn-p
        f g n))))))

(value-triple :itpeval-statement-checked)
:q
