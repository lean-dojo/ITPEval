;; Statement-only formalization of Logipedia corpus artifact
;; permutation.bijn_n_Sn, catalog title "permutation.bijn_n_Sn": a natural
;; function that has bounded preimages through n and fixes n + 1 has bounded
;; preimages through n + 1. This file contains no proof.

(in-package "ACL2")

;; Function tokens reify arbitrary source functions Nat -> Nat. The wrapper
;; enforces the source codomain without restricting the underlying token.
(defstub logipedia-permutation-bijn-n-sn-raw-function-at
  (function natural)
  t)

(defun logipedia-permutation-bijn-n-sn-function-at
    (function natural)
  (nfix
   (logipedia-permutation-bijn-n-sn-raw-function-at
    function natural)))

(defun-sk logipedia-permutation-bijn-n-sn-preimage-p
    (function n value)
  (exists (preimage)
    (and
     (natp preimage)
     (<= preimage n)
     (equal
      (logipedia-permutation-bijn-n-sn-function-at
       function preimage)
      value))))

(defun-sk logipedia-permutation-bijn-n-sn-bijn-p
    (function n)
  (forall (value)
    (implies
     (and
      (natp value)
      (<= value n))
     (logipedia-permutation-bijn-n-sn-preimage-p
      function n value))))

(defun-sk logipedia-permutation-bijn-n-sn-statement ()
  (forall (function n)
    (implies
     (natp n)
     (implies
      (logipedia-permutation-bijn-n-sn-bijn-p function n)
      (implies
       (equal
        (logipedia-permutation-bijn-n-sn-function-at
         function (+ n 1))
        (+ n 1))
       (logipedia-permutation-bijn-n-sn-bijn-p
        function (+ n 1)))))))

(value-triple :itpeval-statement-checked)
:q
