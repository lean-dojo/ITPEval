;; Statement-only formalization of Logipedia corpus artifact
;; permutation.bijn_transpose, catalog title "permutation.bijn_transpose":
;; swapping two natural indices at most n is surjective onto the naturals at
;; most n using preimages at most n. This file contains no proof.

(in-package "ACL2")

(defun logipedia-permutation-bijn-transpose
    (i j natural)
  (if (equal natural i)
      j
    (if (equal natural j)
        i
      natural)))

(defun-sk logipedia-permutation-bijn-transpose-preimage-p
    (i j n value)
  (exists (preimage)
    (and
     (natp preimage)
     (<= preimage n)
     (equal
      (logipedia-permutation-bijn-transpose
       i j preimage)
      value))))

(defun-sk logipedia-permutation-bijn-transpose-bijn-p
    (i j n)
  (forall (value)
    (implies
     (and
      (natp value)
      (<= value n))
     (logipedia-permutation-bijn-transpose-preimage-p
      i j n value))))

(defun-sk logipedia-permutation-bijn-transpose-statement ()
  (forall (n i j)
    (implies
     (and
      (natp n)
      (natp i)
      (natp j)
      (<= i n)
      (<= j n))
     (logipedia-permutation-bijn-transpose-bijn-p
      i j n))))

(value-triple :itpeval-statement-checked)
:q
