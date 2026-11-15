;; Statement-only formalization of Logipedia corpus artifact
;; permutation.injective_invert_permut, catalog title
;; "permutation.injective_invert_permut": a natural-valued function that maps
;; the natural interval from zero through n into itself injectively has an
;; injective inverse on that interval. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-permutation-injective-invert-permut-f (index) t)

(defun-sk
  logipedia-permutation-injective-invert-permut-natural-function-p ()
  (forall (index)
    (implies
      (natp index)
      (natp
        (logipedia-permutation-injective-invert-permut-f index)))))

(defun-sk
  logipedia-permutation-injective-invert-permut-maps-interval-p (n)
  (forall (index)
    (implies
      (and (natp index)
           (<= index n))
      (and
        (natp
          (logipedia-permutation-injective-invert-permut-f index))
        (<= (logipedia-permutation-injective-invert-permut-f index)
            n)))))

(defun-sk
  logipedia-permutation-injective-invert-permut-injective-p (n)
  (forall (left right)
    (implies
      (and (natp left)
           (natp right)
           (<= left n)
           (<= right n)
           (equal
             (logipedia-permutation-injective-invert-permut-f left)
             (logipedia-permutation-injective-invert-permut-f right)))
      (equal left right))))

(defun logipedia-permutation-injective-invert-permut-permut-p (n)
  (and
    (logipedia-permutation-injective-invert-permut-maps-interval-p n)
    (logipedia-permutation-injective-invert-permut-injective-p n)))

(defun logipedia-permutation-injective-invert-permut-inverse (n value)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (if (equal
          value
          (logipedia-permutation-injective-invert-permut-f n))
        n
      (logipedia-permutation-injective-invert-permut-inverse
        (- n 1)
        value))))

(defun-sk
  logipedia-permutation-injective-invert-permut-inverse-injective-p (n)
  (forall (left right)
    (implies
      (and (natp left)
           (natp right)
           (<= left n)
           (<= right n)
           (equal
             (logipedia-permutation-injective-invert-permut-inverse
               n left)
             (logipedia-permutation-injective-invert-permut-inverse
               n right)))
      (equal left right))))

(defun logipedia-permutation-injective-invert-permut-statement (n)
  (implies
    (and
      (logipedia-permutation-injective-invert-permut-natural-function-p)
      (natp n)
      (logipedia-permutation-injective-invert-permut-permut-p n))
    (logipedia-permutation-injective-invert-permut-inverse-injective-p
      n)))

(value-triple :itpeval-statement-checked)

:q
