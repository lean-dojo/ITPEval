;; Statement-only formalization of Logipedia corpus artifact
;; permutation.invert_permut_f, catalog title "permutation.invert_permut_f":
;; a bounded injective natural-number function is recovered by its recursively
;; defined permutation inverse at every index in the bound. This file contains no proof.

(in-package "ACL2")

(defstub logipedia-permutation-invert-permut-f-function (index) t)

(defun-sk logipedia-permutation-invert-permut-f-natural-function-p ()
  (forall (index)
    (implies
     (natp index)
     (natp
      (logipedia-permutation-invert-permut-f-function index)))))

(defun-sk logipedia-permutation-invert-permut-f-injective-through-p (n)
  (forall (i j)
    (implies
     (and
      (natp i)
      (natp j)
      (<= i n)
      (<= j n)
      (equal
       (logipedia-permutation-invert-permut-f-function i)
       (logipedia-permutation-invert-permut-f-function j)))
     (equal i j))))

(defun logipedia-permutation-invert-permut-f-inverse (n value)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (if
     (equal
      value
      (logipedia-permutation-invert-permut-f-function n))
     n
     (logipedia-permutation-invert-permut-f-inverse
      (- n 1) value))))

(defun logipedia-permutation-invert-permut-f-statement (n m)
  (implies
   (and
    (natp n)
    (natp m)
    (logipedia-permutation-invert-permut-f-natural-function-p)
    (<= m n)
    (logipedia-permutation-invert-permut-f-injective-through-p n))
   (equal
    (logipedia-permutation-invert-permut-f-inverse
     n
     (logipedia-permutation-invert-permut-f-function m))
    m)))

(value-triple :itpeval-statement-checked)

:q
