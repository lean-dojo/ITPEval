;; Statement-only formalization of Logipedia corpus artifact
;; permutation.permut_invert_permut, catalog title
;; "permutation.permut_invert_permut": the bounded inverse of a permutation
;; of the natural numbers through n is itself a permutation through n. This
;; file contains no proof.

(in-package "ACL2")

;; This unconstrained function symbol represents the source's universally
;; quantified f : nat -> nat. Its type restriction is explicit below.
(defstub logipedia-permut-invert-permut-f (x) t)

(defun-sk logipedia-permut-invert-permut-nat-function-p ()
  (forall (x)
    (implies
     (natp x)
     (natp (logipedia-permut-invert-permut-f x)))))

;; Source predicate injn: injectivity restricted to the natural interval
;; 0,...,n.
(defun-sk logipedia-permut-invert-permut-injn-p (n)
  (forall (i j)
    (implies
     (and (natp i)
          (natp j)
          (<= i n)
          (<= j n)
          (equal
           (logipedia-permut-invert-permut-f i)
           (logipedia-permut-invert-permut-f j)))
     (equal i j))))

;; Source predicate permut: f maps 0,...,n into itself and is injective there.
(defun-sk logipedia-permut-invert-permut-range-p (n)
  (forall (i)
    (implies
     (and (natp i)
          (<= i n))
     (and
      (natp (logipedia-permut-invert-permut-f i))
      (<= (logipedia-permut-invert-permut-f i) n)))))

(defun logipedia-permut-invert-permut-permut-p (n)
  (and
   (logipedia-permut-invert-permut-range-p n)
   (logipedia-permut-invert-permut-injn-p n)))

;; Source invert_permut scans indices downward: at zero it returns zero; at
;; a positive bound it returns that bound when f maps it to m, and otherwise
;; continues at the predecessor bound.
(defun logipedia-permut-invert-permut-inverse (n m)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      0
    (if (equal
         m
         (logipedia-permut-invert-permut-f n))
        n
      (logipedia-permut-invert-permut-inverse (- n 1) m))))

(defun-sk logipedia-permut-invert-permut-inverse-injn-p (n)
  (forall (i j)
    (implies
     (and (natp i)
          (natp j)
          (<= i n)
          (<= j n)
          (equal
           (logipedia-permut-invert-permut-inverse n i)
           (logipedia-permut-invert-permut-inverse n j)))
     (equal i j))))

(defun-sk logipedia-permut-invert-permut-inverse-range-p (n)
  (forall (i)
    (implies
     (and (natp i)
          (<= i n))
     (and
      (natp
       (logipedia-permut-invert-permut-inverse n i))
      (<=
       (logipedia-permut-invert-permut-inverse n i)
       n)))))

(defun logipedia-permut-invert-permut-inverse-permut-p (n)
  (and
   (logipedia-permut-invert-permut-inverse-range-p n)
   (logipedia-permut-invert-permut-inverse-injn-p n)))

(defun-sk logipedia-permutation-permut-invert-permut-statement ()
  (forall (n)
    (implies
     (and
      (natp n)
      (logipedia-permut-invert-permut-nat-function-p)
      (logipedia-permut-invert-permut-permut-p n))
     (logipedia-permut-invert-permut-inverse-permut-p n))))

(value-triple :itpeval-statement-checked)
:q
