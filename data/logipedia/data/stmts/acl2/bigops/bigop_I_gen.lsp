;; Statement-only formalization of Logipedia corpus artifact
;; bigops.bigop_I_gen: shifting a filtered product to start at a equals
;; filtering the original prefix by the lower bound a.
;; This file contains no proof.

(in-package "ACL2")

;; The environment indexes one arbitrary Boolean predicate and one arbitrary
;; natural-valued sequence.  Only the finite prefix observed by the theorem
;; is type-checked; every such trace extends to total source functions.

(defstub logipedia-bigops-igen-predicate
  (environment index)
  t)

(defstub logipedia-bigops-igen-sequence
  (environment index)
  t)

(defun logipedia-bigops-igen-shifted-product
    (count environment offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (let* ((index (- count 1))
           (source-index (+ index offset))
           (rest
            (logipedia-bigops-igen-shifted-product
             index environment offset)))
      (if (logipedia-bigops-igen-predicate
           environment source-index)
          (*
           (logipedia-bigops-igen-sequence
            environment source-index)
           rest)
        rest))))

(defun logipedia-bigops-igen-filtered-product
    (bound environment lower-bound)
  (declare (xargs :measure (nfix bound)))
  (if (zp bound)
      1
    (let* ((index (- bound 1))
           (rest
            (logipedia-bigops-igen-filtered-product
             index environment lower-bound)))
      (if (and
           (<= lower-bound index)
           (logipedia-bigops-igen-predicate environment index))
          (*
           (logipedia-bigops-igen-sequence environment index)
           rest)
        rest))))

(defun-sk logipedia-bigops-igen-prefix-typed-p
    (environment bound)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index bound))
     (and
      (booleanp
       (logipedia-bigops-igen-predicate environment index))
      (natp
       (logipedia-bigops-igen-sequence environment index))))))

(defun-sk logipedia-bigops-bigop-i-gen-statement ()
  (forall (environment a b)
    (implies
     (and
      (natp a)
      (natp b)
      (<= a b)
      (logipedia-bigops-igen-prefix-typed-p environment b))
     (equal
      (logipedia-bigops-igen-shifted-product
       (- b a) environment a)
      (logipedia-bigops-igen-filtered-product
       b environment a)))))

(value-triple :itpeval-statement-checked)
:q
