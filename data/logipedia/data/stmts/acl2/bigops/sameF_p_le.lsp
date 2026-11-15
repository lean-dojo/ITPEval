;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sameF_p_le, catalog title "bigops.sameF_p_le": agreement of two
;; arbitrary natural-indexed functions at Boolean-selected indices below m
;; is inherited by every natural prefix n <= m. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces represent an arbitrary carrier and arbitrary
;; natural-indexed functions. All typing laws remain explicit hypotheses.

(defstub logipedia-bigops-samef-p-le-member-p (a-type value) t)
(defstub logipedia-bigops-samef-p-le-predicate-at
  (predicate index)
  t)
(defstub logipedia-bigops-samef-p-le-function-at
  (function index)
  t)

(defun-sk logipedia-bigops-samef-p-le-nat-bool-function-p (predicate)
  (forall (index)
    (implies
     (natp index)
     (booleanp
      (logipedia-bigops-samef-p-le-predicate-at
       predicate index)))))

(defun-sk logipedia-bigops-samef-p-le-nat-function-p
    (a-type function)
  (forall (index)
    (implies
     (natp index)
     (logipedia-bigops-samef-p-le-member-p
      a-type
      (logipedia-bigops-samef-p-le-function-at
       function index)))))

;; This is the source sameF_p definition: below bound, every index selected
;; by predicate must receive equal values from the two functions.

(defun-sk logipedia-bigops-samef-p-le-samef-p
    (bound predicate function-f function-g)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index bound)
      (equal
       (logipedia-bigops-samef-p-le-predicate-at
        predicate index)
       t))
     (equal
      (logipedia-bigops-samef-p-le-function-at
       function-f index)
      (logipedia-bigops-samef-p-le-function-at
       function-g index)))))

(defun-sk logipedia-bigops-samef-p-le-statement ()
  (forall (a-type predicate function-f function-g n m)
    (implies
     (and
      (natp n)
      (natp m)
      (logipedia-bigops-samef-p-le-nat-bool-function-p
       predicate)
      (logipedia-bigops-samef-p-le-nat-function-p
       a-type function-f)
      (logipedia-bigops-samef-p-le-nat-function-p
       a-type function-g))
     (implies
      (<= n m)
      (implies
       (logipedia-bigops-samef-p-le-samef-p
        m predicate function-f function-g)
       (logipedia-bigops-samef-p-le-samef-p
        n predicate function-f function-g))))))

(value-triple :itpeval-statement-checked)
:q
