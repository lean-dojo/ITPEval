;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sameF_upto_le, catalog title "bigops.sameF_upto_le": agreement of
;; two arbitrary natural-indexed functions below m is inherited by every
;; natural prefix n <= m. This file contains no proof.

(in-package "ACL2")

;; Conservative interfaces represent an arbitrary carrier and arbitrary
;; natural-indexed functions. All typing laws remain explicit hypotheses.

(defstub logipedia-bigops-samef-upto-le-member-p (a-type value) t)
(defstub logipedia-bigops-samef-upto-le-function-at
  (function index)
  t)

(defun-sk logipedia-bigops-samef-upto-le-nat-function-p
    (a-type function)
  (forall (index)
    (implies
     (natp index)
     (logipedia-bigops-samef-upto-le-member-p
      a-type
      (logipedia-bigops-samef-upto-le-function-at
       function index)))))

;; This is the source sameF_upto definition: below bound, both functions
;; receive equal values at every natural index.

(defun-sk logipedia-bigops-samef-upto-le-samef-upto
    (bound function-f function-g)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index bound))
     (equal
      (logipedia-bigops-samef-upto-le-function-at
       function-f index)
      (logipedia-bigops-samef-upto-le-function-at
       function-g index)))))

(defun-sk logipedia-bigops-samef-upto-le-statement ()
  (forall (a-type function-f function-g n m)
    (implies
     (and
      (natp n)
      (natp m)
      (logipedia-bigops-samef-upto-le-nat-function-p
       a-type function-f)
      (logipedia-bigops-samef-upto-le-nat-function-p
       a-type function-g))
     (implies
      (<= n m)
      (implies
       (logipedia-bigops-samef-upto-le-samef-upto
        m function-f function-g)
       (logipedia-bigops-samef-upto-le-samef-upto
        n function-f function-g))))))

(value-triple :itpeval-statement-checked)
:q
