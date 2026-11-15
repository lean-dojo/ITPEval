;; Statement-only formalization of Logipedia corpus artifact bigops.sub_lt,
;; catalog title "bigops.sub_lt": identity maps give a selected-index sub_hk
;; correspondence from a natural bound to any larger bound. This file contains
;; no proof.

(in-package "ACL2")

;; Conservative application interfaces represent the source's arbitrary total
;; functions nat -> nat and nat -> bool without restricting either domain to a
;; finite table.

(defstub logipedia-bigops-sub-lt-nat-at (function index) t)
(defstub logipedia-bigops-sub-lt-bool-at (function index) t)

(defun-sk logipedia-bigops-sub-lt-nat-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (natp (logipedia-bigops-sub-lt-nat-at function index)))))

(defun-sk logipedia-bigops-sub-lt-bool-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (booleanp (logipedia-bigops-sub-lt-bool-at function index)))))

;; This is sub_hk id id n m p p e e with the two identity applications
;; unfolded. The source definition retains e in its signature but does not
;; inspect it.

(defun-sk logipedia-bigops-sub-lt-identity-sub-hk-p
    (n m predicate sequence)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n)
      (equal
       (logipedia-bigops-sub-lt-bool-at predicate index)
       t))
     (and
      (< index m)
      (equal
       (logipedia-bigops-sub-lt-bool-at predicate index)
       t)
      (equal index index)))))

(defun-sk logipedia-bigops-sub-lt-statement ()
  (forall (sequence predicate n m)
    (implies
     (and
      (logipedia-bigops-sub-lt-nat-function-p sequence)
      (logipedia-bigops-sub-lt-bool-function-p predicate)
      (natp n)
      (natp m))
     (implies
      (<= n m)
      (logipedia-bigops-sub-lt-identity-sub-hk-p
       n m predicate sequence)))))

(value-triple :itpeval-statement-checked)
:q
