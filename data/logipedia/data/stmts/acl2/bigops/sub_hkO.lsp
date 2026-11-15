;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sub_hkO, catalog title "bigops.sub_hkO": when the source bound is
;; zero, the selected-index sub_hk correspondence condition holds for arbitrary
;; natural-valued functions and Boolean selectors. This file contains no proof.

(in-package "ACL2")

;; Conservative application interfaces represent the source's arbitrary total
;; functions nat -> nat and nat -> bool without restricting them to finite
;; tables or fixed examples.

(defstub logipedia-bigops-sub-hko-nat-at (function index) t)
(defstub logipedia-bigops-sub-hko-bool-at (function index) t)

(defun-sk logipedia-bigops-sub-hko-nat-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (natp (logipedia-bigops-sub-hko-nat-at function index)))))

(defun-sk logipedia-bigops-sub-hko-bool-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (booleanp (logipedia-bigops-sub-hko-bool-at function index)))))

;; This is the source definition sub_hk h k n1 n2 p1 p2 f1 f2. The final two
;; function parameters are retained even though the definition does not inspect
;; them.

(defun-sk logipedia-bigops-sub-hko-sub-hk-p
    (h k n1 n2 p1 p2 f1 f2)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n1)
      (equal (logipedia-bigops-sub-hko-bool-at p1 index) t))
     (let ((image (logipedia-bigops-sub-hko-nat-at h index)))
       (and
        (< image n2)
        (equal (logipedia-bigops-sub-hko-bool-at p2 image) t)
        (equal
         (logipedia-bigops-sub-hko-nat-at k image)
         index))))))

(defun-sk logipedia-bigops-sub-hko-statement ()
  (forall (h k n1 n2 p1 p2 f1 f2)
    (implies
     (and
      (logipedia-bigops-sub-hko-nat-function-p h)
      (logipedia-bigops-sub-hko-nat-function-p k)
      (natp n1)
      (natp n2)
      (logipedia-bigops-sub-hko-bool-function-p p1)
      (logipedia-bigops-sub-hko-bool-function-p p2)
      (logipedia-bigops-sub-hko-nat-function-p f1)
      (logipedia-bigops-sub-hko-nat-function-p f2))
     (implies
      (equal n1 0)
      (logipedia-bigops-sub-hko-sub-hk-p
       h k n1 n2 p1 p2 f1 f2)))))

(value-triple :itpeval-statement-checked)
:q
