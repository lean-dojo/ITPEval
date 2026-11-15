;; Statement-only formalization of Logipedia corpus artifact
;; bigops.sub0_to_false, catalog title "bigops.sub0_to_false": if n1 is zero
;; and sub_hk maps every p2-selected index below n2 via h to a p1-selected
;; index below n1, with k(h(i)) = i, then p2 is false below n2. This file
;; contains no proof.

(in-package "ACL2")

;; Conservative application interfaces represent the source's arbitrary total
;; functions nat -> nat and nat -> bool without enumerating their domains.

(defstub logipedia-bigops-sub0-nat-at (function index) t)
(defstub logipedia-bigops-sub0-bool-at (function index) t)

(defun-sk logipedia-bigops-sub0-nat-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (natp (logipedia-bigops-sub0-nat-at function index)))))

(defun-sk logipedia-bigops-sub0-bool-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (booleanp (logipedia-bigops-sub0-bool-at function index)))))

;; Exact definitional expansion of sub_hk h k n1 n2 p1 p2 f1 f2: every
;; p1-selected i below n1 has h(i) below n2, p2(h(i)) true, and k(h(i)) = i.
;; The final two function parameters occur in the definition's signature but
;; are not inspected by its body.

(defun-sk logipedia-bigops-sub0-sub-hk-p
    (h k n1 n2 p1 p2 f1 f2)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n1)
      (equal (logipedia-bigops-sub0-bool-at p1 index) t))
     (let ((image (logipedia-bigops-sub0-nat-at h index)))
       (and
        (< image n2)
        (equal (logipedia-bigops-sub0-bool-at p2 image) t)
        (equal
         (logipedia-bigops-sub0-nat-at k image)
         index))))))

(defun-sk logipedia-bigops-sub0-all-false-p (n2 p2)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n2))
     (equal
      (logipedia-bigops-sub0-bool-at p2 index)
      nil))))

(defun-sk logipedia-bigops-sub0-to-false-statement ()
  (forall (h k n1 n2 p1 p2 f1 f2)
    (implies
     (and
      (logipedia-bigops-sub0-nat-function-p h)
      (logipedia-bigops-sub0-nat-function-p k)
      (natp n1)
      (natp n2)
      (logipedia-bigops-sub0-bool-function-p p1)
      (logipedia-bigops-sub0-bool-function-p p2)
      (logipedia-bigops-sub0-nat-function-p f1)
      (logipedia-bigops-sub0-nat-function-p f2))
     (implies
      (equal n1 0)
      (implies
       (logipedia-bigops-sub0-sub-hk-p
        h k n2 n1 p2 p1 f2 f1)
       (logipedia-bigops-sub0-all-false-p n2 p2))))))

(value-triple :itpeval-statement-checked)
:q
