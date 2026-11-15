;; Statement-only formalization of Logipedia corpus artifact
;; bigops.transitive_sub, catalog title "bigops.transitive_sub": selected-index
;; sub_hk correspondences between natural bounds compose transitively. This
;; file contains no proof.

(in-package "ACL2")

;; Conservative application interfaces represent the source's arbitrary total
;; functions nat -> nat and nat -> bool without restricting either domain to a
;; finite table.

(defstub logipedia-bigops-transitive-sub-nat-at (function index) t)
(defstub logipedia-bigops-transitive-sub-bool-at (function index) t)

(defun-sk logipedia-bigops-transitive-sub-nat-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (natp
      (logipedia-bigops-transitive-sub-nat-at function index)))))

(defun-sk logipedia-bigops-transitive-sub-bool-function-p (function)
  (forall (index)
    (implies
     (natp index)
     (booleanp
      (logipedia-bigops-transitive-sub-bool-at function index)))))

;; This is the source definition sub_hk h k n1 n2 p1 p2 f1 f2. The final two
;; function parameters are retained even though the definition does not
;; inspect them.

(defun-sk logipedia-bigops-transitive-sub-sub-hk-p
    (h k n1 n2 p1 p2 f1 f2)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n1)
      (equal
       (logipedia-bigops-transitive-sub-bool-at p1 index)
       t))
     (let ((image
            (logipedia-bigops-transitive-sub-nat-at h index)))
       (and
        (< image n2)
        (equal
         (logipedia-bigops-transitive-sub-bool-at p2 image)
         t)
        (equal
         (logipedia-bigops-transitive-sub-nat-at k image)
         index))))))

;; This is sub_hk (h2 o h1) (k1 o k2) n1 n3 p1 p3 f1 f3 with both
;; compositions unfolded at each universally quantified natural index.

(defun-sk logipedia-bigops-transitive-sub-composed-sub-hk-p
    (h1 k1 h2 k2 n1 n3 p1 p3 f1 f3)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n1)
      (equal
       (logipedia-bigops-transitive-sub-bool-at p1 index)
       t))
     (let* ((first-image
             (logipedia-bigops-transitive-sub-nat-at h1 index))
            (second-image
             (logipedia-bigops-transitive-sub-nat-at h2 first-image)))
       (and
        (< second-image n3)
        (equal
         (logipedia-bigops-transitive-sub-bool-at p3 second-image)
         t)
        (equal
         (logipedia-bigops-transitive-sub-nat-at
          k1
          (logipedia-bigops-transitive-sub-nat-at
           k2 second-image))
         index))))))

(defun-sk logipedia-bigops-transitive-sub-statement ()
  (forall (h1 k1 h2 k2 n1 n2 n3 p1 p2 p3 f1 f2 f3)
    (implies
     (and
      (logipedia-bigops-transitive-sub-nat-function-p h1)
      (logipedia-bigops-transitive-sub-nat-function-p k1)
      (logipedia-bigops-transitive-sub-nat-function-p h2)
      (logipedia-bigops-transitive-sub-nat-function-p k2)
      (natp n1)
      (natp n2)
      (natp n3)
      (logipedia-bigops-transitive-sub-bool-function-p p1)
      (logipedia-bigops-transitive-sub-bool-function-p p2)
      (logipedia-bigops-transitive-sub-bool-function-p p3)
      (logipedia-bigops-transitive-sub-nat-function-p f1)
      (logipedia-bigops-transitive-sub-nat-function-p f2)
      (logipedia-bigops-transitive-sub-nat-function-p f3))
     (implies
      (logipedia-bigops-transitive-sub-sub-hk-p
       h1 k1 n1 n2 p1 p2 f1 f2)
      (implies
       (logipedia-bigops-transitive-sub-sub-hk-p
        h2 k2 n2 n3 p2 p3 f2 f3)
       (logipedia-bigops-transitive-sub-composed-sub-hk-p
        h1 k1 h2 k2 n1 n3 p1 p3 f1 f3))))))

(value-triple :itpeval-statement-checked)
:q
