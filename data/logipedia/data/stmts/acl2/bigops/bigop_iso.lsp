;; Statement-only formalization of Logipedia corpus artifact
;; bigops.bigop_iso, catalog title "bigops.bigop_iso": isomorphic
;; Boolean-selected families of natural numbers have equal finite products.
;; This file contains no proof.

(in-package "ACL2")

;; The source proposition observes p1 and f1 only below n1, and p2 and f2
;; only below n2. Exact typed prefixes record precisely those observations:
;; each source function restricts to such a prefix, and each prefix extends
;; to a total function by using nil or 0 outside it.

(defun logipedia-bigops-bigop-iso-bool-list-p (values)
  (if (endp values)
      (equal values nil)
    (and (booleanp (car values))
         (logipedia-bigops-bigop-iso-bool-list-p (cdr values)))))

(defun logipedia-bigops-bigop-iso-nat-list-p (values)
  (if (endp values)
      (equal values nil)
    (and (natp (car values))
         (logipedia-bigops-bigop-iso-nat-list-p (cdr values)))))

;; This combines the source value-agreement clause with sub_hk in the
;; n1-to-n2 direction. Every selected source index maps to a selected target
;; index, its value is preserved, and the reverse prefix maps it back.

(defun logipedia-bigops-bigop-iso-forward-p
    (count n2 p1 p2 f1 f2 h k)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let* ((index (- count 1))
           (image (nth index h)))
      (and
       (logipedia-bigops-bigop-iso-forward-p
        index n2 p1 p2 f1 f2 h k)
       (or
        (not (equal (nth index p1) t))
        (and
         (< image n2)
         (equal (nth image p2) t)
         (equal (nth index f1) (nth image f2))
         (equal (nth image k) index)))))))

;; This is the reverse sub_hk clause. It does not impose another value
;; equation, matching the asymmetric value-agreement clause in source iso.

(defun logipedia-bigops-bigop-iso-reverse-p
    (count n1 p2 p1 k h)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let* ((index (- count 1))
           (image (nth index k)))
      (and
       (logipedia-bigops-bigop-iso-reverse-p
        index n1 p2 p1 k h)
       (or
        (not (equal (nth index p2) t))
        (and
         (< image n1)
         (equal (nth image p1) t)
         (equal (nth image h) index)))))))

;; The source existentially quantifies total natural-valued h and k. Since h
;; is observed only below n1 and k only below n2, exact natural prefixes of
;; those lengths are bidirectionally equivalent witnesses and keep them
;; internal to the definition of iso.

(defun-sk logipedia-bigops-bigop-iso-isomorphic-p
    (n1 n2 p1 p2 f1 f2)
  (exists (h k)
    (and
     (logipedia-bigops-bigop-iso-nat-list-p h)
     (logipedia-bigops-bigop-iso-nat-list-p k)
     (equal (len h) n1)
     (equal (len k) n2)
     (logipedia-bigops-bigop-iso-forward-p
      n1 n2 p1 p2 f1 f2 h k)
     (logipedia-bigops-bigop-iso-reverse-p
      n2 n1 p2 p1 k h))))

;; The source bigop is specialized to natural multiplication with neutral
;; element 1. A bound count covers exactly the indices below count.

(defun logipedia-bigops-bigop-iso-filtered-product
    (count predicate-prefix function-prefix)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (let* ((index (- count 1))
           (rest
            (logipedia-bigops-bigop-iso-filtered-product
             index predicate-prefix function-prefix)))
      (if (equal (nth index predicate-prefix) t)
          (* (nth index function-prefix) rest)
        rest))))

(defun-sk logipedia-bigops-bigop-iso-statement ()
  (forall (n1 n2 p1 p2 f1 f2)
    (implies
     (and
      (natp n1)
      (natp n2)
      (logipedia-bigops-bigop-iso-bool-list-p p1)
      (logipedia-bigops-bigop-iso-bool-list-p p2)
      (logipedia-bigops-bigop-iso-nat-list-p f1)
      (logipedia-bigops-bigop-iso-nat-list-p f2)
      (equal (len p1) n1)
      (equal (len f1) n1)
      (equal (len p2) n2)
      (equal (len f2) n2)
      (logipedia-bigops-bigop-iso-isomorphic-p
       n1 n2 p1 p2 f1 f2))
     (equal
      (logipedia-bigops-bigop-iso-filtered-product n1 p1 f1)
      (logipedia-bigops-bigop-iso-filtered-product n2 p2 f2)))))

(value-triple :itpeval-statement-checked)
:q
