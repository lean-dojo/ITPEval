;; Statement-only formalization of Logipedia corpus artifact
;; bigops.bigop_Strue, catalog title "bigops.bigop_Strue": when the
;; Boolean selector at a natural index is true, the successor-bounded
;; polymorphic big operation prepends that index's value.
;; This file contains no proof.

(in-package "ACL2")

;; At each bound k, the source proposition observes only the prefixes through
;; k and the finitely many operation calls made by the fold.  These finite
;; traces are complete for the proposition: total source functions restrict
;; to them, and each trace extends to total functions by the defaults below.

(defun logipedia-bigops-strue-bool-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (booleanp (car values))
     (logipedia-bigops-strue-bool-list-p (cdr values)))))

(defun logipedia-bigops-strue-operation-at
    (operation-table nil-value left right)
  (let ((entry (assoc-equal (list left right) operation-table)))
    (if entry
        (cdr entry)
      nil-value)))

(defun logipedia-bigops-strue-bigop
    (index predicate-prefix nil-value operation-table sequence-prefix)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      nil-value
    (let* ((prior-index (- index 1))
           (rest
            (logipedia-bigops-strue-bigop
             prior-index
             predicate-prefix
             nil-value
             operation-table
             sequence-prefix)))
      (if (nth prior-index predicate-prefix)
          (logipedia-bigops-strue-operation-at
           operation-table
           nil-value
           (nth prior-index sequence-prefix)
           rest)
        rest))))

(defun-sk logipedia-bigops-bigop-strue-statement ()
  (forall
   (k predicate-prefix nil-value operation-table sequence-prefix)
   (implies
    (and
     (natp k)
     (logipedia-bigops-strue-bool-list-p predicate-prefix)
     (true-listp sequence-prefix)
     (alistp operation-table)
     (< k (len predicate-prefix))
     (< k (len sequence-prefix))
     (equal (nth k predicate-prefix) t))
    (equal
     (logipedia-bigops-strue-bigop
      (+ 1 k)
      predicate-prefix
      nil-value
      operation-table
      sequence-prefix)
     (logipedia-bigops-strue-operation-at
      operation-table
      nil-value
      (nth k sequence-prefix)
      (logipedia-bigops-strue-bigop
       k
       predicate-prefix
       nil-value
       operation-table
       sequence-prefix))))))

(value-triple :itpeval-statement-checked)
:q
