;; Statement-only formalization of Logipedia corpus artifact
;; bigops.same_bigop, catalog title "bigops.same_bigop": two Boolean-selected
;; polymorphic big operations below the same natural bound are equal when
;; their selectors agree there and their selected values agree there.
;; This file contains no proof.

(in-package "ACL2")

;; At bound k, the source proposition observes p1, p2, f, and g only below k.
;; Their exact length-k prefixes therefore preserve every observation. In the
;; other direction, each prefix extends to a total natural-indexed function by
;; using nil, respectively nil-value, from k onward.
;;
;; Each fold makes finitely many calls to op. Restricting a source operation to
;; those argument pairs gives an alist with the same two fold results.
;; Conversely, the evaluator below is a total binary operation, using
;; nil-value away from recorded pairs. Carrier values are equality-preserving
;; ACL2 codes: a source instance restricts to finitely many values that can be
;; injected into the ACL2 universe, while every ACL2 trace is a source instance
;; over that universe. Thus the trace statement and source statement imply one
;; another without bounding k or the source carrier.

(defun logipedia-bigops-same-bigop-bool-list-p (values)
  (if (endp values)
      (equal values nil)
    (and
     (booleanp (car values))
     (logipedia-bigops-same-bigop-bool-list-p (cdr values)))))

;; These are the restrictions of source sameF_upto and sameF_p to [0,k).

(defun logipedia-bigops-same-bigop-samef-upto
    (predicate-prefix-1 predicate-prefix-2)
  (if (endp predicate-prefix-1)
      (equal predicate-prefix-2 nil)
    (and
     (consp predicate-prefix-2)
     (equal (car predicate-prefix-1)
            (car predicate-prefix-2))
     (logipedia-bigops-same-bigop-samef-upto
      (cdr predicate-prefix-1)
      (cdr predicate-prefix-2)))))

(defun logipedia-bigops-same-bigop-samef-p
    (predicate-prefix sequence-prefix-f sequence-prefix-g)
  (if (endp predicate-prefix)
      t
    (and
     (consp sequence-prefix-f)
     (consp sequence-prefix-g)
     (implies
      (equal (car predicate-prefix) t)
      (equal (car sequence-prefix-f)
             (car sequence-prefix-g)))
     (logipedia-bigops-same-bigop-samef-p
      (cdr predicate-prefix)
      (cdr sequence-prefix-f)
      (cdr sequence-prefix-g)))))

(defun logipedia-bigops-same-bigop-operation-at
    (operation-table nil-value left right)
  (let ((entry (assoc-equal (list left right) operation-table)))
    (if entry
        (cdr entry)
      nil-value)))

;; This recursion is definitionally the source bigop: zero returns the neutral
;; value, and a successor bound conditionally prepends the preceding value.

(defun logipedia-bigops-same-bigop-bigop
    (count predicate-prefix nil-value operation-table sequence-prefix)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil-value
    (let* ((index (- count 1))
           (rest
            (logipedia-bigops-same-bigop-bigop
             index
             predicate-prefix
             nil-value
             operation-table
             sequence-prefix)))
      (if (nth index predicate-prefix)
       (logipedia-bigops-same-bigop-operation-at
        operation-table
        nil-value
        (nth index sequence-prefix)
        rest)
       rest))))

(defun-sk logipedia-bigops-same-bigop-statement ()
  (forall
   (k predicate-prefix-1 predicate-prefix-2
      nil-value operation-table sequence-prefix-f sequence-prefix-g)
   (implies
    (and
     (natp k)
     (logipedia-bigops-same-bigop-bool-list-p predicate-prefix-1)
     (logipedia-bigops-same-bigop-bool-list-p predicate-prefix-2)
     (true-listp sequence-prefix-f)
     (true-listp sequence-prefix-g)
     (alistp operation-table)
     (equal (len predicate-prefix-1) k)
     (equal (len predicate-prefix-2) k)
     (equal (len sequence-prefix-f) k)
     (equal (len sequence-prefix-g) k))
    (implies
     (logipedia-bigops-same-bigop-samef-upto
      predicate-prefix-1 predicate-prefix-2)
     (implies
      (logipedia-bigops-same-bigop-samef-p
       predicate-prefix-1 sequence-prefix-f sequence-prefix-g)
      (equal
       (logipedia-bigops-same-bigop-bigop
        k
        predicate-prefix-1
        nil-value
        operation-table
        sequence-prefix-f)
       (logipedia-bigops-same-bigop-bigop
        k
        predicate-prefix-2
        nil-value
        operation-table
        sequence-prefix-g)))))))

(value-triple :itpeval-statement-checked)
:q
