;; Statement-only formalization of Logipedia corpus artifact
;; bigops.bigop_diff, catalog title "bigops.bigop_diff": a Boolean-selected
;; product of natural values below a bound factors out any selected index,
;; leaving the selected product with that index excluded. This file contains
;; no proof.

(in-package "ACL2")

;; The source proposition observes p and f only at indices below n.  A typed
;; prefix of length n records exactly those observations: every pair of source
;; functions restricts to such prefixes, and every such pair extends to total
;; functions by using nil and 0 beyond the prefixes.

(defun logipedia-bigops-bigop-diff-bool-list-p (values)
  (if (endp values)
      (equal values nil)
    (and (booleanp (car values))
         (logipedia-bigops-bigop-diff-bool-list-p (cdr values)))))

(defun logipedia-bigops-bigop-diff-nat-list-p (values)
  (if (endp values)
      (equal values nil)
    (and (natp (car values))
         (logipedia-bigops-bigop-diff-nat-list-p (cdr values)))))

(defun logipedia-bigops-bigop-diff-product
    (count predicate-prefix function-prefix excluded-index exclude-index-p)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (let* ((index (- count 1))
           (rest
             (logipedia-bigops-bigop-diff-product
               index
               predicate-prefix
               function-prefix
               excluded-index
               exclude-index-p)))
      (if (and
            (nth index predicate-prefix)
            (or (not exclude-index-p)
                (not (equal excluded-index index))))
          (* (nth index function-prefix) rest)
        rest))))

(defun-sk logipedia-bigops-bigop-diff-statement ()
  (forall (predicate-prefix function-prefix i n)
    (implies
      (and (natp i)
           (natp n)
           (logipedia-bigops-bigop-diff-bool-list-p predicate-prefix)
           (logipedia-bigops-bigop-diff-nat-list-p function-prefix)
           (equal (len predicate-prefix) n)
           (equal (len function-prefix) n)
           (< i n)
           (equal (nth i predicate-prefix) t))
      (equal
        (logipedia-bigops-bigop-diff-product
          n predicate-prefix function-prefix i nil)
        (* (nth i function-prefix)
           (logipedia-bigops-bigop-diff-product
             n predicate-prefix function-prefix i t))))))

(value-triple :itpeval-statement-checked)
:q
