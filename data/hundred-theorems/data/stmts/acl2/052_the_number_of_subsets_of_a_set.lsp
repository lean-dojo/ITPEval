;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__052, "The Number of Subsets of a Set": every finite
;; set has exactly 2 raised to its cardinality subsets, represented by a
;; duplicate-free true list of arbitrary ACL2 objects and its recursively
;; enumerated power set. This file contains no proof.

(in-package "ACL2")

(defun ht052-prepend-to-each (value sets)
  (if (atom sets)
      nil
    (cons
     (cons value (car sets))
     (ht052-prepend-to-each value (cdr sets)))))

(defun ht052-power-set (set-elements)
  (if (atom set-elements)
      (list nil)
    (let ((tail-power-set
           (ht052-power-set (cdr set-elements))))
      (append
       tail-power-set
       (ht052-prepend-to-each
        (car set-elements) tail-power-set)))))

(defun hundred-theorems-052-number-of-subsets-of-a-set-statement
    (set-elements)
  (implies
   (and (true-listp set-elements)
        (no-duplicatesp-equal set-elements))
   (equal
    (len (ht052-power-set set-elements))
    (expt 2 (len set-elements)))))

(value-triple :itpeval-statement-checked)
:q
