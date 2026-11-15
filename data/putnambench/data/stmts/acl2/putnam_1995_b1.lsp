;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_b1:
;; any two partitions of a nine-element set have two distinct elements whose
;; containing blocks have equal sizes in both partitions. This file contains
;; no proof.

(in-package "ACL2")

;; A partition is represented by a true list of nonempty blocks. Its flattened
;; list is required to contain each element of Finset.range 9 exactly once, so
;; forgetting list order gives exactly a Finpartition of that carrier. Every
;; source partition can conversely be enumerated this way. Isabelle's carrier
;; {1,...,9} is equivalent via the cardinality-preserving shift x |-> x+1.
;; The source function Pi is uniquely fixed by Pi_def, so computing the length
;; of the unique containing block is a definitional elimination of Pi.

(defun putnam-1995-b1-domain-elements-p (elements)
  (if (consp elements)
      (and
       (natp (car elements))
       (< (car elements) 9)
       (putnam-1995-b1-domain-elements-p
        (cdr elements)))
    (equal elements nil)))

(defun putnam-1995-b1-blocks-p (partition)
  (if (consp partition)
      (and
       (true-listp (car partition))
       (consp (car partition))
       (putnam-1995-b1-domain-elements-p
        (car partition))
       (putnam-1995-b1-blocks-p
        (cdr partition)))
    (equal partition nil)))

(defun putnam-1995-b1-flatten (partition)
  (if (consp partition)
      (append
       (car partition)
       (putnam-1995-b1-flatten (cdr partition)))
    nil))

(defun putnam-1995-b1-partition-p (partition)
  (let ((elements
         (putnam-1995-b1-flatten partition)))
    (and
     (true-listp partition)
     (putnam-1995-b1-blocks-p partition)
     (no-duplicatesp-equal elements)
     (member-equal 0 elements)
     (member-equal 1 elements)
     (member-equal 2 elements)
     (member-equal 3 elements)
     (member-equal 4 elements)
     (member-equal 5 elements)
     (member-equal 6 elements)
     (member-equal 7 elements)
     (member-equal 8 elements))))

(defun putnam-1995-b1-containing-block-size
    (partition element)
  (if (consp partition)
      (if (member-equal element (car partition))
          (len (car partition))
        (putnam-1995-b1-containing-block-size
         (cdr partition) element))
    0))

(defun putnam-1995-b1-same-size-pair-p
    (left right first-partition second-partition)
  (and
   (equal
    (putnam-1995-b1-containing-block-size
     first-partition left)
    (putnam-1995-b1-containing-block-size
     first-partition right))
   (equal
    (putnam-1995-b1-containing-block-size
     second-partition left)
    (putnam-1995-b1-containing-block-size
     second-partition right))))

(defun putnam-1995-b1-collision-with-p
    (left remaining first-partition second-partition)
  (if (consp remaining)
      (or
       (putnam-1995-b1-same-size-pair-p
        left
        (car remaining)
        first-partition
        second-partition)
       (putnam-1995-b1-collision-with-p
        left
        (cdr remaining)
        first-partition
        second-partition))
    nil))

;; Searching only the tail after LEFT makes the two internally quantified
;; witnesses distinct, and the nested recursion covers every unordered pair.

(defun putnam-1995-b1-collision-exists-p
    (remaining first-partition second-partition)
  (if (consp remaining)
      (or
       (putnam-1995-b1-collision-with-p
        (car remaining)
        (cdr remaining)
        first-partition
        second-partition)
       (putnam-1995-b1-collision-exists-p
        (cdr remaining)
        first-partition
        second-partition))
    nil))

(defun putnambench-putnam-1995-b1-statement
    (first-partition second-partition)
  (implies
   (and
    (putnam-1995-b1-partition-p first-partition)
    (putnam-1995-b1-partition-p second-partition))
   (putnam-1995-b1-collision-exists-p
    '(0 1 2 3 4 5 6 7 8)
    first-partition
    second-partition)))

(value-triple :itpeval-statement-checked)
:q
