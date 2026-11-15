;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__096, "Principle of Inclusion / Exclusion": for
;; every finite indexed family of finite sets, the cardinality of its union is
;; the alternating sum of the cardinalities of the intersections indexed by
;; its nonempty subfamilies. This file contains no proof.

(in-package "ACL2")

;; Duplicate-free true lists represent finite sets of arbitrary ACL2 objects.
;; Positions in the outer list are the family indices, so equal member sets
;; may repeat without identifying their distinct indices.
(defun ht096-finite-set-family-p (family)
  (if (consp family)
      (and (true-listp (car family))
           (no-duplicatesp-equal (car family))
           (ht096-finite-set-family-p (cdr family)))
    (equal family nil)))

(defun ht096-set-union (left right)
  (if (consp left)
      (if (member-equal (car left) right)
          (ht096-set-union (cdr left) right)
        (cons (car left)
              (ht096-set-union (cdr left) right)))
    right))

(defun ht096-family-union (family)
  (if (consp family)
      (ht096-set-union
       (car family)
       (ht096-family-union (cdr family)))
    nil))

(defun ht096-set-intersection (left right)
  (if (consp left)
      (if (member-equal (car left) right)
          (cons
           (car left)
           (ht096-set-intersection (cdr left) right))
        (ht096-set-intersection (cdr left) right))
    nil))

(defun ht096-family-intersection (family)
  (if (consp family)
      (if (consp (cdr family))
          (ht096-set-intersection
           (car family)
           (ht096-family-intersection (cdr family)))
        (car family))
    nil))

(defun ht096-prepend-to-each (value families)
  (if (consp families)
      (cons
       (cons value (car families))
       (ht096-prepend-to-each value (cdr families)))
    nil))

;; This power-set enumeration is positional. If two indices carry equal sets,
;; the corresponding equal-looking subfamilies remain separate list entries.
(defun ht096-index-subfamilies (family)
  (if (consp family)
      (let ((tail-subfamilies
             (ht096-index-subfamilies (cdr family))))
        (append
         tail-subfamilies
         (ht096-prepend-to-each
          (car family) tail-subfamilies)))
    (list nil)))

(defun ht096-inclusion-exclusion-sum (subfamilies)
  (if (consp subfamilies)
      (let ((subfamily (car subfamilies)))
        (+
         (if (consp subfamily)
             (*
              (expt -1 (+ (len subfamily) 1))
              (len (ht096-family-intersection subfamily)))
           0)
         (ht096-inclusion-exclusion-sum
          (cdr subfamilies))))
    0))

(defun hundred-theorems-096-principle-of-inclusion-exclusion-statement
    (family)
  (implies
   (ht096-finite-set-family-p family)
   (equal
    (len (ht096-family-union family))
    (ht096-inclusion-exclusion-sum
     (ht096-index-subfamilies family)))))

(value-triple :itpeval-statement-checked)
:q
