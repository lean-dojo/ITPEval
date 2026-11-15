;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q716171, "Erdős–Ginzburg–Ziv theorem": a finite
;; set of at least 2*n-1 indices carrying not-necessarily-distinct labels in
;; ZMod n has an n-element subset whose labels sum to zero. This file contains
;; no proof.

(in-package "ACL2")

;; A duplicate-free true list represents the source Finset of indices. Only
;; label values on that finite set occur in the proposition, and every finite
;; labeling is represented by a tame unary lookup function; conversely, each
;; such ACL2 labeling gives a source function after transporting the finite
;; indices. Thus APPLY$ does not restrict the source function quantifier.
;; For positive n, ZMod n is represented by its unique natural representative
;; below n; ZMod 0 is the integers. The include/exclude recursion is an exact
;; internal existential search through all subsets of the finite index set.

(defun q716171-index-set-p (indices)
  (and (true-listp indices)
       (no-duplicatesp-equal indices)))

(defun q716171-zmod-element-p (value n)
  (if (zp n)
      (integerp value)
    (and (natp value)
         (< value n))))

(defun q716171-labels-valid-p (indices labels n)
  (if (consp indices)
      (and
       (q716171-zmod-element-p
        (apply$ labels (list (car indices)))
        n)
       (q716171-labels-valid-p (cdr indices) labels n))
    (equal indices nil)))

(defun q716171-zero-in-zmod-p (integer-sum n)
  (if (zp n)
      (equal integer-sum 0)
    (equal (mod integer-sum n) 0)))

(defun q716171-subset-witness-exists-p
    (remaining labels n needed integer-sum)
  (declare (xargs :measure (len remaining)))
  (if (zp needed)
      (q716171-zero-in-zmod-p integer-sum n)
    (if (consp remaining)
        (or
         (q716171-subset-witness-exists-p
          (cdr remaining) labels n needed integer-sum)
         (q716171-subset-witness-exists-p
          (cdr remaining)
          labels
          n
          (- needed 1)
          (+ integer-sum
             (apply$ labels (list (car remaining))))))
      nil)))

(defun q716171-twice-minus-one (n)
  (if (zp n)
      0
    (- (* 2 n) 1)))

(defun thousand-theorems-q716171-erdos-ginzburg-ziv-statement
    (n indices labels)
  (implies
   (and
    (natp n)
    (q716171-index-set-p indices)
    (tamep-functionp labels)
    (q716171-labels-valid-p indices labels n)
    (<= (q716171-twice-minus-one n)
        (len indices)))
   (q716171-subset-witness-exists-p
    indices labels n n 0)))

(value-triple :itpeval-statement-checked)
:q
