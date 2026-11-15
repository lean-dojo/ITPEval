;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q718875, "Erdős–Ko–Rado theorem": an intersecting
;; family of r-element subsets of Fin n, with r at most n/2, has cardinality
;; at most (n - 1) choose (r - 1). This file contains no proof.

(in-package "ACL2")

;; A Fin n element is represented by a natural below n. Duplicate-free true
;; lists represent finite subsets, and outer lists contain no two
;; extensionally equal subsets. Hence valid outer lists represent exactly
;; Finset (Finset (Fin n)), independently of list order.

(defun q718875-fin-element-p (x n)
  (and (natp x)
       (< x n)))

(defun q718875-fin-set-elements-p (set n)
  (if (consp set)
      (and (q718875-fin-element-p (car set) n)
           (q718875-fin-set-elements-p (cdr set) n))
    (equal set nil)))

(defun q718875-fin-set-p (set n)
  (and (true-listp set)
       (no-duplicatesp-equal set)
       (q718875-fin-set-elements-p set n)))

(defun q718875-subset-p (left right)
  (if (consp left)
      (and (member-equal (car left) right)
           (q718875-subset-p (cdr left) right))
    t))

(defun q718875-set-equal-p (left right)
  (and (q718875-subset-p left right)
       (q718875-subset-p right left)))

(defun q718875-set-distinct-from-family-p (set family)
  (if (consp family)
      (and (not (q718875-set-equal-p set (car family)))
           (q718875-set-distinct-from-family-p
            set (cdr family)))
    t))

(defun q718875-family-p (family n)
  (if (consp family)
      (and (q718875-fin-set-p (car family) n)
           (q718875-set-distinct-from-family-p
            (car family) (cdr family))
           (q718875-family-p (cdr family) n))
    (equal family nil)))

(defun q718875-sized-family-p (family r)
  (if (consp family)
      (and (equal (len (car family)) r)
           (q718875-sized-family-p (cdr family) r))
    t))

(defun q718875-sets-intersect-p (left right)
  (if (consp left)
      (or (member-equal (car left) right)
          (q718875-sets-intersect-p (cdr left) right))
    nil))

(defun q718875-intersects-every-set-p (set family)
  (if (consp family)
      (and (q718875-sets-intersect-p set (car family))
           (q718875-intersects-every-set-p set (cdr family)))
    t))

;; Including the current set in each comparison preserves Mathlib's
;; Intersecting condition for equal arguments and excludes an empty member.

(defun q718875-intersecting-family-p (family)
  (if (consp family)
      (and (q718875-intersects-every-set-p
            (car family) family)
           (q718875-intersecting-family-p (cdr family)))
    (equal family nil)))

(defun q718875-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (q718875-binomial-coefficient (- n 1) k)
       (q718875-binomial-coefficient (- n 1) (- k 1)))))

(defun thousand-theorems-q718875-erdos-ko-rado-theorem-statement
    (n r family)
  (implies
   (and
    (natp n)
    (natp r)
    (q718875-family-p family n)
    (q718875-intersecting-family-p family)
    (q718875-sized-family-p family r)
    (<= r (floor n 2)))
   (<=
    (len family)
    (q718875-binomial-coefficient
     (nfix (- n 1))
     (nfix (- r 1))))))

(value-triple :itpeval-statement-checked)
:q
