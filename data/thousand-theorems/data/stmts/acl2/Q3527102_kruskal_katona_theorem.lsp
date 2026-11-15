;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q3527102, "Kruskal-Katona theorem": among
;; families of r-element subsets of Fin n, a
;; colexicographic initial segment has shadow no larger than that of any family
;; with at least as many members. This file contains no proof.

(in-package "ACL2")

;; A Fin n element is represented by a natural below n. Duplicate-free true
;; lists represent finite subsets, and outer lists contain no two
;; extensionally equal subsets. Hence valid outer lists represent exactly
;; Finset (Finset (Fin n)), independently of list order.

(defun q3527102-fin-element-p (x n)
  (and (natp x)
       (< x n)))

(defun q3527102-fin-set-elements-p (set n)
  (if (consp set)
      (and (q3527102-fin-element-p (car set) n)
           (q3527102-fin-set-elements-p (cdr set) n))
    (equal set nil)))

(defun q3527102-fin-set-p (set n)
  (and (true-listp set)
       (no-duplicatesp-equal set)
       (q3527102-fin-set-elements-p set n)))

(defun q3527102-subset-p (left right)
  (if (consp left)
      (and (member-equal (car left) right)
           (q3527102-subset-p (cdr left) right))
    t))

(defun q3527102-set-equal-p (left right)
  (and (q3527102-subset-p left right)
       (q3527102-subset-p right left)))

(defun q3527102-family-member-p (set family)
  (if (consp family)
      (or (q3527102-set-equal-p set (car family))
          (q3527102-family-member-p set (cdr family)))
    nil))

(defun q3527102-set-distinct-from-family-p (set family)
  (if (consp family)
      (and (not (q3527102-set-equal-p set (car family)))
           (q3527102-set-distinct-from-family-p set (cdr family)))
    t))

(defun q3527102-family-p (family n)
  (if (consp family)
      (and (q3527102-fin-set-p (car family) n)
           (q3527102-set-distinct-from-family-p
            (car family) (cdr family))
           (q3527102-family-p (cdr family) n))
    (equal family nil)))

(defun q3527102-sized-family-p (family r)
  (if (consp family)
      (and (equal (len (car family)) r)
           (q3527102-sized-family-p (cdr family) r))
    t))

;; This is Mathlib's colex non-strict relation specialized to Fin n:
;; every element of LEFT \ RIGHT is bounded above by an element of
;; RIGHT \ LEFT.

(defun q3527102-colex-witness-p (a left right)
  (if (consp right)
      (or (and (not (member-equal (car right) left))
               (<= a (car right)))
          (q3527102-colex-witness-p a left (cdr right)))
    nil))

(defun q3527102-colex-le-aux-p (remaining left right)
  (if (consp remaining)
      (and
       (or (member-equal (car remaining) right)
           (q3527102-colex-witness-p
            (car remaining) left right))
       (q3527102-colex-le-aux-p
        (cdr remaining) left right))
    t))

(defun q3527102-colex-le-p (left right)
  (q3527102-colex-le-aux-p left left right))

(defun q3527102-colex-lt-p (left right)
  (and (not (q3527102-set-equal-p left right))
       (q3527102-colex-le-p left right)))

;; Enumerate every subset of Fin n. This is used only to express the universal
;; downward-closure clause in IsInitSeg; it does not restrict the source
;; domain, which is already the finite type Fin n.

(defun q3527102-fin-range (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (append (q3527102-fin-range (- n 1))
            (list (- n 1)))))

(defun q3527102-prepend-to-each (x sets)
  (if (consp sets)
      (cons (cons x (car sets))
            (q3527102-prepend-to-each x (cdr sets)))
    nil))

(defun q3527102-powerset (carrier)
  (if (consp carrier)
      (let ((tail-powerset
             (q3527102-powerset (cdr carrier))))
        (append
         tail-powerset
         (q3527102-prepend-to-each
          (car carrier) tail-powerset)))
    (list nil)))

(defun q3527102-all-lower-r-sets-present-p
    (set candidates family r)
  (if (consp candidates)
      (and
       (implies
        (and (equal (len (car candidates)) r)
             (q3527102-colex-lt-p (car candidates) set))
        (q3527102-family-member-p (car candidates) family))
       (q3527102-all-lower-r-sets-present-p
        set (cdr candidates) family r))
    t))

(defun q3527102-initial-segment-members-p
    (remaining-family whole-family candidates r)
  (if (consp remaining-family)
      (and
       (q3527102-all-lower-r-sets-present-p
        (car remaining-family) candidates whole-family r)
       (q3527102-initial-segment-members-p
        (cdr remaining-family) whole-family candidates r))
    t))

(defun q3527102-initial-segment-p (family n r)
  (and
   (q3527102-sized-family-p family r)
   (q3527102-initial-segment-members-p
    family
    family
    (q3527102-powerset (q3527102-fin-range n))
    r)))

;; The shadow is the extensional family of every one-element erasure.

(defun q3527102-erase-one (a set)
  (if (consp set)
      (if (equal a (car set))
          (cdr set)
        (cons (car set)
              (q3527102-erase-one a (cdr set))))
    nil))

(defun q3527102-family-insert (set family)
  (if (q3527102-family-member-p set family)
      family
    (cons set family)))

(defun q3527102-shadow-of-set-aux (remaining set shadow)
  (if (consp remaining)
      (q3527102-shadow-of-set-aux
       (cdr remaining)
       set
       (q3527102-family-insert
        (q3527102-erase-one (car remaining) set)
        shadow))
    shadow))

(defun q3527102-shadow-aux (family shadow)
  (if (consp family)
      (q3527102-shadow-aux
       (cdr family)
       (q3527102-shadow-of-set-aux
        (car family) (car family) shadow))
    shadow))

(defun q3527102-shadow (family)
  (q3527102-shadow-aux family nil))

(defun thousand-theorems-q3527102-kruskal-katona-statement
    (n r family-a family-c)
  (implies
   (and
    (natp n)
    (natp r)
    (q3527102-family-p family-a n)
    (q3527102-family-p family-c n)
    (q3527102-sized-family-p family-a r)
    (<= (len family-c) (len family-a))
    (q3527102-initial-segment-p family-c n r))
   (<=
    (len (q3527102-shadow family-c))
    (len (q3527102-shadow family-a)))))

(value-triple :itpeval-statement-checked)
:q
