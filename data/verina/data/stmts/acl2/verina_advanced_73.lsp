;; Statement-only formalization of VERINA corpus artifact verina_advanced_73,
;; "smallestMissing": an exact recursive scan of a strictly increasing natural-
;; number list returns its least missing natural, together with the complete
;; precondition and postcondition correctness contract. This file contains no proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-73-natural-listp (l)
  (declare (xargs :measure (acl2-count l)))
  (if (consp l)
      (and
       (natp (car l))
       (verina-advanced-73-natural-listp (cdr l)))
    (equal l nil)))

;; List.Pairwise (fun x y => x < y) requires each head to be less than every
;; later element and recursively imposes the same requirement on the tail.

(defun verina-advanced-73-head-less-than-all-p (x l)
  (declare (xargs :measure (acl2-count l)))
  (if (consp l)
      (and
       (< x (car l))
       (verina-advanced-73-head-less-than-all-p
        x
        (cdr l)))
    (equal l nil)))

(defun verina-advanced-73-pairwise-strictly-increasing-p (l)
  (declare (xargs :measure (acl2-count l)))
  (if (consp l)
      (and
       (verina-advanced-73-head-less-than-all-p
        (car l)
        (cdr l))
       (verina-advanced-73-pairwise-strictly-increasing-p
        (cdr l)))
    (equal l nil)))

(defun verina-advanced-73-smallest-missing-precond (l)
  (verina-advanced-73-pairwise-strictly-increasing-p l))

;; This is the source-local search recursion. Equality advances both the list
;; and candidate, a greater head returns the candidate, and a smaller head is
;; skipped without changing the candidate.

(defun verina-advanced-73-search (lst n)
  (declare (xargs :measure (acl2-count lst)))
  (if (consp lst)
      (let ((x (car lst))
            (xs (cdr lst)))
        (if (equal x n)
            (verina-advanced-73-search xs (+ n 1))
          (if (> x n)
              n
            (verina-advanced-73-search xs n))))
    n))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. SORTEDLIST is the source identity binding of L.

(defun verina-advanced-73-smallest-missing (l)
  (verina-advanced-73-search l 0))

;; Descending from RESULT checks exactly every natural candidate satisfying
;; candidate < RESULT, which is equivalent to the source universal quantifier.

(defun verina-advanced-73-all-smaller-members-p (result l)
  (declare (xargs :measure (nfix result)))
  (if (not (natp result))
      nil
    (if (zp result)
        t
      (let ((candidate (- result 1)))
        (and
         (member-equal candidate l)
         (verina-advanced-73-all-smaller-members-p
          candidate
          l))))))

(defun verina-advanced-73-smallest-missing-postcond
    (l result)
  (and
   (verina-advanced-73-natural-listp l)
   (natp result)
   (not (member-equal result l))
   (verina-advanced-73-all-smaller-members-p result l)))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Nat binder and complete source precondition;
;; its conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-73-smallest-missing-spec-satisfied-statement
    (l)
  (implies
   (and
    (verina-advanced-73-natural-listp l)
    (verina-advanced-73-smallest-missing-precond l))
   (verina-advanced-73-smallest-missing-postcond
    l
    (verina-advanced-73-smallest-missing l))))

(value-triple :itpeval-statement-checked)
:q
