;; Statement-only formalization of VERINA corpus artifact verina_advanced_12,
;; "firstDuplicate": a deterministic left-to-right scan returns the first
;; integer encountered for a second time, or none when the input has no
;; duplicates, together with its correctness contract. This file contains no proof.

(in-package "ACL2")

(defun verina-advanced-12-integer-listp (lst)
  (if (consp lst)
      (and
       (integerp (car lst))
       (verina-advanced-12-integer-listp (cdr lst)))
    (equal lst nil)))

;; The source precondition is True; the List Int type is made explicit in the
;; final statement predicate.

(defun verina-advanced-12-first-duplicate-precond (lst)
  (declare (ignore lst))
  t)

;; Option Int is represented by :none or by the tagged pair (:some . value).

(defun verina-advanced-12-option-int-p (result)
  (or
   (equal result :none)
   (and
    (consp result)
    (equal (car result) :some)
    (integerp (cdr result)))))

(defun verina-advanced-12-some (value)
  (cons :some value))

(defun verina-advanced-12-first-duplicate-helper (seen remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (member-equal (car remaining) seen)
          (verina-advanced-12-some (car remaining))
        (verina-advanced-12-first-duplicate-helper
         (cons (car remaining) seen)
         (cdr remaining)))
    :none))

(defun verina-advanced-12-first-duplicate (lst)
  (verina-advanced-12-first-duplicate-helper nil lst))

(defun verina-advanced-12-list-count (value lst)
  (if (consp lst)
      (+
       (if (equal (car lst) value) 1 0)
       (verina-advanced-12-list-count value (cdr lst)))
    0))

;; This is List.idxOf: failure at the empty suffix returns zero, so failure in
;; a nonempty list returns that list's length through the recursive increments.

(defun verina-advanced-12-index-of (value lst)
  (if (consp lst)
      (if (equal (car lst) value)
          0
        (+ 1
           (verina-advanced-12-index-of value (cdr lst))))
    0))

(defun verina-advanced-12-drop (count lst)
  (if (and (posp count) (consp lst))
      (verina-advanced-12-drop (- count 1) (cdr lst))
    lst))

(defun verina-advanced-12-second-occ-index (lst value)
  (let ((first
         (verina-advanced-12-index-of value lst)))
    (+
     first
     1
     (verina-advanced-12-index-of
      value
      (verina-advanced-12-drop (+ first 1) lst)))))

(defun verina-advanced-12-no-duplicates-p (lst)
  (if (consp lst)
      (and
       (not (member-equal (car lst) (cdr lst)))
       (verina-advanced-12-no-duplicates-p (cdr lst)))
    (equal lst nil)))

(defun verina-advanced-12-all-second-indices-at-least-p
    (remaining whole first-duplicate)
  (if (consp remaining)
      (and
       (or
        (equal
         (verina-advanced-12-list-count
          (car remaining) whole)
         1)
        (<=
         (verina-advanced-12-second-occ-index
          whole first-duplicate)
         (verina-advanced-12-second-occ-index
          whole (car remaining))))
       (verina-advanced-12-all-second-indices-at-least-p
        (cdr remaining) whole first-duplicate))
    (equal remaining nil)))

(defun verina-advanced-12-first-duplicate-postcond
    (lst result)
  (and
   (verina-advanced-12-integer-listp lst)
   (verina-advanced-12-option-int-p result)
   (if (equal result :none)
       (verina-advanced-12-no-duplicates-p lst)
     (let ((value (cdr result)))
       (and
        (< 1
           (verina-advanced-12-list-count value lst))
        (verina-advanced-12-all-second-indices-at-least-p
         lst lst value))))))

(defun verina-advanced-12-first-duplicate-spec-satisfied-statement
    (lst)
  (implies
   (and
    (verina-advanced-12-integer-listp lst)
    (verina-advanced-12-first-duplicate-precond lst))
   (verina-advanced-12-first-duplicate-postcond
    lst
    (verina-advanced-12-first-duplicate lst))))

(value-triple :itpeval-statement-checked)
:q
