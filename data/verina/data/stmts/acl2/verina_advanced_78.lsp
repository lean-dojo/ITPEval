;; Statement-only formalization of VERINA corpus artifact verina_advanced_78,
;; catalog title "twoSum": an exact integer-list complement-search program
;; returns the unique pair of increasing indices whose values sum to the
;; target. This file contains no proof.

(in-package "ACL2")

;; Lean's List Int domain is represented by proper ACL2 lists of integers.

(defun verina-advanced-78-integer-listp (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (and
       (integerp (car nums))
       (verina-advanced-78-integer-listp (cdr nums)))
    (equal nums nil)))

;; For each head value, pair it with every later value, then recurse on the
;; tail. This is exactly the source List.range/flatMap/drop/map construction,
;; including order and multiplicity.

(defun verina-advanced-78-add-to-each (x nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (cons
       (+ x (car nums))
       (verina-advanced-78-add-to-each
        x
        (cdr nums)))
    nil))

(defun verina-advanced-78-pairwise-sums (nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (append
       (verina-advanced-78-add-to-each
        (car nums)
        (cdr nums))
       (verina-advanced-78-pairwise-sums
        (cdr nums)))
    nil))

(defun verina-advanced-78-count-equal (value nums)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (+
       (if (equal value (car nums)) 1 0)
       (verina-advanced-78-count-equal
        value
        (cdr nums)))
    0))

(defun verina-advanced-78-two-sum-precond (nums target)
  (and
   (> (len nums) 1)
   (equal
    (verina-advanced-78-count-equal
     target
     (verina-advanced-78-pairwise-sums nums))
    1)))

;; NIL represents Option.none and a natural represents Option.some. ACL2's
;; natural zero is non-NIL, so this representation also distinguishes some 0.

(defun verina-advanced-78-find-complement-aux
    (nums target i x j)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (if (equal (+ x (car nums)) target)
          (+ i j 1)
        (verina-advanced-78-find-complement-aux
         (cdr nums)
         target
         i
         x
         (+ j 1)))
    nil))

(defun verina-advanced-78-find-complement
    (nums target i x)
  (verina-advanced-78-find-complement-aux
   nums
   target
   i
   x
   0))

;; Results are dotted pairs (first-index . second-index), representing
;; Prod Nat Nat. Lean's panic! returns the inhabited default (0, 0) after
;; reporting the panic; the result component is preserved in the empty case.

(defun verina-advanced-78-two-sum-aux
    (nums target i)
  (declare (xargs :measure (acl2-count nums)))
  (if (consp nums)
      (let ((j
             (verina-advanced-78-find-complement
              (cdr nums)
              target
              i
              (car nums))))
        (if j
            (cons i j)
          (verina-advanced-78-two-sum-aux
           (cdr nums)
           target
           (+ i 1))))
    (cons 0 0)))

;; The proof-valued precondition argument is computationally irrelevant in
;; Lean and is erased here. The remaining call is exactly twoSumAux nums
;; target 0.

(defun verina-advanced-78-two-sum (nums target)
  (verina-advanced-78-two-sum-aux
   nums
   target
   0))

;; The source precondition proof parameter is unused by the postcondition and
;; is erased. Dotted-pair projections are car and cdr, while ACL2 nth is the
;; same zero-based lookup on the explicitly in-bounds indices.

(defun verina-advanced-78-two-sum-postcond
    (nums target result)
  (let ((i (car result))
        (j (cdr result)))
    (and
     (verina-advanced-78-integer-listp nums)
     (integerp target)
     (consp result)
     (natp i)
     (natp j)
     (< i j)
     (< i (len nums))
     (< j (len nums))
     (equal
      (+ (nth i nums) (nth j nums))
      target))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the List Int and Int binder domains and the complete
;; unique-pair precondition; its conclusion applies the complete postcondition
;; to the exact executable result.

(defun
    verina-advanced-78-two-sum-spec-satisfied-statement
    (nums target)
  (implies
   (and
    (verina-advanced-78-integer-listp nums)
    (integerp target)
    (verina-advanced-78-two-sum-precond
     nums
     target))
   (verina-advanced-78-two-sum-postcond
    nums
    target
    (verina-advanced-78-two-sum
     nums
     target))))

(value-triple :itpeval-statement-checked)
:q
