;; Statement-only formalization of VERINA corpus artifact verina_basic_22,
;; catalog title "dissimilarElements": a deterministic integer-array program
;; returns the sorted duplicate-free symmetric difference of two arrays,
;; together with its full membership and ordering contract. This file contains no proof.

(in-package "ACL2")

;; ACL2 proper lists of integers represent exactly the finite Array Int inputs
;; and output.

(defun verina-basic-22-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-22-int-array-p (cdr arr)))
    (equal arr nil)))

;; This is the source inArray helper: Array.any with integer equality, returned
;; as an ACL2 Boolean.

(defun verina-basic-22-in-array (arr x)
  (if (member-equal x arr)
      t
    nil))

;; The source precondition is True. Both Array Int domains remain explicit in
;; the final correctness proposition.

(defun verina-basic-22-dissimilar-elements-precond (a b)
  (declare (ignore a b))
  t)

;; A duplicate-free ACL2 list represents the source HashSet extensionally.
;; HashSet.insert changes exactly the represented membership when the value is
;; fresh; its internal bucket order is unobservable before the final sort.

(defun verina-basic-22-set-insert (x set)
  (if (verina-basic-22-in-array set x)
      set
    (cons x set)))

;; This is one source Array.foldl. Each value absent from OTHER is inserted
;; into SET, while a value present in OTHER leaves SET unchanged.

(defun verina-basic-22-fold-dissimilar
    (remaining other set)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((x (car remaining)))
        (verina-basic-22-fold-dissimilar
         (cdr remaining)
         other
         (if (verina-basic-22-in-array other x)
             set
           (verina-basic-22-set-insert x set))))
    set))

;; Insertion sorting is extensionally identical to the source mergeSort here:
;; both return the unique nondecreasing permutation of the HashSet contents.

(defun verina-basic-22-insert-sorted (x sorted)
  (declare (xargs :measure (acl2-count sorted)))
  (if (consp sorted)
      (if (<= x (car sorted))
          (cons x sorted)
        (cons
         (car sorted)
         (verina-basic-22-insert-sorted
          x
          (cdr sorted))))
    (list x)))

(defun verina-basic-22-sort (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (verina-basic-22-insert-sorted
       (car xs)
       (verina-basic-22-sort (cdr xs)))
    nil))

;; These two folds are the exact executable program after erasing the
;; proof-valued True precondition argument. The first adds values unique to A;
;; the second adds values unique to B; the final sort canonically fixes order.

(defun verina-basic-22-dissimilar-elements (a b)
  (let* ((from-a
          (verina-basic-22-fold-dissimilar
           a
           b
           nil))
         (from-b
          (verina-basic-22-fold-dissimilar
           b
           a
           from-a)))
    (verina-basic-22-sort from-b)))

;; This is result.all (fun x => inArray a x != inArray b x).

(defun verina-basic-22-all-memberships-differ-p
    (result a b)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (not
        (equal
         (verina-basic-22-in-array a (car result))
         (verina-basic-22-in-array b (car result))))
       (verina-basic-22-all-memberships-differ-p
        (cdr result)
        a
        b))
    (equal result nil)))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element, recursively.

(defun verina-basic-22-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-basic-22-head-at-most-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-basic-22-pairwise-nondecreasing-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (verina-basic-22-head-at-most-all-p
        (car xs)
        (cdr xs))
       (verina-basic-22-pairwise-nondecreasing-p
        (cdr xs)))
    (equal xs nil)))

;; This is List.Nodup.

(defun verina-basic-22-no-duplicates-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (not
        (verina-basic-22-in-array
         (cdr xs)
         (car xs)))
       (verina-basic-22-no-duplicates-p
        (cdr xs)))
    (equal xs nil)))

;; For every element of SOURCE, this preserves the source conditional:
;; membership in OTHER implies absence from RESULT, and nonmembership in
;; OTHER implies membership in RESULT.

(defun verina-basic-22-directional-coverage-p
    (source other result)
  (declare (xargs :measure (acl2-count source)))
  (if (consp source)
      (and
       (if (verina-basic-22-in-array other (car source))
           (not
            (verina-basic-22-in-array
             result
             (car source)))
         (verina-basic-22-in-array
          result
          (car source)))
       (verina-basic-22-directional-coverage-p
        (cdr source)
        other
        result))
    (equal source nil)))

(defun verina-basic-22-dissimilar-elements-postcond
    (a b result)
  (and
   (verina-basic-22-int-array-p a)
   (verina-basic-22-int-array-p b)
   (verina-basic-22-int-array-p result)
   (verina-basic-22-all-memberships-differ-p
    result
    a
    b)
   (verina-basic-22-pairwise-nondecreasing-p
    result)
   (verina-basic-22-no-duplicates-p
    result)
   (verina-basic-22-directional-coverage-p
    a
    b
    result)
   (verina-basic-22-directional-coverage-p
    b
    a
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; arbitrary Array Int inputs and the True precondition, and applies the full
;; postcondition to the exact executable result.

(defun-sk
    verina-basic-22-dissimilar-elements-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (verina-basic-22-int-array-p a)
      (verina-basic-22-int-array-p b)
      (verina-basic-22-dissimilar-elements-precond a b))
     (verina-basic-22-dissimilar-elements-postcond
      a
      b
      (verina-basic-22-dissimilar-elements a b)))))

(value-triple :itpeval-statement-checked)
:q
