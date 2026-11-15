;; Statement-only formalization of VERINA corpus artifact verina_basic_71,
;; catalog title "LongestCommonPrefix": a deterministic Unicode-character-list
;; program computes the longest prefix shared by two input lists and satisfies
;; the complete maximal-common-prefix contract. This file contains no proof.

(in-package "ACL2")

;; A Lean List Char is represented bijectively by a proper ACL2 list of
;; Unicode scalar values, preserving the complete Lean Char domain.

(defun verina-basic-71-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-71-char-list-p (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (and
       (verina-basic-71-unicode-scalar-p
        (car characters))
       (verina-basic-71-char-list-p
        (cdr characters)))
    (equal characters nil)))

;; The source precondition is True. The two List Char binder domains remain
;; explicit in the final correctness proposition.

(defun verina-basic-71-longest-common-prefix-precond
    (str1 str2)
  (declare (ignore str1 str2))
  t)

;; This is Nat.min on the natural list lengths used by the implementation.

(defun verina-basic-71-nat-min (left right)
  (if (<= left right)
      left
    right))

;; Option Char is represented by :none or the tagged pair (:some . code).
;; This is exactly List.get? at a natural index.

(defun verina-basic-71-nth-option (index characters)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp characters)
        (if (zp index)
            (cons :some (car characters))
          (verina-basic-71-nth-option
           (- index 1)
           (cdr characters)))
      :none)))

;; This is the source local AUX recursion. MIN-LENGTH is the closed-over
;; Nat.min of the input lengths. At each natural IDX below that bound, the
;; optional entries are compared; a mismatch returns ACC, while a match
;; appends the character and advances the index.

(defun verina-basic-71-longest-common-prefix-aux
    (idx acc min-length str1 str2)
  (declare
   (xargs :measure
          (nfix (- min-length idx))))
  (if (and
       (natp idx)
       (natp min-length)
       (< idx min-length))
      (let ((left
             (verina-basic-71-nth-option idx str1))
            (right
             (verina-basic-71-nth-option idx str2)))
        (if (and
             (consp left)
             (equal (car left) :some)
             (consp right)
             (equal (car right) :some))
            (let ((c1 (cdr left))
                  (c2 (cdr right)))
              (if (not (equal c1 c2))
                  acc
                (verina-basic-71-longest-common-prefix-aux
                 (+ idx 1)
                 (append acc (list c1))
                 min-length
                 str1
                 str2)))
          acc))
    acc))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The exact source call starts AUX at index zero with an empty
;; accumulator and the minimum input length.

(defun verina-basic-71-longest-common-prefix
    (str1 str2)
  (let ((min-length
         (verina-basic-71-nat-min
          (len str1)
          (len str2))))
    (verina-basic-71-longest-common-prefix-aux
     0
     nil
     min-length
     str1
     str2)))

;; Exact recursive encoding of List.take on natural lengths.

(defun verina-basic-71-take (n characters)
  (declare (xargs :measure (nfix n)))
  (if (or
       (not (natp n))
       (zp n)
       (not (consp characters)))
      nil
    (cons
     (car characters)
     (verina-basic-71-take
      (- n 1)
      (cdr characters)))))

;; This is the complete source postcondition. The tagged optional accesses
;; preserve the final disjunction: the result reaches an input's length, or
;; the next optional characters differ.

(defun verina-basic-71-longest-common-prefix-postcond
    (str1 str2 result)
  (and
   (verina-basic-71-char-list-p str1)
   (verina-basic-71-char-list-p str2)
   (verina-basic-71-char-list-p result)
   (<= (len result) (len str1))
   (equal
    result
    (verina-basic-71-take
     (len result)
     str1))
   (<= (len result) (len str2))
   (equal
    result
    (verina-basic-71-take
     (len result)
     str2))
   (or
    (equal (len result) (len str1))
    (equal (len result) (len str2))
    (not
     (equal
      (verina-basic-71-nth-option
       (len result)
       str1)
      (verina-basic-71-nth-option
       (len result)
       str2))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every pair of finite Lean character lists, assumes exactly the source
;; True precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-71-longest-common-prefix-spec-satisfied-statement
    ()
  (forall (str1 str2)
    (implies
     (and
      (verina-basic-71-char-list-p str1)
      (verina-basic-71-char-list-p str2)
      (verina-basic-71-longest-common-prefix-precond
       str1
       str2))
     (verina-basic-71-longest-common-prefix-postcond
      str1
      str2
      (verina-basic-71-longest-common-prefix
       str1
       str2)))))

(value-triple :itpeval-statement-checked)
:q
