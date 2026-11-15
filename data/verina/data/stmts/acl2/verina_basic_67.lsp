;; Statement-only formalization of VERINA corpus artifact verina_basic_67,
;; catalog title "IsPalindrome": a deterministic Unicode-character-list
;; program compares mirrored entries and returns true exactly when the list is
;; a palindrome. This file contains no proof.

(in-package "ACL2")

;; A Lean List Char is represented bijectively by a proper ACL2 list of
;; Unicode scalar values, preserving the complete Lean Char domain.

(defun verina-basic-67-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-67-char-list-p (x)
  (declare (xargs :measure (acl2-count x)))
  (if (consp x)
      (and
       (verina-basic-67-unicode-scalar-p (car x))
       (verina-basic-67-char-list-p (cdr x)))
    (equal x nil)))

;; The source precondition is True. The List Char binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-67-is-palindrome-precond (x)
  (declare (ignore x))
  t)

;; Option Char is represented by :none or the tagged pair (:some . code).
;; This is exactly the source List.get? operation on natural indices.

(defun verina-basic-67-nth-option (index x)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp x)
        (if (zp index)
            (cons :some (car x))
          (verina-basic-67-nth-option
           (- index 1)
           (cdr x)))
      :none)))

;; This is the source isPalindromeHelper recursion. It compares the optional
;; entries at I and J, returns false on a mismatch or failed access, and moves
;; both indices inward using Lean's natural-number subtraction.

(defun verina-basic-67-is-palindrome-helper (x i j)
  (declare (xargs :measure (nfix j)))
  (if (or
       (not (natp i))
       (not (natp j)))
      nil
    (if (< i j)
        (let ((left
               (verina-basic-67-nth-option i x))
              (right
               (verina-basic-67-nth-option j x)))
          (if (and
               (consp left)
               (equal (car left) :some)
               (consp right)
               (equal (car right) :some))
              (if (not (equal (cdr left) (cdr right)))
                  nil
                (verina-basic-67-is-palindrome-helper
                 x
                 (+ i 1)
                 (- j 1)))
            nil))
      t)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The empty-list branch and the initial indices exactly match
;; the source executable IsPalindrome definition.

(defun verina-basic-67-is-palindrome (x)
  (if (equal (len x) 0)
      t
    (verina-basic-67-is-palindrome-helper
     x
     0
     (- (len x) 1))))

;; List.get! returns Unicode NUL outside the natural in-bounds case.

(defun verina-basic-67-char-at (index x)
  (if (and
       (natp index)
       (< index (len x)))
      (nth index x)
    0))

;; ACL2 NFIX of an integer difference is Lean's truncated Nat subtraction.

(defun verina-basic-67-nat-sub (left right)
  (nfix (- left right)))

;; This preserves the postcondition's universal Nat quantifier and its exact
;; mirrored index x.length - i - 1, with left-associative truncated
;; subtraction.

(defun-sk verina-basic-67-mirrored-at-every-index-p (x)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len x)))
     (equal
      (verina-basic-67-char-at i x)
      (verina-basic-67-char-at
       (verina-basic-67-nat-sub
        (verina-basic-67-nat-sub (len x) i)
        1)
       x)))))

(defun verina-basic-67-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This is the complete source postcondition. Boolean coercion in the Lean
;; biconditional is represented by equality of RESULT with true.

(defun verina-basic-67-is-palindrome-postcond (x result)
  (and
   (verina-basic-67-char-list-p x)
   (verina-basic-67-bool-p result)
   (iff
    (equal result t)
    (verina-basic-67-mirrored-at-every-index-p x))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite Lean character list, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk verina-basic-67-is-palindrome-spec-satisfied-statement ()
  (forall (x)
    (implies
     (and
      (verina-basic-67-char-list-p x)
      (verina-basic-67-is-palindrome-precond x))
     (verina-basic-67-is-palindrome-postcond
      x
      (verina-basic-67-is-palindrome x)))))

(value-triple :itpeval-statement-checked)
:q
