;; Statement-only formalization of VERINA corpus artifact verina_advanced_26,
;; "letterCombinations": the executable telephone-keypad recursion generates
;; letter strings for a Unicode digit string, together with its independently
;; folded combination correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. Thus a List String is a proper list of such scalar lists.

(defun verina-advanced-26-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-26-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-26-unicode-scalar-p (car s))
       (verina-advanced-26-string-p (cdr s)))
    (equal s nil)))

(defun verina-advanced-26-string-list-p (strings)
  (declare (xargs :measure (acl2-count strings)))
  (if (consp strings)
      (and
       (verina-advanced-26-string-p (car strings))
       (verina-advanced-26-string-list-p (cdr strings)))
    (equal strings nil)))

;; Character codes below are the Unicode scalar values of the source literals.

(defun verina-advanced-26-digit-to-letters (c)
  (cond
   ((equal c 50) (list 97 98 99))
   ((equal c 51) (list 100 101 102))
   ((equal c 52) (list 103 104 105))
   ((equal c 53) (list 106 107 108))
   ((equal c 54) (list 109 110 111))
   ((equal c 55) (list 112 113 114 115))
   ((equal c 56) (list 116 117 118))
   ((equal c 57) (list 119 120 121 122))
   (t nil)))

(defun verina-advanced-26-letter-combinations-precond (digits)
  (declare (ignore digits))
  t)

;; This predicate is the implementation's chars.any test: it detects exactly
;; those characters whose digitToLetters image is empty.

(defun verina-advanced-26-has-empty-mapping-p (chars)
  (declare (xargs :measure (acl2-count chars)))
  (if (consp chars)
      (or
       (equal
        (verina-advanced-26-digit-to-letters (car chars))
        nil)
       (verina-advanced-26-has-empty-mapping-p (cdr chars)))
    nil))

(defun verina-advanced-26-singleton-strings (letters)
  (declare (xargs :measure (acl2-count letters)))
  (if (consp letters)
      (cons
       (list (car letters))
       (verina-advanced-26-singleton-strings (cdr letters)))
    nil))

(defun verina-advanced-26-prepend-letter-to-strings
    (letter strings)
  (declare (xargs :measure (acl2-count strings)))
  (if (consp strings)
      (cons
       (cons letter (car strings))
       (verina-advanced-26-prepend-letter-to-strings
        letter
        (cdr strings)))
    nil))

;; This is currentLetters.flatMap over the recursively computed suffixes.

(defun verina-advanced-26-prepend-each-letter
    (letters strings)
  (declare (xargs :measure (acl2-count letters)))
  (if (consp letters)
      (append
       (verina-advanced-26-prepend-letter-to-strings
        (car letters)
        strings)
       (verina-advanced-26-prepend-each-letter
        (cdr letters)
        strings))
    nil))

;; Exact translation of the source's local right-recursive go function,
;; including its special empty-suffix branch.

(defun verina-advanced-26-letter-combinations-go (chars)
  (declare (xargs :measure (acl2-count chars)))
  (if (consp chars)
      (let* ((rest-combinations
              (verina-advanced-26-letter-combinations-go
               (cdr chars)))
             (current-letters
              (verina-advanced-26-digit-to-letters
               (car chars))))
        (if (equal rest-combinations nil)
            (verina-advanced-26-singleton-strings
             current-letters)
          (verina-advanced-26-prepend-each-letter
           current-letters
           rest-combinations)))
    nil))

;; The proof-valued True precondition argument is computationally irrelevant.
;; Under the canonical string representation, String.toList is the identity.

(defun verina-advanced-26-letter-combinations (digits)
  (if (verina-advanced-26-has-empty-mapping-p digits)
      nil
    (verina-advanced-26-letter-combinations-go digits)))

;; The postcondition tests invalidity independently by membership in 2,...,9.

(defun verina-advanced-26-valid-digit-p (c)
  (or
   (equal c 50)
   (equal c 51)
   (equal c 52)
   (equal c 53)
   (equal c 54)
   (equal c 55)
   (equal c 56)
   (equal c 57)))

(defun verina-advanced-26-contains-invalid-digit-p (chars)
  (declare (xargs :measure (acl2-count chars)))
  (if (consp chars)
      (or
       (not
        (verina-advanced-26-valid-digit-p (car chars)))
       (verina-advanced-26-contains-invalid-digit-p
        (cdr chars)))
    nil))

;; The next three definitions reproduce the postcondition's List.map followed
;; by foldl from [""]. Each step flatMaps the accumulated strings and appends
;; one current digit letter to the right of each string.

(defun verina-advanced-26-append-each-letter
    (string letters)
  (declare (xargs :measure (acl2-count letters)))
  (if (consp letters)
      (cons
       (append string (list (car letters)))
       (verina-advanced-26-append-each-letter
        string
        (cdr letters)))
    nil))

(defun verina-advanced-26-expected-fold-step
    (accumulator letters)
  (declare (xargs :measure (acl2-count accumulator)))
  (if (consp accumulator)
      (append
       (verina-advanced-26-append-each-letter
        (car accumulator)
        letters)
       (verina-advanced-26-expected-fold-step
        (cdr accumulator)
        letters))
    nil))

(defun verina-advanced-26-expected-fold
    (remaining-digits accumulator)
  (declare (xargs :measure (acl2-count remaining-digits)))
  (if (consp remaining-digits)
      (verina-advanced-26-expected-fold
       (cdr remaining-digits)
       (verina-advanced-26-expected-fold-step
        accumulator
        (verina-advanced-26-digit-to-letters
         (car remaining-digits))))
    accumulator))

(defun verina-advanced-26-expected-combinations (digits)
  (verina-advanced-26-expected-fold digits (list nil)))

(defun verina-advanced-26-all-members-of-p (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (consp left)
      (and
       (member-equal (car left) right)
       (verina-advanced-26-all-members-of-p
        (cdr left)
        right))
    t))

(defun verina-advanced-26-letter-combinations-postcond
    (digits result)
  (and
   (verina-advanced-26-string-p digits)
   (verina-advanced-26-string-list-p result)
   (if (equal digits nil)
       (equal result nil)
     (if (verina-advanced-26-contains-invalid-digit-p digits)
         (equal result nil)
       (let ((expected
              (verina-advanced-26-expected-combinations digits)))
         (and
          (equal (len result) (len expected))
          (verina-advanced-26-all-members-of-p
           result
           expected)
          (verina-advanced-26-all-members-of-p
           expected
           result)))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves the Lean String binder and the source precondition.

(defun
    verina-advanced-26-letter-combinations-spec-satisfied-statement
    (digits)
  (implies
   (and
    (verina-advanced-26-string-p digits)
    (verina-advanced-26-letter-combinations-precond digits))
   (verina-advanced-26-letter-combinations-postcond
    digits
    (verina-advanced-26-letter-combinations digits))))

(value-triple :itpeval-statement-checked)
:q
