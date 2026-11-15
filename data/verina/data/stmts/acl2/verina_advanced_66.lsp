;; Statement-only formalization of VERINA corpus artifact verina_advanced_66,
;; "reverseWords": a deterministic Unicode-string program splits on spaces,
;; removes empty words, reverses their order, and rejoins them with one space.
;; This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain instead of restricting
;; strings to ACL2's host character set. A List String is a proper list of
;; such scalar lists.

(defun verina-advanced-66-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-66-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-66-unicode-scalar-p (car s))
       (verina-advanced-66-string-p (cdr s)))
    (equal s nil)))

(defun verina-advanced-66-string-list-p (strings)
  (declare (xargs :measure (acl2-count strings)))
  (if (consp strings)
      (and
       (verina-advanced-66-string-p (car strings))
       (verina-advanced-66-string-list-p (cdr strings)))
    (equal strings nil)))

;; The source precondition is True. The String binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-66-reverse-words-precond (words-str)
  (declare (ignore words-str))
  t)

;; Exact String.splitOn " " for the list representation. CURRENT-REVERSED is
;; the current word in reverse order. Every encountered U+0020 emits a word,
;; including empty words, and exhaustion emits the final word; therefore the
;; empty input splits to the singleton list containing the empty string.

(defun verina-advanced-66-split-on-space-aux
    (characters current-reversed)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (if (equal (car characters) 32)
          (cons
           (reverse current-reversed)
           (verina-advanced-66-split-on-space-aux
            (cdr characters)
            nil))
        (verina-advanced-66-split-on-space-aux
         (cdr characters)
         (cons (car characters) current-reversed)))
    (list (reverse current-reversed))))

(defun verina-advanced-66-split-on-space (words-str)
  (verina-advanced-66-split-on-space-aux words-str nil))

;; This is the source-local filterNonEmpty helper.

(defun verina-advanced-66-filter-nonempty (words)
  (declare (xargs :measure (acl2-count words)))
  (if (consp words)
      (if (equal (car words) nil)
          (verina-advanced-66-filter-nonempty (cdr words))
        (cons
         (car words)
         (verina-advanced-66-filter-nonempty (cdr words))))
    nil))

;; This is the source-local joinWithSpace helper. The scalar value 32 is the
;; one-character string " ".

(defun verina-advanced-66-join-with-space (words)
  (declare (xargs :measure (acl2-count words)))
  (if (consp words)
      (if (consp (cdr words))
          (append
           (car words)
           (cons
            32
            (verina-advanced-66-join-with-space
             (cdr words))))
        (car words))
    nil))

;; The proof-valued True precondition argument is computationally irrelevant.
;; The let-bound stages below preserve the complete executable source program.

(defun verina-advanced-66-reverse-words (words-str)
  (let* ((raw-words
          (verina-advanced-66-split-on-space words-str))
         (filtered-words
          (verina-advanced-66-filter-nonempty raw-words))
         (rev-words
          (reverse filtered-words))
         (result
          (verina-advanced-66-join-with-space rev-words)))
    result))

;; String.intercalate " " is represented independently as String.join after
;; inserting the singleton-space string between adjacent list elements.

(defun verina-advanced-66-intersperse-space (words)
  (declare (xargs :measure (acl2-count words)))
  (if (consp words)
      (if (consp (cdr words))
          (cons
           (car words)
           (cons
            (list 32)
            (verina-advanced-66-intersperse-space
             (cdr words))))
        (list (car words)))
    nil))

(defun verina-advanced-66-concat-strings (strings)
  (declare (xargs :measure (acl2-count strings)))
  (if (consp strings)
      (append
       (car strings)
       (verina-advanced-66-concat-strings (cdr strings)))
    nil))

(defun verina-advanced-66-intercalate-space (words)
  (verina-advanced-66-concat-strings
   (verina-advanced-66-intersperse-space words)))

;; This preserves the source postcondition's internal existential List String
;; witness and both conjuncts that characterize it.

(defun-sk verina-advanced-66-reverse-words-postcond
    (words-str result)
  (exists
   (words)
   (and
    (verina-advanced-66-string-p words-str)
    (verina-advanced-66-string-p result)
    (verina-advanced-66-string-list-p words)
    (equal
     words
     (verina-advanced-66-filter-nonempty
      (verina-advanced-66-split-on-space words-str)))
    (equal
     result
     (verina-advanced-66-intercalate-space
      (reverse words))))))

;; This predicate is the unproved final correctness proposition connecting
;; the source precondition and postcondition to the exact executable result.

(defun
    verina-advanced-66-reverse-words-spec-satisfied-statement
    (words-str)
  (implies
   (and
    (verina-advanced-66-string-p words-str)
    (verina-advanced-66-reverse-words-precond words-str))
   (verina-advanced-66-reverse-words-postcond
    words-str
    (verina-advanced-66-reverse-words words-str))))

(value-triple :itpeval-statement-checked)
:q
