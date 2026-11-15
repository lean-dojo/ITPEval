;; Statement-only formalization of VERINA corpus artifact verina_advanced_59,
;; "palindromeIgnoreNonAlnum": a deterministic Unicode-string program removes
;; non-alphanumeric characters, lowercases ASCII letters, and decides whether
;; the cleaned character list is a palindrome. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves characters beyond ACL2's host character set.

(defun verina-advanced-59-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-59-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-59-unicode-scalar-p (car s))
       (verina-advanced-59-string-p (cdr s)))
    (equal s nil)))

(defun verina-advanced-59-is-upper-alpha (c)
  (and
   (<= 65 c)
   (<= c 90)))

(defun verina-advanced-59-is-lower-alpha (c)
  (and
   (<= 97 c)
   (<= c 122)))

(defun verina-advanced-59-is-alpha (c)
  (or
   (verina-advanced-59-is-upper-alpha c)
   (verina-advanced-59-is-lower-alpha c)))

(defun verina-advanced-59-is-digit (c)
  (and
   (<= 48 c)
   (<= c 57)))

(defun verina-advanced-59-is-alphanumeric (c)
  (or
   (verina-advanced-59-is-alpha c)
   (verina-advanced-59-is-digit c)))

(defun verina-advanced-59-to-lower (c)
  (if (verina-advanced-59-is-upper-alpha c)
      (+ c 32)
    c))

;; These two recursions are respectively the source List.filter and List.map.

(defun verina-advanced-59-filter-alphanumeric (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (if (verina-advanced-59-is-alphanumeric
           (car characters))
          (cons
           (car characters)
           (verina-advanced-59-filter-alphanumeric
            (cdr characters)))
        (verina-advanced-59-filter-alphanumeric
         (cdr characters)))
    nil))

(defun verina-advanced-59-map-to-lower (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (cons
       (verina-advanced-59-to-lower (car characters))
       (verina-advanced-59-map-to-lower
        (cdr characters)))
    nil))

(defun verina-advanced-59-cleaned (s)
  (verina-advanced-59-map-to-lower
   (verina-advanced-59-filter-alphanumeric s)))

(defun verina-advanced-59-palindrome-ignore-nonalnum-precond
    (s)
  (declare (ignore s))
  t)

;; Option Char is represented by :none or the tagged pair (:some . code).

(defun verina-advanced-59-nth-option (index characters)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp characters)
        (if (zp index)
            (cons :some (car characters))
          (verina-advanced-59-nth-option
           (- index 1)
           (cdr characters)))
      :none)))

;; This is the source local check recursion, including optional indexed access,
;; inward index movement, and truncated natural-number subtraction.

(defun verina-advanced-59-check (left right cleaned)
  (declare (xargs :measure (nfix right)))
  (if (or
       (not (natp left))
       (not (natp right)))
      nil
    (if (>= left right)
        t
      (if (equal
           (verina-advanced-59-nth-option left cleaned)
           (verina-advanced-59-nth-option right cleaned))
          (verina-advanced-59-check
           (+ left 1)
           (- right 1)
           cleaned)
        nil))))

;; The source proof-valued True precondition argument is computationally
;; irrelevant. The final statement retains its predicate explicitly.

(defun verina-advanced-59-palindrome-ignore-nonalnum (s)
  (let* ((cleaned
          (verina-advanced-59-cleaned s))
         (n (len cleaned))
         (start-index 0)
         (end-index
          (if (equal n 0)
              0
            (- n 1))))
    (verina-advanced-59-check
     start-index
     end-index
     cleaned)))

(defun verina-advanced-59-reverse-list (characters)
  (reverse characters))

(defun verina-advanced-59-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

(defun verina-advanced-59-palindrome-ignore-nonalnum-postcond
    (s result)
  (let* ((cleaned
          (verina-advanced-59-cleaned s))
         (forward cleaned)
         (backward
          (verina-advanced-59-reverse-list cleaned)))
    (and
     (verina-advanced-59-string-p s)
     (verina-advanced-59-bool-p result)
     (if (equal result t)
         (equal forward backward)
       (not (equal forward backward))))))

;; This predicate is the unproved final correctness proposition. Its
;; conclusion applies the complete postcondition to the exact executable
;; result.

(defun
    verina-advanced-59-palindrome-ignore-nonalnum-spec-satisfied-statement
    (s)
  (implies
   (and
    (verina-advanced-59-string-p s)
    (verina-advanced-59-palindrome-ignore-nonalnum-precond s))
   (verina-advanced-59-palindrome-ignore-nonalnum-postcond
    s
    (verina-advanced-59-palindrome-ignore-nonalnum s))))

(value-triple :itpeval-statement-checked)
:q
