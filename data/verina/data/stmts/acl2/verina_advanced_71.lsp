;; Statement-only formalization of VERINA corpus artifact verina_advanced_71,
;; "shortestBeautifulSubstring": a deterministic binary-string program selects
;; the shortest substring with exactly k ones, breaking ties lexicographically,
;; together with its full correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-advanced-71-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-71-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-71-unicode-scalar-p (car s))
       (verina-advanced-71-string-p (cdr s)))
    (equal s nil)))

;; This accumulator recursion is countOnes: List.foldl increments exactly for
;; the Unicode scalar value of '1'.

(defun verina-advanced-71-count-ones-fold
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-71-count-ones-fold
       (cdr remaining)
       (if (equal (car remaining) 49)
           (+ accumulator 1)
         accumulator))
    accumulator))

(defun verina-advanced-71-count-ones (characters)
  (verina-advanced-71-count-ones-fold characters 0))

;; The source precondition is String.toList.all over the two binary characters.
;; Its k argument is present but computationally unused, exactly as in Lean.

(defun verina-advanced-71-binary-characters-p (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (and
       (or
        (equal (car characters) 48)
        (equal (car characters) 49))
       (verina-advanced-71-binary-characters-p
        (cdr characters)))
    (equal characters nil)))

(defun verina-advanced-71-shortest-beautiful-substring-precond
    (s k)
  (declare (ignore k))
  (verina-advanced-71-binary-characters-p s))

;; Under the canonical representation, String.mk and List.asString preserve
;; the represented scalar sequence exactly.

(defun verina-advanced-71-list-to-string (characters)
  characters)

;; UTF-8 string order on valid scalar sequences is the lexicographic scalar
;; order below. This is the source isLexSmaller helper.

(defun verina-advanced-71-lex-smaller-p (a b)
  (declare
   (xargs
    :measure
    (+ (acl2-count a) (acl2-count b))))
  (if (consp a)
      (if (consp b)
          (if (< (car a) (car b))
              t
            (if (< (car b) (car a))
                nil
              (verina-advanced-71-lex-smaller-p
               (cdr a)
               (cdr b))))
        nil)
    (if (consp b) t nil)))

(defun verina-advanced-71-is-lex-smaller (a b)
  (verina-advanced-71-lex-smaller-p
   (verina-advanced-71-list-to-string a)
   (verina-advanced-71-list-to-string b)))

;; For a nonempty suffix, this constructs its prefixes in lengths 1, 2, ... .
;; Consequently all-substrings appends exactly the source List.range/flatMap
;; sequence: increasing start position, then increasing positive length.

(defun verina-advanced-71-prepend-to-each
    (char-code lists)
  (declare (xargs :measure (acl2-count lists)))
  (if (consp lists)
      (cons
       (cons char-code (car lists))
       (verina-advanced-71-prepend-to-each
        char-code
        (cdr lists)))
    nil))

(defun verina-advanced-71-nonempty-prefixes (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (cons
       (list (car characters))
       (verina-advanced-71-prepend-to-each
        (car characters)
        (verina-advanced-71-nonempty-prefixes
         (cdr characters))))
    nil))

(defun verina-advanced-71-all-substrings (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (append
       (verina-advanced-71-nonempty-prefixes characters)
       (verina-advanced-71-all-substrings
        (cdr characters)))
    nil))

(defun verina-advanced-71-filter-by-count
    (substrings k)
  (declare (xargs :measure (acl2-count substrings)))
  (if (consp substrings)
      (if (equal
           (verina-advanced-71-count-ones
            (car substrings))
           k)
          (cons
           (car substrings)
           (verina-advanced-71-filter-by-count
            (cdr substrings)
            k))
        (verina-advanced-71-filter-by-count
         (cdr substrings)
         k))
    nil))

;; This is the local compare function: strictly shorter first, followed by
;; strictly lexicographically smaller when lengths agree.

(defun verina-advanced-71-better-candidate-p (a b)
  (or
   (< (len a) (len b))
   (and
    (equal (len a) (len b))
    (verina-advanced-71-is-lex-smaller a b))))

;; The option is represented as nil for none and (:some . substring) for some.
;; The recursion is precisely candidates.foldl, including retention of the
;; earlier best candidate whenever compare is false.

(defun verina-advanced-71-best-fold
    (candidates best-option)
  (declare (xargs :measure (acl2-count candidates)))
  (if (consp candidates)
      (let ((current (car candidates)))
        (verina-advanced-71-best-fold
         (cdr candidates)
         (if (consp best-option)
             (if
                 (verina-advanced-71-better-candidate-p
                  current
                  (cdr best-option))
                 (cons :some current)
               best-option)
           (cons :some current))))
    best-option))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. All source helper calls, filtering, folding, and the none/empty
;; fallback remain explicit.

(defun verina-advanced-71-shortest-beautiful-substring
    (s k)
  (let* ((characters s)
         (candidates
          (verina-advanced-71-filter-by-count
           (verina-advanced-71-all-substrings characters)
           k))
         (best
          (verina-advanced-71-best-fold candidates nil)))
    (if (consp best)
        (verina-advanced-71-list-to-string (cdr best))
      nil)))

;; The postcondition has a distinct substring enumeration. For every source
;; start index it includes lengths 0 through the remaining length, so each
;; nonempty suffix contributes nil followed by all of its nonempty prefixes.

(defun verina-advanced-71-post-all-substrings (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (append
       (cons
        nil
        (verina-advanced-71-nonempty-prefixes characters))
       (verina-advanced-71-post-all-substrings
        (cdr characters)))
    nil))

;; This recursive map preserves the source beautiful.map List.asString,
;; including list order and duplicates.

(defun verina-advanced-71-map-list-to-string (substrings)
  (declare (xargs :measure (acl2-count substrings)))
  (if (consp substrings)
      (cons
       (verina-advanced-71-list-to-string
        (car substrings))
       (verina-advanced-71-map-list-to-string
        (cdr substrings)))
    nil))

(defun verina-advanced-71-filter-nonempty-strings (strings)
  (declare (xargs :measure (acl2-count strings)))
  (if (consp strings)
      (if (consp (car strings))
          (cons
           (car strings)
           (verina-advanced-71-filter-nonempty-strings
            (cdr strings)))
        (verina-advanced-71-filter-nonempty-strings
         (cdr strings)))
    nil))

(defun verina-advanced-71-targets (s k)
  (verina-advanced-71-filter-nonempty-strings
   (verina-advanced-71-map-list-to-string
    (verina-advanced-71-filter-by-count
     (verina-advanced-71-post-all-substrings s)
     k))))

(defun verina-advanced-71-target-member-p
    (result targets)
  (declare (xargs :measure (acl2-count targets)))
  (if (consp targets)
      (or
       (equal result (car targets))
       (verina-advanced-71-target-member-p
        result
        (cdr targets)))
    nil))

(defun verina-advanced-71-lex-at-most-p (a b)
  (or
   (equal a b)
   (verina-advanced-71-lex-smaller-p a b)))

;; This is the postcondition's universal quantifier over target membership.

(defun verina-advanced-71-minimal-against-all-targets-p
    (result targets)
  (declare (xargs :measure (acl2-count targets)))
  (if (consp targets)
      (and
       (or
        (< (len result) (len (car targets)))
        (and
         (equal (len result) (len (car targets)))
         (verina-advanced-71-lex-at-most-p
          result
          (car targets))))
       (verina-advanced-71-minimal-against-all-targets-p
        result
        (cdr targets)))
    t))

(defun verina-advanced-71-shortest-beautiful-substring-postcond
    (s k result)
  (let ((targets (verina-advanced-71-targets s k)))
    (and
     (verina-advanced-71-string-p s)
     (natp k)
     (verina-advanced-71-string-p result)
     (or
      (and
       (equal result nil)
       (equal targets nil))
      (and
       (verina-advanced-71-target-member-p result targets)
       (verina-advanced-71-minimal-against-all-targets-p
        result
        targets))))))

;; This predicate is the unproved final correctness proposition. Its
;; antecedent preserves both typed source binders and the complete precondition;
;; its conclusion applies the full postcondition to the exact executable result.

(defun
    verina-advanced-71-shortest-beautiful-substring-spec-satisfied-statement
    (s k)
  (implies
   (and
    (verina-advanced-71-string-p s)
    (natp k)
    (verina-advanced-71-shortest-beautiful-substring-precond
     s
     k))
   (verina-advanced-71-shortest-beautiful-substring-postcond
    s
    k
    (verina-advanced-71-shortest-beautiful-substring s k))))

(value-triple :itpeval-statement-checked)
:q
