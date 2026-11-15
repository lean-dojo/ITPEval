;; Statement-only formalization of VERINA corpus artifact verina_advanced_6,
;; "allVowels": a deterministic case-insensitive Unicode-string scan checks
;; whether all five English vowels occur, together with its Boolean correctness
;; contract. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves characters beyond ACL2's host character set.

(defun verina-advanced-6-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-6-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-6-unicode-scalar-p (car s))
       (verina-advanced-6-string-p (cdr s)))
    (equal s nil)))

;; This is the source toLower helper: precisely the ASCII uppercase range is
;; shifted to the corresponding lowercase Unicode scalar value.

(defun verina-advanced-6-to-lower (c)
  (if (and
       (<= 65 c)
       (<= c 90))
      (+ c 32)
    c))

;; Under the canonical representation, String.data is the represented list,
;; so this recursive map is exactly normalize_str.

(defun verina-advanced-6-normalize-str (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (cons
       (verina-advanced-6-to-lower (car s))
       (verina-advanced-6-normalize-str (cdr s)))
    nil))

;; The source precondition is True. The String binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-6-all-vowels-precond (s)
  (declare (ignore s))
  t)

(defun verina-advanced-6-contains-code-p (code chars)
  (declare (xargs :measure (acl2-count chars)))
  (if (consp chars)
      (or
       (equal code (car chars))
       (verina-advanced-6-contains-code-p
        code
        (cdr chars)))
    nil))

;; This is List.all over the source vowelSet. The codes are the Unicode scalar
;; values for a, e, i, o, and u, in the same order as the Lean list.

(defun verina-advanced-6-all-contained-p (vowels chars)
  (declare (xargs :measure (acl2-count vowels)))
  (if (consp vowels)
      (and
       (verina-advanced-6-contains-code-p
        (car vowels)
        chars)
       (verina-advanced-6-all-contained-p
        (cdr vowels)
        chars))
    t))

;; The proof-valued True precondition argument is computationally irrelevant;
;; the final statement supplies the corresponding predicate explicitly.

(defun verina-advanced-6-all-vowels (s)
  (let ((chars
         (verina-advanced-6-normalize-str s))
        (vowel-set
         (list 97 101 105 111 117)))
    (verina-advanced-6-all-contained-p
     vowel-set
     chars)))

(defun verina-advanced-6-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; Equality of ACL2's t/nil Boolean values is the source postcondition's
;; propositional equivalence between result and the independent List.all test.

(defun verina-advanced-6-all-vowels-postcond (s result)
  (let ((chars
         (verina-advanced-6-normalize-str s))
        (vowel-set
         (list 97 101 105 111 117)))
    (and
     (verina-advanced-6-string-p s)
     (verina-advanced-6-bool-p result)
     (equal
      result
      (verina-advanced-6-all-contained-p
       vowel-set
       chars)))))

;; This predicate is the unproved final correctness proposition connecting the
;; complete precondition and postcondition to the exact executable result.

(defun
    verina-advanced-6-all-vowels-spec-satisfied-statement
    (s)
  (implies
   (and
    (verina-advanced-6-string-p s)
    (verina-advanced-6-all-vowels-precond s))
   (verina-advanced-6-all-vowels-postcond
    s
    (verina-advanced-6-all-vowels s))))

(value-triple :itpeval-statement-checked)
:q
