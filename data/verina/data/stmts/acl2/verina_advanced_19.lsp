;; Statement-only formalization of VERINA corpus artifact verina_advanced_19,
;; "isCleanPalindrome": ASCII letters in a Unicode string are lowercased,
;; nonletters are removed, and the resulting character list is tested for
;; palindromicity with its Boolean correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves characters beyond ACL2's host character set.

(defun verina-advanced-19-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-19-string-p (s)
  (if (consp s)
      (and
       (verina-advanced-19-unicode-scalar-p (car s))
       (verina-advanced-19-string-p (cdr s)))
    (equal s nil)))

(defun verina-advanced-19-is-upper-alpha (c)
  (and
   (<= 65 c)
   (<= c 90)))

(defun verina-advanced-19-is-lower-alpha (c)
  (and
   (<= 97 c)
   (<= c 122)))

(defun verina-advanced-19-is-alpha (c)
  (or
   (verina-advanced-19-is-upper-alpha c)
   (verina-advanced-19-is-lower-alpha c)))

(defun verina-advanced-19-to-lower (c)
  (if (verina-advanced-19-is-upper-alpha c)
      (+ c 32)
    c))

;; Option Char is represented by :none or the tagged pair (:some . code).

(defun verina-advanced-19-normalize-char (c)
  (if (verina-advanced-19-is-alpha c)
      (cons :some (verina-advanced-19-to-lower c))
    :none))

;; This right-recursive definition is the source foldr over String.toList.

(defun verina-advanced-19-normalize-string (s)
  (if (consp s)
      (let* ((normalized-char
              (verina-advanced-19-normalize-char (car s)))
             (normalized-rest
              (verina-advanced-19-normalize-string (cdr s))))
        (if (equal normalized-char :none)
            normalized-rest
          (cons (cdr normalized-char) normalized-rest)))
    nil))

(defun verina-advanced-19-is-clean-palindrome-precond (s)
  (declare (ignore s))
  t)

(defun verina-advanced-19-reverse-list (xs)
  (reverse xs))

;; The source proof-valued precondition argument is erased; the final
;; statement supplies the corresponding precondition predicate explicitly.

(defun verina-advanced-19-is-clean-palindrome (s)
  (let ((norm
         (verina-advanced-19-normalize-string s)))
    (equal
     norm
     (verina-advanced-19-reverse-list norm))))

(defun verina-advanced-19-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

(defun verina-advanced-19-is-clean-palindrome-postcond
    (s result)
  (let ((norm
         (verina-advanced-19-normalize-string s)))
    (and
     (verina-advanced-19-string-p s)
     (verina-advanced-19-bool-p result)
     (implies
      (equal result t)
      (equal
       norm
       (verina-advanced-19-reverse-list norm)))
     (implies
      (equal result nil)
      (not
       (equal
        norm
        (verina-advanced-19-reverse-list norm)))))))

(defun
    verina-advanced-19-is-clean-palindrome-spec-satisfied-statement
    (s)
  (implies
   (and
    (verina-advanced-19-string-p s)
    (verina-advanced-19-is-clean-palindrome-precond s))
   (verina-advanced-19-is-clean-palindrome-postcond
    s
    (verina-advanced-19-is-clean-palindrome s))))

(value-triple :itpeval-statement-checked)
:q
