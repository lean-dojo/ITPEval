;; Statement-only formalization of VERINA corpus artifact verina_advanced_21,
;; "isPalindrome": two deterministic checks decide whether a Unicode string
;; reads identically forward and backward, together with the Boolean
;; correctness contract. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves characters beyond ACL2's host character set.

(defun verina-advanced-21-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-21-string-p (s)
  (if (consp s)
      (and
       (verina-advanced-21-unicode-scalar-p (car s))
       (verina-advanced-21-string-p (cdr s)))
    (equal s nil)))

(defun verina-advanced-21-is-palindrome-precond (s)
  (declare (ignore s))
  t)

;; Option Char is represented by :none or the tagged pair (:some . code).

(defun verina-advanced-21-nth-option (index chars)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      :none
    (if (consp chars)
        (if (zp index)
            (cons :some (car chars))
          (verina-advanced-21-nth-option
           (- index 1)
           (cdr chars)))
      :none)))

;; This is the source's inward-moving checkIndices recursion, including its
;; optional list accesses and truncated natural-number subtraction.

(defun verina-advanced-21-check-indices (left right chars)
  (declare (xargs :measure (nfix right)))
  (if (or
       (not (natp left))
       (not (natp right)))
      nil
    (if (<= right left)
        t
      (let ((left-option
             (verina-advanced-21-nth-option left chars))
            (right-option
             (verina-advanced-21-nth-option right chars)))
        (if (and
             (consp left-option)
             (equal (car left-option) :some)
             (consp right-option)
             (equal (car right-option) :some))
            (if (equal (cdr left-option)
                       (cdr right-option))
                (verina-advanced-21-check-indices
                 (+ left 1)
                 (- right 1)
                 chars)
              nil)
          nil)))))

;; This tail recursion is the source's local reverseList helper.

(defun verina-advanced-21-reverse-list-aux (acc xs)
  (if (consp xs)
      (verina-advanced-21-reverse-list-aux
       (cons (car xs) acc)
       (cdr xs))
    acc))

(defun verina-advanced-21-reverse-list (xs)
  (verina-advanced-21-reverse-list-aux nil xs))

;; The source proof-valued precondition argument is erased; the final
;; statement supplies the corresponding precondition predicate explicitly.

(defun verina-advanced-21-is-palindrome (s)
  (let ((length (len s)))
    (if (<= length 1)
        t
      (let ((approach1
             (verina-advanced-21-check-indices
              0
              (- length 1)
              s))
            (approach2
             (equal
              s
              (verina-advanced-21-reverse-list s))))
        (and approach1 approach2)))))

(defun verina-advanced-21-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

(defun verina-advanced-21-is-palindrome-postcond
    (s result)
  (let ((reversed
         (verina-advanced-21-reverse-list s)))
    (and
     (verina-advanced-21-string-p s)
     (verina-advanced-21-bool-p result)
     (implies
      (equal result t)
      (equal s reversed))
     (implies
      (equal result nil)
      (and
       (not (equal s nil))
       (not (equal s reversed)))))))

(defun
    verina-advanced-21-is-palindrome-spec-satisfied-statement
    (s)
  (implies
   (and
    (verina-advanced-21-string-p s)
    (verina-advanced-21-is-palindrome-precond s))
   (verina-advanced-21-is-palindrome-postcond
    s
    (verina-advanced-21-is-palindrome s))))

(value-triple :itpeval-statement-checked)
:q
