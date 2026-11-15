;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/there_and_back_again_Palindrome_palindromeqtvc: the palindrome
;; wrapper verification condition over reflected integer indices, normal
;; recursive returns, and exceptional mismatch witnesses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and its equality predicate.

(defstub tba-palq-element-p (value) t)
(defstub tba-palq-default-element () t)
(defstub tba-palq-eq-p (left right) t)

(defun tba-palq-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (tba-palq-element-p (car xs))
       (tba-palq-list-p (cdr xs)))
    (equal xs nil)))

;; Why3 list lookup returns an option. The tagged ACL2 representation keeps
;; an out-of-range lookup distinct from every possible source element.

(defun tba-palq-nth-option (xs index)
  (if (and
       (integerp index)
       (<= 0 index)
       (< index (len xs)))
      (cons :some (nth index xs))
    :none))

;; This is the source predicate pal: every integer index in [0,N) agrees with
;; its reflected index.

(defun-sk tba-palq-pal-p (xs n)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
      (equal
       (tba-palq-nth-option xs index)
       (tba-palq-nth-option xs (- (- n 1) index)))))))

;; The source equality predicate is specified extensionally on the abstract
;; carrier.

(defun tba-palq-eq-spec-at-p (left right)
  (equal
   (if (tba-palq-eq-p left right) t nil)
   (equal left right)))

(defun-sk tba-palq-eq-spec-p ()
  (forall (left right)
    (implies
     (and
      (tba-palq-element-p left)
      (tba-palq-element-p right))
     (tba-palq-eq-spec-at-p left right))))

;; The existential prefix witness remains internal: WHOLE is PREFIX ++ SUFFIX
;; and PREFIX has the requested length.

(defun-sk tba-palq-prefix-split-p (whole prefix-length suffix)
  (exists (prefix)
    (and
     (tba-palq-list-p prefix)
     (equal (len prefix) prefix-length)
     (equal whole (append prefix suffix)))))

;; Every possible normal recursive result retains its source universal scope.
;; The palindrome premise and conclusion are deliberately both present,
;; exactly as in the generated verification condition.

(defun-sk tba-palq-all-normal-results-p (x)
  (forall (suffix)
    (implies
     (tba-palq-list-p suffix)
     (implies
      (and
       (tba-palq-prefix-split-p x (len x) suffix)
       (tba-palq-pal-p x (len x)))
      (tba-palq-pal-p x (len x))))))

;; This is the exceptional mismatch witness from the source statement.

(defun-sk tba-palq-mismatch-p (x n)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index n)
     (not
      (equal
       (tba-palq-nth-option x index)
       (tba-palq-nth-option x (- (- n 1) index)))))))

(defun
  ntp4vc-pearl-there-and-back-again-palindrome-palindromeqtvc-statement
  (x)
  (implies
   (and
    (tba-palq-element-p (tba-palq-default-element))
    (tba-palq-eq-spec-p)
    (tba-palq-list-p x))
   (and
    (<= (len x) (len x))
    (tba-palq-all-normal-results-p x)
    (implies
     (tba-palq-mismatch-p x (len x))
     (not (tba-palq-pal-p x (len x)))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
