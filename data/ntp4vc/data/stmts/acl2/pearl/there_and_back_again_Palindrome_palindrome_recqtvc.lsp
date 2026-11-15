;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/there_and_back_again_Palindrome_palindrome_recqtvc: the recursive
;; palindrome verification condition relating prefix decompositions,
;; palindrome indices, equality testing, and exceptional mismatch witnesses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type and its equality predicate.

(defstub tba-pal-element-p (value) t)
(defstub tba-pal-default-element () t)
(defstub tba-pal-eq-p (left right) t)

(defun tba-pal-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (tba-pal-element-p (car xs))
       (tba-pal-list-p (cdr xs)))
    (equal xs nil)))

;; Why3 list lookup returns an option.  The tagged ACL2 representation keeps
;; an out-of-range lookup distinct from every possible source element.

(defun tba-pal-nth-option (xs index)
  (if (and
       (integerp index)
       (<= 0 index)
       (< index (len xs)))
      (cons :some (nth index xs))
    :none))

;; This is the source predicate pal: every valid index below N agrees with its
;; reflected index.  Integer typing remains explicit under ACL2 quantification.

(defun-sk tba-pal-p (xs n)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
       (equal
       (tba-pal-nth-option xs index)
       (tba-pal-nth-option xs (- (- n 1) index)))))))

;; The source equality predicate is specified extensionally on the abstract
;; carrier.  Booleanization records ACL2 truth values without restricting the
;; carrier's structural equality.

(defun tba-pal-eq-spec-at-p (left right)
  (equal
   (if (tba-pal-eq-p left right) t nil)
   (equal left right)))

(defun-sk tba-pal-eq-spec-p ()
  (forall (left right)
    (implies
     (and
      (tba-pal-element-p left)
      (tba-pal-element-p right))
     (tba-pal-eq-spec-at-p left right))))

;; The existential prefix remains internal: WHOLE is PREFIX ++ SUFFIX and the
;; prefix has exactly the requested length.

(defun-sk tba-pal-prefix-split-p (whole prefix-length suffix)
  (exists (prefix)
    (and
     (tba-pal-list-p prefix)
     (equal (len prefix) prefix-length)
     (equal whole (append prefix suffix)))))

;; This is the exceptional postcondition from the Why3 procedure.

(defun-sk tba-pal-mismatch-p (xs n)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index n)
     (not
      (equal
       (tba-pal-nth-option xs index)
       (tba-pal-nth-option xs (- (- n 1) index)))))))

(defun tba-pal-normal-post-p (whole prefix-length suffix)
  (and
   (tba-pal-prefix-split-p whole prefix-length suffix)
   (tba-pal-p whole prefix-length)))

;; For every possible recursive result O1 satisfying the recursive normal
;; postconditions, preserve the source pattern match and equality-test branch.

(defun tba-pal-recursive-result-p
    (whole whole-length head recursive-result)
  (if (consp recursive-result)
      (let ((recursive-head (car recursive-result))
            (recursive-tail (cdr recursive-result)))
        (implies
         (tba-pal-eq-spec-at-p head recursive-head)
         (if (tba-pal-eq-p head recursive-head)
             (tba-pal-normal-post-p
              whole whole-length recursive-tail)
           (tba-pal-mismatch-p whole whole-length))))
    nil))

(defun-sk tba-pal-all-recursive-results-p
    (whole whole-length head tail inner-length)
  (forall (recursive-result)
    (implies
     (tba-pal-list-p recursive-result)
     (implies
      (and
       (tba-pal-prefix-split-p
        tail inner-length recursive-result)
       (tba-pal-p tail inner-length))
      (tba-pal-recursive-result-p
       whole
       whole-length
       head
       recursive-result)))))

;; This is the Cons/Cons recursive case.  It retains the recursive-call
;; decrease condition, all normal recursive results, and propagation of every
;; exceptional mismatch witness.

(defun tba-pal-deep-branch-p (y x)
  (if (consp x)
      (let ((head (car x))
            (tail (cdr x))
            (inner-y (cdr (cdr y))))
        (and
         (equal (cdr x) tail)
         (<= (len inner-y) (len tail))
         (tba-pal-all-recursive-results-p
          x (len y) head tail (len inner-y))
         (implies
          (tba-pal-mismatch-p tail (len inner-y))
          (tba-pal-mismatch-p x (len y)))))
    nil))

;; These nested tests are definitionally the source matches on Y, its tail,
;; and X.  Proper-list typing in the statement makes each non-cons case Nil.

(defun tba-pal-vc-body-p (y x)
  (if (consp y)
      (if (consp (cdr y))
          (tba-pal-deep-branch-p y x)
        (if (consp x)
            (tba-pal-normal-post-p x (len y) (cdr x))
          nil))
    (tba-pal-normal-post-p x (len y) x)))

(defun
  ntp4vc-pearl-there-and-back-again-palindrome-palindrome-recqtvc-statement
  (y x)
  (implies
   (and
    (tba-pal-element-p (tba-pal-default-element))
    (tba-pal-eq-spec-p)
    (tba-pal-list-p y)
    (tba-pal-list-p x)
    (<= (len y) (len x)))
   (tba-pal-vc-body-p y x)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
