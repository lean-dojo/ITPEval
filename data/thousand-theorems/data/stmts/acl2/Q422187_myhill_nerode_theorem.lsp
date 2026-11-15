;; Statement-only formalization of thousand-theorems corpus artifact Q422187,
;; "Myhill–Nerode theorem": over an arbitrary alphabet, a language is
;; recognized by a finite deterministic automaton if and only if its set of
;; left quotients is finite. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame unary function objects represent the arbitrary alphabet carrier and
;; language predicate. Words are all finite true lists over that carrier; no
;; finite-alphabet restriction is imposed.

(defun q422187-alphabet-member-p (alphabet symbol)
  (if (apply$ alphabet (list symbol)) t nil))

(defun q422187-language-member-p (language word)
  (if (apply$ language (list word)) t nil))

(defun q422187-word-p (alphabet word)
  (if (consp word)
      (and
       (q422187-alphabet-member-p alphabet (car word))
       (q422187-word-p alphabet (cdr word)))
    (equal word nil)))

;; Two prefixes have the same left quotient exactly when every suffix belongs
;; to one quotient iff it belongs to the other.

(defun-sk q422187-left-quotient-equal-p
    (alphabet language left-prefix right-prefix)
  (forall (suffix)
    (implies
     (q422187-word-p alphabet suffix)
     (iff
      (q422187-language-member-p
       language (append left-prefix suffix))
      (q422187-language-member-p
       language (append right-prefix suffix))))))

(defun q422187-representative-list-p
    (alphabet representatives)
  (if (consp representatives)
      (and
       (q422187-word-p alphabet (car representatives))
       (q422187-representative-list-p
        alphabet (cdr representatives)))
    (equal representatives nil)))

(defun-sk q422187-word-has-representative-p
    (alphabet language representatives word)
  (exists (representative)
    (and
     (member-equal representative representatives)
     (q422187-left-quotient-equal-p
      alphabet language word representative))))

(defun-sk q422187-representatives-cover-p
    (alphabet language representatives)
  (forall (word)
    (implies
     (q422187-word-p alphabet word)
     (q422187-word-has-representative-p
      alphabet language representatives word))))

(defun-sk q422187-finite-left-quotient-range-p
    (alphabet language)
  (exists (representatives)
    (and
     (true-listp representatives)
     (no-duplicatesp-equal representatives)
     (q422187-representative-list-p
      alphabet representatives)
     (q422187-representatives-cover-p
      alphabet language representatives))))

;; A finite DFA is represented extensionally by a duplicate-free finite state
;; list, a start state, a finite accepting subset, and a tame binary transition
;; function object. The transition closure condition ranges over every symbol
;; in the arbitrary alphabet.

(defun q422187-transition-value
    (transition current-state symbol)
  (apply$ transition (list current-state symbol)))

(defun-sk q422187-transition-closed-p
    (alphabet states transition)
  (forall (current-state symbol)
    (implies
     (and
      (member-equal current-state states)
      (q422187-alphabet-member-p alphabet symbol))
     (member-equal
      (q422187-transition-value
       transition current-state symbol)
      states))))

(defun q422187-subset-p (left right)
  (if (consp left)
      (and
       (member-equal (car left) right)
       (q422187-subset-p (cdr left) right))
    (equal left nil)))

(defun q422187-run (transition current-state word)
  (if (consp word)
      (q422187-run
       transition
       (q422187-transition-value
        transition current-state (car word))
       (cdr word))
    current-state))

(defun-sk q422187-recognizer-correct-p
    (alphabet language transition start accepting)
  (forall (word)
    (implies
     (q422187-word-p alphabet word)
     (iff
      (member-equal
       (q422187-run transition start word)
       accepting)
      (q422187-language-member-p language word)))))

(defun q422187-finite-dfa-recognizes-p
    (alphabet language states start accepting transition)
  (and
   (true-listp states)
   (no-duplicatesp-equal states)
   (member-equal start states)
   (true-listp accepting)
   (no-duplicatesp-equal accepting)
   (q422187-subset-p accepting states)
   (tamep-functionp transition)
   (q422187-transition-closed-p
    alphabet states transition)
   (q422187-recognizer-correct-p
    alphabet language transition start accepting)))

(defun-sk q422187-regular-language-p (alphabet language)
  (exists (states start accepting transition)
    (q422187-finite-dfa-recognizes-p
     alphabet language states start accepting transition)))

(defun thousand-theorems-q422187-myhill-nerode-theorem-statement
    (alphabet language)
  (implies
   (and
    (tamep-functionp alphabet)
    (tamep-functionp language))
   (iff
    (q422187-regular-language-p alphabet language)
    (q422187-finite-left-quotient-range-p
     alphabet language))))

(value-triple :itpeval-statement-checked)
:q
