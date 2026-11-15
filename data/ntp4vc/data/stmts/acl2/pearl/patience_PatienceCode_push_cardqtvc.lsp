;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/patience_PatienceCode_push_cardqtvc: the patience-solitaire
;; push-card verification condition, preserving nonempty integer stacks
;; through recursive search and card placement. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 lists are represented by ACL2 proper lists, and the source card type
;; is mathematical integer. These predicates retain the complete, unbounded
;; source domains.

(defun ppc-integer-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (integerp (car xs))
       (ppc-integer-list-p (cdr xs)))
    (equal xs nil)))

(defun ppc-stack-list-p (stacks)
  (declare (xargs :measure (acl2-count stacks)))
  (if (consp stacks)
      (and
       (ppc-integer-list-p (car stacks))
       (ppc-stack-list-p (cdr stacks)))
    (equal stacks nil)))

;; This is the source recursive predicate WF_STACKS: every stack in the outer
;; list is nonempty. Element and proper-list typing are supplied separately by
;; PPC-STACK-LIST-P, as they are by the Why3 type system.

(defun ppc-wf-stacks-p (stacks)
  (declare (xargs :measure (acl2-count stacks)))
  (if (consp stacks)
      (and
       (consp (car stacks))
       (ppc-wf-stacks-p (cdr stacks)))
    (equal stacks nil)))

;; This is list.RevAppend.rev_append, used by both return branches of the
;; source function.

(defun ppc-rev-append (front back)
  (declare (xargs :measure (acl2-count front)))
  (if (consp front)
      (ppc-rev-append
       (cdr front)
       (cons (car front) back))
    back))

;; The first theorem conjunct records the recursive-call side conditions in
;; the branch where C is greater than the current stack's top card.

(defun ppc-recursive-side-condition-p
    (stacks1 acc c)
  (if (consp stacks1)
      (let ((stack (car stacks1))
            (remaining-stacks (cdr stacks1)))
        (if (consp stack)
            (let ((top-card (car stack)))
              (implies
               (not (<= c top-card))
               (and
                (equal
                 (cdr stacks1)
                 remaining-stacks)
                (ppc-wf-stacks-p
                 remaining-stacks)
                (ppc-wf-stacks-p
                 (cons stack acc)))))
          nil))
    t))

;; This is the exact branch-dependent premise describing a possible RESULT
;; returned by push_card.

(defun ppc-result-premise-p
    (stacks1 acc c result)
  (if (consp stacks1)
      (let ((stack (car stacks1))
            (remaining-stacks (cdr stacks1)))
        (if (consp stack)
            (let ((top-card (car stack)))
              (if (<= c top-card)
                  (equal
                   result
                   (ppc-rev-append
                    (cons (cons c stack) acc)
                    remaining-stacks))
                (ppc-wf-stacks-p result)))
          nil))
    (equal
     result
     (ppc-rev-append
      (cons (list c) acc)
      nil))))

;; RESULT retains its source universal quantifier over every integer stack
;; list, inside the conclusion of the verification condition.

(defun-sk ppc-all-results-well-formed-p
    (stacks1 acc c)
  (forall (result)
    (implies
     (ppc-stack-list-p result)
     (implies
      (ppc-result-premise-p
       stacks1 acc c result)
      (ppc-wf-stacks-p result)))))

(defun-sk
  ntp4vc-pearl-patience-patiencecode-push-cardqtvc-statement
  ()
  (forall (stacks1 acc c)
    (implies
     (and
      (ppc-stack-list-p stacks1)
      (ppc-stack-list-p acc)
      (integerp c)
      (ppc-wf-stacks-p stacks1)
      (ppc-wf-stacks-p acc))
     (and
      (ppc-recursive-side-condition-p
       stacks1 acc c)
      (ppc-all-results-well-formed-p
       stacks1 acc c)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
