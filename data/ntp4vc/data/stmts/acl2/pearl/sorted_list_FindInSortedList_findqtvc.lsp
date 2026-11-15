;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sorted_list_FindInSortedList_findqtvc: correctness of Boolean
;; membership search in a sorted integer list. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integer
;; list domain.

(defun ntp4vc-sorted-list-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (ntp4vc-sorted-list-integer-list-p (cdr xs)))
    (equal xs nil)))

;; This pairwise definition is the finite-list rendering of source sortedness:
;; every head is at most every element of its tail, and the tail is sorted.

(defun ntp4vc-sorted-list-all-at-least-p (lower xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (<= lower (car xs))
       (ntp4vc-sorted-list-all-at-least-p lower (cdr xs)))
    (equal xs nil)))

(defun ntp4vc-sorted-list-sorted-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (ntp4vc-sorted-list-all-at-least-p (car xs) (cdr xs))
       (ntp4vc-sorted-list-sorted-p (cdr xs)))
    (equal xs nil)))

;; This preserves the nested match in the generated verification condition:
;; matching the same nonempty list again returns exactly its tail.

(defun ntp4vc-sorted-list-tail-match-p (whole expected-tail)
  (if (consp whole)
      (equal (cdr whole) expected-tail)
    nil))

(defun ntp4vc-sorted-list-head-tail-obligation-p (list x)
  (if (consp list)
      (let ((y (car list))
            (rest (cdr list)))
        (implies
         (not (equal x y))
         (implies
          (< y x)
          (and
           (ntp4vc-sorted-list-tail-match-p list rest)
           (ntp4vc-sorted-list-sorted-p rest)))))
    t))

(defun ntp4vc-sorted-list-member-bool (x list)
  (if (member-equal x list) t nil))

;; This is the source match expression that determines the Boolean result.

(defun ntp4vc-sorted-list-result-equation-p (list x result)
  (if (consp list)
      (let ((y (car list))
            (rest (cdr list)))
        (if (equal x y)
            (equal result t)
          (if (< y x)
              (equal
               result
               (ntp4vc-sorted-list-member-bool x rest))
            (equal result nil))))
    (equal result nil)))

;; RESULT retains its internal universal quantifier over the complete Boolean
;; domain. Any result satisfying the source match equation is true exactly
;; when X occurs in LIST.

(defun-sk ntp4vc-sorted-list-all-results-correct-p (list x)
  (forall (result)
    (implies
     (booleanp result)
     (implies
      (ntp4vc-sorted-list-result-equation-p list x result)
      (iff
       (equal result t)
       (member-equal x list))))))

(defun
    ntp4vc-pearl-sorted-list-findinsortedlist-findqtvc-statement
    (list x)
  (implies
   (and
    (ntp4vc-sorted-list-integer-list-p list)
    (integerp x)
    (ntp4vc-sorted-list-sorted-p list))
   (and
    (ntp4vc-sorted-list-head-tail-obligation-p list x)
    (ntp4vc-sorted-list-all-results-correct-p list x))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
