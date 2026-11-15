;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/cursor_examples_TestListCursor_list_sumqtvc: the list-cursor sum
;; verification condition, including empty initialization, prefix permission,
;; strict cursor progress, and preservation of the accumulated sum. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source cursor type is abstract and inhabited.  These conservative
;; symbols represent its carrier predicate and its two list-valued projections.
;; Their type laws and nonemptiness are explicit in the statement.

(defstub list-sum-cursor-p (cursor) t)
(defstub list-sum-visited (cursor) t)
(defstub list-sum-collection (cursor) t)

(defun list-sum-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (list-sum-integer-list-p (cdr xs)))))

(defun-sk list-sum-cursor-domain-nonempty-p ()
  (exists (cursor)
    (list-sum-cursor-p cursor)))

(defun-sk list-sum-cursor-projections-typed-p ()
  (forall (cursor)
    (implies
     (list-sum-cursor-p cursor)
     (and
      (list-sum-integer-list-p
       (list-sum-visited cursor))
      (list-sum-integer-list-p
       (list-sum-collection cursor))))))

(defun list-sum-cursor-interface-p ()
  (and
   (list-sum-cursor-domain-nonempty-p)
   (list-sum-cursor-projections-typed-p)))

;; On proper lists, this recursive relation is equivalent to the source's
;; length bound together with pointwise equality at every visited index.

(defun list-sum-prefix-p (prefix whole)
  (if (consp prefix)
      (and
       (consp whole)
       (equal (car prefix) (car whole))
       (list-sum-prefix-p (cdr prefix) (cdr whole)))
    (equal prefix nil)))

(defun list-sum-permitted-p (cursor)
  (and
   (<=
    (len (list-sum-visited cursor))
    (len (list-sum-collection cursor)))
   (list-sum-prefix-p
    (list-sum-visited cursor)
    (list-sum-collection cursor))))

(defun list-sum-complete-p (cursor)
  (equal
   (len (list-sum-visited cursor))
   (len (list-sum-collection cursor))))

;; For an integer list XS, this is exactly
;; sum (get_closure XS) 0 (length XS): get_closure selects the indexed entry,
;; and the source integer-range sum visits precisely all list positions.

(defun list-sum-values (xs)
  (if (endp xs)
      0
    (+
     (car xs)
     (list-sum-values (cdr xs)))))

;; Preserve the innermost universal quantifier over every integer X.

(defun-sk list-sum-all-extensions-p (cursor1 cursor2 input-list)
  (forall (x)
    (implies
     (integerp x)
     (implies
      (and
       (equal
        (list-sum-visited cursor2)
        (append
         (list-sum-visited cursor1)
         (list x)))
       (list-sum-permitted-p cursor2))
      (and
       (<=
        0
        (-
         (len input-list)
         (len (list-sum-visited cursor1))))
       (<
        (-
         (len input-list)
         (len (list-sum-visited cursor2)))
        (-
         (len input-list)
         (len (list-sum-visited cursor1))))
       (equal
        (+
         (list-sum-values
          (list-sum-visited cursor1))
         x)
        (list-sum-values
         (list-sum-visited cursor2)))
       (list-sum-permitted-p cursor2))))))

;; CURSOR2 remains universally quantified inside the incomplete-cursor branch,
;; with collection equality outside the universal quantifier over X.

(defun-sk list-sum-all-successors-p (cursor1 input-list)
  (forall (cursor2)
    (implies
     (list-sum-cursor-p cursor2)
     (implies
      (equal
       (list-sum-collection cursor2)
       (list-sum-collection cursor1))
      (list-sum-all-extensions-p
       cursor1 cursor2 input-list)))))

;; This is the exact body of the source's universal quantifier over CURSOR1.

(defun list-sum-cursor1-conclusion-p
    (cursor1 input-list)
  (and
   (list-sum-permitted-p cursor1)
   (if (not (list-sum-complete-p cursor1))
       (and
        (not (list-sum-complete-p cursor1))
        (list-sum-permitted-p cursor1)
        (list-sum-all-successors-p
         cursor1 input-list))
     (equal
      (list-sum-values
       (list-sum-visited cursor1))
      (list-sum-values input-list)))))

(defun-sk list-sum-all-cursors-p (cursor input-list)
  (forall (cursor1)
    (implies
     (list-sum-cursor-p cursor1)
     (implies
      (equal
       (list-sum-collection cursor1)
       (list-sum-collection cursor))
      (implies
       (list-sum-permitted-p cursor1)
       (list-sum-cursor1-conclusion-p
        cursor1 input-list))))))

(defun
  ntp4vc-pearl-cursor-examples-testlistcursor-list-sumqtvc-statement
  (cursor input-list)
  (implies
   (and
    (list-sum-cursor-interface-p)
    (list-sum-cursor-p cursor)
    (list-sum-integer-list-p input-list)
    (list-sum-permitted-p cursor)
    (equal (list-sum-visited cursor) nil)
    (equal
     (list-sum-collection cursor)
     input-list))
   (and
    (equal
     0
     (list-sum-values
      (list-sum-visited cursor)))
    (list-sum-permitted-p cursor)
    (list-sum-all-cursors-p
     cursor input-list))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
