;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linked_list_rev_InPlaceRevSeq_in_place_reverseqtvc: the linked-list
;; in-place reversal verification condition for list segments, disjointness,
;; and preservation of the reversed sequence. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Locations form an arbitrary inhabited source carrier.  The successor
;; functions are conservative generic interfaces for the two universally
;; arbitrary loc -> loc functions in the verification condition.  Their
;; source typing laws are explicit in the statement predicate.

(defstub ipr-loc-p (x) t)
(defstub ipr-null () t)
(defstub ipr-default-loc () t)
(defstub ipr-next1 (x) t)
(defstub ipr-next2 (x) t)

(defun-sk ipr-loc-domain-nonempty-p ()
  (exists (x)
    (ipr-loc-p x)))

(defun-sk ipr-next1-typed-p ()
  (forall (x)
    (implies
     (ipr-loc-p x)
     (ipr-loc-p (ipr-next1 x)))))

(defun-sk ipr-next2-typed-p ()
  (forall (x)
    (implies
     (ipr-loc-p x)
     (ipr-loc-p (ipr-next2 x)))))

(defun ipr-interface-p ()
  (and
   (ipr-loc-domain-nonempty-p)
   (ipr-loc-p (ipr-null))
   (ipr-loc-p (ipr-default-loc))
   (ipr-next1-typed-p)
   (ipr-next2-typed-p)))

(defun ipr-loc-list-p (xs)
  (if (consp xs)
      (and
       (ipr-loc-p (car xs))
       (ipr-loc-list-p (cdr xs)))
    (equal xs nil)))

;; This is the source conversion Int.toNat, followed by the source's total
;; list indexing with its fixed inhabited default.

(defun ipr-int-to-nat (value)
  (if (and (integerp value)
           (< value 0))
      0
    (nfix value)))

(defun ipr-nth-loc (xs index)
  (let ((tail
         (nthcdr
          (ipr-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      (ipr-default-loc))))

;; The source boolean equality is completely characterized by eq_loc'spec,
;; so ACL2 equality is a definitionally equivalent implementation.

(defun ipr-eq-loc (left right)
  (equal left right))

;; A finite list is disjoint from another exactly when no element occurring
;; at any position of the first occurs at a position of the second.

(defun ipr-disjoint-p (left right)
  (if (consp left)
      (and
       (not (member-equal (car left) right))
       (ipr-disjoint-p (cdr left) right))
    (equal left nil)))

;; Dispatch distinguishes the outer successor, the continuation successor,
;; and the exact single-location update next2(p := r).

(defun ipr-next-apply
    (kind update-key update-value location)
  (cond
   ((equal kind :next1)
    (ipr-next1 location))
   ((equal kind :next2)
    (ipr-next2 location))
   ((equal kind :updated-next2)
    (if (equal location update-key)
        update-value
      (ipr-next2 location)))
   (t
    (ipr-default-loc))))

(defun-sk ipr-list-elements-nonnull-p (xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len xs)))
      (not
       (equal
        (ipr-nth-loc xs index)
        (ipr-null)))))))

(defun-sk ipr-list-links-p
    (kind update-key update-value xs)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (- (len xs) 1)))
      (equal
       (ipr-next-apply
        kind
        update-key
        update-value
        (ipr-nth-loc xs index))
       (ipr-nth-loc xs (+ index 1)))))))

;; This is list_seg verbatim after replacing the source integer length by the
;; equal ACL2 natural length of a proper list.

(defun ipr-list-seg-p
    (kind update-key update-value p xs q)
  (and
   (ipr-list-elements-nonnull-p xs)
   (or
    (and
     (equal p q)
     (equal (len xs) 0))
    (and
     (<= 1 (len xs))
     (equal
      (ipr-nth-loc xs 0)
      p)
     (equal
      (ipr-next-apply
       kind
       update-key
       update-value
       (ipr-nth-loc xs (- (len xs) 1)))
      q)
     (ipr-list-links-p
      kind
      update-key
      update-value
      xs)))))

(defun ipr-list-seg-next1-p (p xs q)
  (ipr-list-seg-p
   :next1
   (ipr-null)
   (ipr-null)
   p xs q))

(defun ipr-list-seg-next2-p (p xs q)
  (ipr-list-seg-p
   :next2
   (ipr-null)
   (ipr-null)
   p xs q))

(defun ipr-list-seg-updated-next2-p
    (update-key update-value p xs q)
  (ipr-list-seg-p
   :updated-next2
   update-key
   update-value
   p xs q))

;; The following universal predicate is the source pointwise description of
;; o4 = Cons o3 rM at all positive indices.

(defun-sk ipr-cons-shift-p (o4 rM)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (< 0 index)
       (<= index (len rM)))
      (equal
       (ipr-nth-loc o4 index)
       (ipr-nth-loc rM (- index 1)))))))

(defun ipr-updated-state-conclusion-p
    (lM rM pM p r)
  (let* ((o3 (ipr-nth-loc pM 0))
         (o4 (cons o3 rM)))
    (implies
     (and
      (equal
       (len o4)
       (+ 1 (len rM)))
      (equal
       (ipr-nth-loc o4 0)
       o3)
      (ipr-cons-shift-p o4 rM))
     (and
      (and
       (<= 0 1)
       (<= 1 (len pM)))
      (and
       (<= 0 (len pM))
       (< (len (cdr pM))
          (len pM)))
      (ipr-list-seg-updated-next2-p
       p
       r
       (ipr-next2 p)
       (cdr pM)
       (ipr-null))
      (ipr-list-seg-updated-next2-p
       p
       r
       p
       o4
       (ipr-null))
      (ipr-disjoint-p
       (cdr pM)
       o4)
      (equal
       (append
        (reverse (cdr pM))
        o4)
       (reverse lM))))))

;; This preserves the complete body of the source continuation implication,
;; including its repeated non-null conjunct and the explicit equality-test
;; specification antecedent.

(defun ipr-continuation-case-p
    (lM rM r pM p)
  (implies
   (and
    (ipr-list-seg-next2-p
     p pM (ipr-null))
    (ipr-list-seg-next2-p
     r rM (ipr-null))
    (ipr-disjoint-p pM rM)
    (equal
     (append
      (reverse pM)
      rM)
     (reverse lM)))
   (let* ((o1 (ipr-null))
          (o2 (ipr-eq-loc p o1)))
     (implies
      (equal
       (equal o2 t)
       (equal p o1))
      (if (not (equal o2 t))
          (and
           (not (equal p (ipr-null)))
           (not (equal p (ipr-null)))
           (ipr-updated-state-conclusion-p
            lM rM pM p r))
        (ipr-list-seg-next2-p
         r
         (reverse lM)
         (ipr-null)))))))

;; rM, r, pM, and p remain universally quantified inside the conclusion.
;; The generic next2 interface above is ACL2's conservative representation of
;; the source universal function parameter.

(defun-sk ipr-all-continuations-p (lM)
  (forall (rM r pM p)
    (implies
     (and
      (ipr-loc-list-p rM)
      (ipr-loc-p r)
      (ipr-loc-list-p pM)
      (ipr-loc-p p))
     (ipr-continuation-case-p
      lM rM r pM p))))

(defun
  ntp4vc-pearl-linked-list-rev-inplacerevseq-in-place-reverseqtvc-statement
  (l lM)
  (implies
   (and
    (ipr-interface-p)
    (ipr-loc-p l)
    (ipr-loc-list-p lM)
    (ipr-list-seg-next1-p
     l lM (ipr-null)))
   (and
    (ipr-list-seg-next1-p
     l lM (ipr-null))
    (ipr-list-seg-next1-p
     (ipr-null)
     nil
     (ipr-null))
    (ipr-disjoint-p lM nil)
    (equal
     (append (reverse lM) nil)
     (reverse lM))
    (ipr-all-continuations-p lM))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
