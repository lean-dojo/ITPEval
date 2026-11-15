;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linked_list_rev_InPlaceRev_in_place_reverseqtvc: the linked-list
;; in-place reversal verification condition for list segments, disjointness,
;; and preservation of the reversed list. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source location type is arbitrary and inhabited by NULL.  NEXT and
;; NEXT1 are conservative interfaces for the two arbitrary loc -> loc
;; functions in the verification condition; their typing laws remain explicit
;; assumptions of the statement.

(defstub llri-loc-p (x) t)
(defstub llri-null () t)
(defstub llri-next (x) t)
(defstub llri-next1 (x) t)

(defun-sk llri-next-typed-p ()
  (forall (x)
    (implies
     (llri-loc-p x)
     (llri-loc-p (llri-next x)))))

(defun-sk llri-next1-typed-p ()
  (forall (x)
    (implies
     (llri-loc-p x)
     (llri-loc-p (llri-next1 x)))))

(defun llri-interface-p ()
  (and
   (llri-loc-p (llri-null))
   (llri-next-typed-p)
   (llri-next1-typed-p)))

(defun llri-loc-list-p (xs)
  (if (consp xs)
      (and
       (llri-loc-p (car xs))
       (llri-loc-list-p (cdr xs)))
    (equal xs nil)))

;; EQ_LOC is uniquely characterized by the source specification
;; eq_loc x y = true iff x = y, so ACL2 equality is definitionally
;; equivalent to the source Boolean operation.

(defun llri-eq-loc (left right)
  (equal left right))

(defun llri-disjoint-p (left right)
  (if (consp left)
      (and
       (not (member-equal (car left) right))
       (llri-disjoint-p (cdr left) right))
    (equal left nil)))

(defun llri-no-repet-p (xs)
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (llri-no-repet-p (cdr xs)))
    (equal xs nil)))

;; KIND selects the outer NEXT, the continuation NEXT1, or the exact
;; functional update next1(update-key := update-value).

(defun llri-next-apply
    (kind update-key update-value location)
  (cond
   ((equal kind :next)
    (llri-next location))
   ((equal kind :next1)
    (llri-next1 location))
   ((equal kind :updated-next1)
    (if (equal location update-key)
        update-value
      (llri-next1 location)))
   (t
    (llri-null))))

;; This recursion is definitionally equivalent to the source inductive
;; LIST_SEG constructors: NIL ends at its starting location, while CONS
;; records a non-null head and follows the selected successor.

(defun llri-list-seg-p
    (kind update-key update-value p xs q)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (equal (car xs) p)
       (not (equal p (llri-null)))
       (llri-list-seg-p
        kind
        update-key
        update-value
        (llri-next-apply
         kind update-key update-value p)
        (cdr xs)
        q))
    (and
     (equal xs nil)
     (equal p q))))

(defun llri-list-seg-next-p (p xs q)
  (llri-list-seg-p
   :next
   (llri-null)
   (llri-null)
   p xs q))

(defun llri-list-seg-next1-p (p xs q)
  (llri-list-seg-p
   :next1
   (llri-null)
   (llri-null)
   p xs q))

(defun llri-list-seg-updated-next1-p
    (update-key update-value p xs q)
  (llri-list-seg-p
   :updated-next1
   update-key
   update-value
   p xs q))

;; The nested source matches are retained explicitly.  In the CONS case the
;; inner match states that its tail is the outer match's tail.

(defun llri-nonnull-continuation-p
    (lM rM pM p r)
  (and
   (not (equal p (llri-null)))
   (if (consp pM)
       (let ((head (car pM))
             (tail (cdr pM)))
         (and
          (equal (cdr pM) tail)
          (llri-list-seg-updated-next1-p
           p
           r
           (llri-next1 p)
           tail
           (llri-null))
          (llri-list-seg-updated-next1-p
           p
           r
           p
           (cons head rM)
           (llri-null))
          (llri-disjoint-p
           tail
           (cons head rM))
          (equal
           (append
            (reverse tail)
            (cons head rM))
           (reverse lM))))
     nil)))

(defun llri-continuation-case-p
    (lM rM r pM p)
  (implies
   (and
    (llri-list-seg-next1-p
     p pM (llri-null))
    (llri-list-seg-next1-p
     r rM (llri-null))
    (llri-disjoint-p pM rM)
    (equal
     (append (reverse pM) rM)
     (reverse lM)))
   (let* ((o1 (llri-null))
          (o2 (llri-eq-loc p o1)))
     (implies
      (equal
       (equal o2 t)
       (equal p o1))
      (if (not (equal o2 t))
          (llri-nonnull-continuation-p
           lM rM pM p r)
        (llri-list-seg-next1-p
         r
         (reverse lM)
         (llri-null)))))))

;; The source quantifies these four list/location variables internally.
;; NEXT1 is an arbitrary conservative function interface, as permitted for a
;; theorem generic over an operation symbol.

(defun-sk llri-all-continuations-p (lM)
  (forall (rM r pM p)
    (implies
     (and
      (llri-loc-list-p rM)
      (llri-loc-p r)
      (llri-loc-list-p pM)
      (llri-loc-p p))
     (llri-continuation-case-p
      lM rM r pM p))))

(defun
    ntp4vc-pearl-linked-list-rev-inplacerev-in-place-reverseqtvc-statement
    (l lM)
  (implies
   (and
    (llri-interface-p)
    (llri-loc-p l)
    (llri-loc-list-p lM)
    (llri-list-seg-next-p
     l lM (llri-null)))
   (and
    (llri-list-seg-next-p
     l lM (llri-null))
    (llri-list-seg-next-p
     (llri-null)
     nil
     (llri-null))
    (llri-disjoint-p lM nil)
    (equal
     (append (reverse lM) nil)
     (reverse lM))
    (llri-all-continuations-p lM))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
