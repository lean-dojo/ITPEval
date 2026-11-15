;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/list_removal_Top_remove1qtvc: the verification condition for removing
;; one entry from linked list segments by a single successor update. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; location and memory types, its distinguished locations, and the arbitrary
;; loc -> loc successor function. The type and distinctness conditions remain
;; explicit assumptions of the statement.

(defstub lr-loc-p (x) t)
(defstub lr-mem-p (x) t)
(defstub lr-mem-default () t)
(defstub lr-null () t)
(defstub lr-head () t)
(defstub lr-entry () t)
(defstub lr-mem1 (location) t)

(defun-sk lr-mem1-typed-p ()
  (forall (location)
    (implies
     (lr-loc-p location)
     (lr-loc-p (lr-mem1 location)))))

(defun lr-interface-p ()
  (and
   (lr-mem-p (lr-mem-default))
   (lr-loc-p (lr-null))
   (lr-loc-p (lr-head))
   (lr-loc-p (lr-entry))
   (not (equal (lr-head) (lr-null)))
   (not (equal (lr-entry) (lr-null)))
   (not (equal (lr-head) (lr-entry)))
   (lr-mem1-typed-p)))

;; KIND selects the original successor or its exact single-location
;; functional update.

(defun lr-next-apply
    (kind update-key update-value location)
  (if (equal kind :updated)
      (if (equal location update-key)
          update-value
        (lr-mem1 location))
    (lr-mem1 location)))

;; For a nonnegative integer length this recursion is definitionally
;; equivalent to the source list'def axiom: length zero means equal endpoints,
;; and a positive length requires a non-null start followed by one fewer link.

(defun lr-list-nat-p
    (kind update-key update-value start length finish)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      (equal start finish)
    (and
     (not (equal start (lr-null)))
     (lr-list-nat-p
      kind
      update-key
      update-value
      (lr-next-apply
       kind update-key update-value start)
      (- length 1)
      finish))))

(defun lr-list-p
    (kind update-key update-value start length finish)
  (and
   (integerp length)
   (<= 0 length)
   (lr-list-nat-p
    kind update-key update-value start length finish)))

(defun lr-original-list-p (start length finish)
  (lr-list-p
   :original
   (lr-null)
   (lr-null)
   start
   length
   finish))

(defun lr-updated-list-p
    (update-key update-value start length finish)
  (lr-list-p
   :updated
   update-key
   update-value
   start
   length
   finish))

(defun lr-loop-antecedent-p (n1 n2 n curr prev)
  (and
   (and (< 0 n)
        (<= n n1))
   (lr-original-list-p
    (lr-head) n curr)
   (not (equal curr (lr-null)))
   (implies
    (equal prev (lr-null))
    (equal n 1))
   (implies
    (not (equal prev (lr-null)))
    (equal (lr-mem1 prev) curr))
   (implies
    (not (equal prev (lr-null)))
    (lr-original-list-p
     (lr-head) (- n 1) prev))
   (lr-original-list-p
    curr (- n1 n) (lr-entry))
   (lr-original-list-p
    (lr-entry) n2 (lr-null))))

(defun lr-advance-branch-p (n1 n2 n curr)
  (and
   (not (equal curr (lr-null)))
   (and
    (<= 0 (- n1 n))
    (< (- n1 (+ n 1))
       (- n1 n)))
   (and
    (< 0 (+ n 1))
    (<= (+ n 1) n1))
   (lr-original-list-p
    (lr-head)
    (+ n 1)
    (lr-mem1 curr))
   (not (equal (lr-mem1 curr) (lr-null)))
   (implies
    (equal curr (lr-null))
    (equal (+ n 1) 1))
   (implies
    (not (equal curr (lr-null)))
    t)
   (implies
    (not (equal curr (lr-null)))
    (lr-original-list-p
     (lr-head)
     (- (+ n 1) 1)
     curr))
   (lr-original-list-p
    (lr-mem1 curr)
    (- n1 (+ n 1))
    (lr-entry))
   (lr-original-list-p
    (lr-entry) n2 (lr-null))))

(defun lr-remove-head-branch-p (n1 n2 curr)
  (and
   (not (equal curr (lr-null)))
   (let ((o3 (lr-head)))
     (and
      (not (equal o3 (lr-null)))
      (lr-updated-list-p
       o3
       (lr-mem1 curr)
       (lr-head)
       (- (+ n1 n2) 1)
       (lr-null))))))

(defun lr-remove-after-prev-branch-p
    (n1 n2 curr prev)
  (and
   (not (equal curr (lr-null)))
   (not (equal prev (lr-null)))
   (lr-updated-list-p
    prev
    (lr-mem1 curr)
    (lr-head)
    (- (+ n1 n2) 1)
    (lr-null))))

(defun lr-loop-conclusion-p (n1 n2 n curr prev)
  (if (not (equal curr (lr-entry)))
      (lr-advance-branch-p n1 n2 n curr)
    (if (equal prev (lr-null))
        (lr-remove-head-branch-p n1 n2 curr)
      (lr-remove-after-prev-branch-p
       n1 n2 curr prev))))

(defun lr-loop-case-p (n1 n2 n curr prev)
  (implies
   (lr-loop-antecedent-p n1 n2 n curr prev)
   (lr-loop-conclusion-p n1 n2 n curr prev)))

;; The loop index and the current and previous locations retain their internal
;; universal quantifier scope from the source conclusion.

(defun-sk lr-all-loop-cases-p (n1 n2)
  (forall (n curr prev)
    (implies
     (and
      (integerp n)
      (lr-loc-p curr)
      (lr-loc-p prev))
     (lr-loop-case-p n1 n2 n curr prev))))

(defun lr-remove1-conclusion-p (n1 n2)
  (let* ((o1 (lr-head))
         (o2 (lr-mem1 o1)))
    (and
     (not (equal o1 (lr-null)))
     (and
      (and
       (and (< 0 1)
            (<= 1 n1))
       (lr-original-list-p
        (lr-head) 1 o2)
       (not (equal o2 (lr-null)))
       (lr-original-list-p
        o2 (- n1 1) (lr-entry))
       (lr-original-list-p
        (lr-entry) n2 (lr-null)))
      (lr-all-loop-cases-p n1 n2)))))

(defun
    ntp4vc-pearl-list-removal-top-remove1qtvc-statement
    (n1 n2)
  (implies
   (and
    (lr-interface-p)
    (integerp n1)
    (integerp n2)
    (< 0 n1)
    (< 0 n2)
    (lr-original-list-p
     (lr-head) n1 (lr-entry))
    (lr-original-list-p
     (lr-entry) n2 (lr-null)))
   (lr-remove1-conclusion-p n1 n2)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
