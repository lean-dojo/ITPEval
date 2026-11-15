;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/list_removal_Top_remove2qtvc: the verification condition for removing
;; an entry from two linked-list segments by updating its predecessor's
;; successor. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; location and memory types, distinguished locations, and arbitrary
;; loc -> loc successor function. All typing and distinctness conditions are
;; explicit assumptions of the statement.

(defstub lr2-loc-p (x) t)
(defstub lr2-mem-p (x) t)
(defstub lr2-mem-default () t)
(defstub lr2-null () t)
(defstub lr2-head () t)
(defstub lr2-entry () t)
(defstub lr2-mem1 (location) t)

(defun-sk lr2-mem1-typed-p ()
  (forall (location)
    (implies
     (lr2-loc-p location)
     (lr2-loc-p (lr2-mem1 location)))))

(defun lr2-interface-p ()
  (and
   (lr2-mem-p (lr2-mem-default))
   (lr2-loc-p (lr2-null))
   (lr2-loc-p (lr2-head))
   (lr2-loc-p (lr2-entry))
   (not (equal (lr2-head) (lr2-null)))
   (not (equal (lr2-entry) (lr2-null)))
   (not (equal (lr2-head) (lr2-entry)))
   (lr2-mem1-typed-p)))

;; KIND selects the original successor or its exact single-location
;; functional update.

(defun lr2-next-apply
    (kind update-key update-value location)
  (if (equal kind :updated)
      (if (equal location update-key)
          update-value
        (lr2-mem1 location))
    (lr2-mem1 location)))

;; For a nonnegative integer length this recursion is definitionally
;; equivalent to the source list'def axiom: zero length means equal endpoints,
;; while a positive length requires a non-null start and one fewer link.

(defun lr2-list-nat-p
    (kind update-key update-value start length finish)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      (equal start finish)
    (and
     (not (equal start (lr2-null)))
     (lr2-list-nat-p
      kind
      update-key
      update-value
      (lr2-next-apply
       kind update-key update-value start)
      (- length 1)
      finish))))

(defun lr2-list-p
    (kind update-key update-value start length finish)
  (and
   (integerp length)
   (<= 0 length)
   (lr2-list-nat-p
    kind update-key update-value start length finish)))

(defun lr2-original-list-p (start length finish)
  (lr2-list-p
   :original
   (lr2-null)
   (lr2-null)
   start
   length
   finish))

(defun lr2-updated-list-p
    (update-key update-value start length finish)
  (lr2-list-p
   :updated
   update-key
   update-value
   start
   length
   finish))

(defun lr2-loop-antecedent-p (n1 n2 n ind)
  (and
   (and
    (< 0 n)
    (<= n n1))
   (not (equal ind (lr2-null)))
   (lr2-original-list-p
    (lr2-head) (- n 1) ind)
   (lr2-original-list-p
    (lr2-mem1 ind) (- n1 n) (lr2-entry))
   (lr2-original-list-p
    (lr2-entry) n2 (lr2-null))))

(defun lr2-advance-branch-p (n1 n2 n ind)
  (and
   (not (equal ind (lr2-null)))
   (and
    (<= 0 (- n1 n))
    (< (- n1 (+ n 1))
       (- n1 n)))
   (and
    (< 0 (+ n 1))
    (<= (+ n 1) n1))
   (not (equal (lr2-mem1 ind) (lr2-null)))
   (lr2-original-list-p
    (lr2-head)
    (- (+ n 1) 1)
    (lr2-mem1 ind))
   (lr2-original-list-p
    (lr2-mem1 (lr2-mem1 ind))
    (- n1 (+ n 1))
    (lr2-entry))
   (lr2-original-list-p
    (lr2-entry) n2 (lr2-null))))

(defun lr2-remove-branch-p (n1 n2 ind)
  (let ((o1 (lr2-entry)))
    (and
     (not (equal o1 (lr2-null)))
     (not (equal ind (lr2-null)))
     (lr2-updated-list-p
      ind
      (lr2-mem1 o1)
      (lr2-head)
      (- (+ n1 n2) 1)
      (lr2-null)))))

(defun lr2-loop-conclusion-p (n1 n2 n ind)
  (and
   (not (equal ind (lr2-null)))
   (if (not (equal (lr2-mem1 ind)
                   (lr2-entry)))
       (lr2-advance-branch-p n1 n2 n ind)
     (lr2-remove-branch-p n1 n2 ind))))

(defun lr2-loop-case-p (n1 n2 n ind)
  (implies
   (lr2-loop-antecedent-p n1 n2 n ind)
   (lr2-loop-conclusion-p n1 n2 n ind)))

;; The loop index and predecessor location retain their internal universal
;; quantifier scope from the source conclusion.

(defun-sk lr2-all-loop-cases-p (n1 n2)
  (forall (n ind)
    (implies
     (and
      (integerp n)
      (lr2-loc-p ind))
     (lr2-loop-case-p n1 n2 n ind))))

(defun lr2-remove2-conclusion-p (n1 n2)
  (and
   (< 0 1)
   (<= 1 n1)
   (not (equal (lr2-head) (lr2-null)))
   (lr2-original-list-p
    (lr2-head) (- 1 1) (lr2-head))
   (lr2-original-list-p
    (lr2-mem1 (lr2-head))
    (- n1 1)
    (lr2-entry))
   (lr2-original-list-p
    (lr2-entry) n2 (lr2-null))
   (lr2-all-loop-cases-p n1 n2)))

(defun
    ntp4vc-pearl-list-removal-top-remove2qtvc-statement
    (n1 n2)
  (implies
   (and
    (lr2-interface-p)
    (integerp n1)
    (integerp n2)
    (< 0 n1)
    (< 0 n2)
    (lr2-original-list-p
     (lr2-head) n1 (lr2-entry))
    (lr2-original-list-p
     (lr2-entry) n2 (lr2-null)))
   (lr2-remove2-conclusion-p n1 n2)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
