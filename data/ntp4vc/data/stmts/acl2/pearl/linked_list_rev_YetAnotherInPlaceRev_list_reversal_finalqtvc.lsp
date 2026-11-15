;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc: the
;; final linked-list reversal verification condition, relating forward and
;; reversed cell enumerations under a framed memory update. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source location type is an arbitrary inhabited carrier.  These
;; conservative interfaces represent its distinguished null value, the
;; arbitrary integer-indexed cell enumeration, and the two arbitrary
;; loc -> loc successor functions quantified by the source statement.

(defstub yair-loc-p (x) t)
(defstub yair-null () t)
(defstub yair-s (i) t)
(defstub yair-mem1 (location) t)
(defstub yair-mem3 (location) t)

(defun-sk yair-s-typed-p ()
  (forall (i)
    (implies
     (integerp i)
     (yair-loc-p (yair-s i)))))

(defun-sk yair-mem1-typed-p ()
  (forall (location)
    (implies
     (yair-loc-p location)
     (yair-loc-p (yair-mem1 location)))))

(defun-sk yair-mem3-typed-p ()
  (forall (location)
    (implies
     (yair-loc-p location)
     (yair-loc-p (yair-mem3 location)))))

(defun yair-interface-p ()
  (and
   (yair-loc-p (yair-null))
   (yair-s-typed-p)
   (yair-mem1-typed-p)
   (yair-mem3-typed-p)))

;; The memory tag is only a first-order dispatcher for the two source
;; successor functions; it does not restrict their arbitrary behavior.

(defun yair-next (memory location)
  (if (equal memory :mem3)
      (yair-mem3 location)
    (yair-mem1 location)))

;; :FORWARD denotes s(i), while :REVERSED denotes the source function
;; fc(s,n)(i) = s(n - 1 - i).

(defun yair-sequence-at
    (sequence-kind reversal-length index)
  (if (equal sequence-kind :reversed)
      (yair-s (- (- reversal-length 1) index))
    (yair-s index)))

;; This finite recursion is definitionally equivalent to the source is_list
;; equations together with result(s)(i) = s(i+1).  OFFSET records the repeated
;; applications of result.

(defun yair-is-list-aux-p
    (memory sequence-kind reversal-length location offset count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (equal location (yair-null))
    (let ((head
           (yair-sequence-at
            sequence-kind reversal-length offset)))
      (and
       (equal location head)
       (not (equal head (yair-null)))
       (yair-is-list-aux-p
        memory
        sequence-kind
        reversal-length
        (yair-next memory location)
        (+ offset 1)
        (- count 1))))))

(defun yair-is-list-p
    (memory location sequence-kind reversal-length count)
  (yair-is-list-aux-p
   memory sequence-kind reversal-length location 0 count))

;; The two components of valid_cells preserve the source quantifiers over all
;; mathematical integers in the half-open interval [0,n).

(defun-sk yair-valid-cells-nonnull-p (n)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i n))
      (not
       (equal (yair-s i) (yair-null)))))))

(defun-sk yair-valid-cells-distinct-p (n)
  (forall (i j)
    (implies
     (and
      (integerp i)
      (integerp j))
     (implies
      (and
       (<= 0 i)
       (< i n)
       (<= 0 j)
       (< j n)
       (not (equal i j)))
      (not
       (equal (yair-s i) (yair-s j)))))))

(defun yair-valid-cells-p (n)
  (and
   (yair-valid-cells-nonnull-p n)
   (yair-valid-cells-distinct-p n)))

(defun-sk yair-list-lr-links-p (memory lo hi)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= lo k)
       (< k (- hi 1)))
      (equal
       (yair-next memory (yair-s k))
       (yair-s (+ k 1)))))))

(defun yair-list-lr-p (memory location lo hi)
  (and
   (<= 0 lo)
   (<= lo hi)
   (if (equal lo hi)
       (equal location (yair-null))
     (and
      (equal location (yair-s lo))
      (equal
       (yair-next memory (yair-s (- hi 1)))
       (yair-null))
      (yair-list-lr-links-p memory lo hi)))))

(defun-sk yair-list-rl-links-p (memory lo hi)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (< lo k)
       (< k hi))
      (equal
       (yair-next memory (yair-s k))
       (yair-s (- k 1)))))))

(defun yair-list-rl-p (memory location lo hi)
  (and
   (<= 0 lo)
   (<= lo hi)
   (if (equal lo hi)
       (equal location (yair-null))
     (and
      (equal
       (yair-next memory (yair-s lo))
       (yair-null))
      (equal location (yair-s (- hi 1)))
      (yair-list-rl-links-p memory lo hi)))))

;; A location is outside the enumerated cells exactly when it differs from
;; s(i) for every integer i in [0,n).

(defun-sk yair-outside-cells-p (location n)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i n))
      (not
       (equal location (yair-s i)))))))

(defun-sk yair-frame-p (new-memory old-memory n)
  (forall (location)
    (implies
     (yair-loc-p location)
     (implies
      (yair-outside-cells-p location n)
      (equal
       (yair-next new-memory location)
       (yair-next old-memory location))))))

(defun yair-result-location-post-p (n location)
  (implies
   (and
    (yair-list-rl-p :mem3 location 0 n)
    (yair-frame-p :mem3 :mem1 n))
   (and
    (yair-is-list-p
     :mem3 location :reversed n n)
    (yair-frame-p :mem3 :mem1 n))))

;; LOCATION remains universally quantified in the conclusion.  The generic
;; MEM3 interface above is ACL2's conservative representation of the source
;; universal function parameter.

(defun-sk yair-all-result-locations-p (n)
  (forall (location)
    (implies
     (yair-loc-p location)
     (yair-result-location-post-p n location))))

;; N and LOCATION are the source's universally quantified value parameters.
;; The generic S, MEM1, and MEM3 interfaces preserve the arbitrary function
;; parameters without replacing them by finite tables.

(defun-sk
  ntp4vc-pearl-linked-list-rev-yetanotherinplacerev-list-reversal-finalqtvc-statement
  ()
  (forall (n location)
    (implies
     (and
      (integerp n)
      (yair-loc-p location))
     (implies
      (and
       (yair-interface-p)
       (<= 0 n)
       (yair-is-list-p
        :mem1 location :forward 0 n))
      (and
       (yair-valid-cells-p n)
       (yair-list-lr-p :mem1 location 0 n)
       (yair-all-result-locations-p n))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
