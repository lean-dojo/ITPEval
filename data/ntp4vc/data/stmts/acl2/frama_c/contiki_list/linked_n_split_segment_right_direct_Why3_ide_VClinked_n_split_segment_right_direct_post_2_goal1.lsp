;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_right_direct_Why3_ide_VClinked_n_split_segment_right_direct_post_2_goal1:
;; direct extraction of the rightmost one-node suffix of an inductively
;; defined linked-list segment. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssrdg1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssrdg1-address-base (address)
  (car address))

(defun lnssrdg1-address-offset (address)
  (cdr address))

(defun lnssrdg1-shift (address amount)
  (cons
   (lnssrdg1-address-base address)
   (+ (lnssrdg1-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssrdg1-t1 (address) t)
(defstub lnssrdg1-t (index) t)
(defstub lnssrdg1-region (base) t)
(defstub lnssrdg1-linked-op () t)

(defun-sk lnssrdg1-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssrdg1-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssrdg1-address-p (lnssrdg1-t1 address))
      (integerp (lnssrdg1-t index))
      (integerp (lnssrdg1-region base))))))

(defun lnssrdg1-linked-p ()
  (if (lnssrdg1-linked-op) t nil))

(defun lnssrdg1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssrdg1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssrdg1-address-base address))
    (<= 0 (lnssrdg1-address-offset address))
    (<=
     (+ (lnssrdg1-address-offset address) length)
     (lnssrdg1-t (lnssrdg1-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssrdg1-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssrdg1-address-p root)
   (lnssrdg1-address-p array)
   (integerp index)
   (integerp n)
   (lnssrdg1-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssrdg1-t1 (lnssrdg1-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssrdg1-valid-rw-p root 4)
      (lnssrdg1-p-linked-n-p
       (lnssrdg1-t1 (lnssrdg1-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssrdg1-framed-p ()
  (forall (address)
    (implies
     (lnssrdg1-address-p address)
     (<=
      (lnssrdg1-region
       (lnssrdg1-address-base (lnssrdg1-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-right-direct-post-2-goal1-statement ()
  (forall
   (a2 i i1 a a1)
   (implies
    (and
     (lnssrdg1-function-types-p)
     (lnssrdg1-address-p a2)
     (integerp i)
     (integerp i1)
     (lnssrdg1-address-p a)
     (lnssrdg1-address-p a1))
    (let
        ((a3
          (lnssrdg1-t1
           (lnssrdg1-shift
            (lnssrdg1-t1
             (lnssrdg1-shift a2 (- (+ i i1) 1)))
            0))))
      (implies
       (and
        (< 0 i)
        (<= (lnssrdg1-region (lnssrdg1-address-base a)) 0)
        (<= (lnssrdg1-region (lnssrdg1-address-base a1)) 0)
        (<= (lnssrdg1-region (lnssrdg1-address-base a2)) 0)
        (<= (lnssrdg1-region (lnssrdg1-address-base a3)) 0)
        (lnssrdg1-framed-p)
        (lnssrdg1-linked-p)
        (lnssrdg1-is-sint32-p i)
        (lnssrdg1-is-sint32-p i1)
        (lnssrdg1-valid-rw-p
         (lnssrdg1-shift a2 0)
         2147483646)
        (lnssrdg1-p-linked-n-p
         a a2 i1 (+ 1 i) a1))
       (lnssrdg1-p-linked-n-p
        a3 a2 (+ i i1) 1 a1))))))

(value-triple :itpeval-statement-checked)

:q
